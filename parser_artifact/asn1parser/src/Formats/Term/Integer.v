Require Import
  BinInt
  Lia
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.NonNeg.

Lemma int_le_1 (lb ub : Z) : forall a : Z,
  (lb <= a <= ub)%Z ->
  Z.to_nat (a - lb) <= Z.to_nat (ub - lb) /\
  (Z.of_nat (Z.to_nat (a - lb)) + lb)%Z = a. 
Proof.
  intros. lia. 
(*  - apply Z2Nat.inj_le; try lia.
  - rewrite Z2Nat.id; try lia.  *)
Qed.

Lemma int_le_2 (lb ub : Z) (pf : (lb <= ub)%Z) : forall a' : nat,
   a' <= Z.to_nat (ub - lb) ->
   (lb <= Z.of_nat a' + lb <= ub)%Z /\ Z.to_nat (Z.of_nat a' + lb - lb) = a'.
Proof.
  intros. lia.
Qed.

Definition z_range_dec (lb ub : Z)
  : (forall a : Z, {(lb <= a <= ub)%Z} + {~ (lb <= a <= ub)%Z}).
  intro. 
  apply sumbool_and1; 
  apply ZArith_dec.Z_le_dec. 
Defined.
  
Definition ranged_int_format (lb ub : Z) (pf : (lb <= ub)%Z)
    (pf2 : to_bit_sz (Z.to_nat (ub - lb)%Z) <= INT_MAX_LEN ) :
  T_Format Z (fun z => (lb <= z <= ub)%Z) :=
  proj_format
    (fun z => (lb <= z <= ub)%Z)
    (nat_format (Z.to_nat (ub - lb)) pf2 )
    (fun z : Z => Z.to_nat (z - lb)%Z )
    (fun n : nat => ((Z.of_nat n) + lb)%Z )
    (int_le_1 lb ub)
    (int_le_2 lb ub pf)
    (z_range_dec lb ub).

Lemma fix_int_helper1 (n : Z) : (forall a : Z,
        (fun z : Z => z = n) a ->
        (fun _ : unit => True) ((fun _ : Z => tt) a) /\
          (fun _ : unit => n) ((fun _ : Z => tt) a) = a).
Proof.
  intros. simpl in H. subst. split; auto .
Qed.

Lemma fix_int_helper2 (n : Z) :  (forall a' : unit,
        (fun _ : unit => True) a' ->
        (fun z : Z => z = n) ((fun _ : unit => n) a') /\
          (fun _ : Z => tt) ((fun _ : unit => n) a') = a').
Proof.
  intros. simpl in *. destruct a'. split; auto.
Qed.

Require Import ASN1Parser.Formats.Term.Unit.

Definition fixed_int_format (n : Z) : T_Format Z (fun z : Z => z = n) :=
  proj_format
    (fun z => z = n)
    unit_format
    (fun _ => tt)
    (fun _ => n)
    (fix_int_helper1 n)
    (fix_int_helper2 n)
    (fun z => Z.eq_dec z n).


(* This is unconstrained whole number. Even though theoretically,
   we could encode an infinitely large number. However, here, we
   limit the integer to some value -2^47  <= z <= 2^47 - 1. As we
   we just want to use one BasicBits operations. 

   First a length determinant is added, then, it is encoded into
   the minimum number of octet it needs. 
 *)

Require Import ASN1Parser.Formats.Term.LengthDet
               ASN1Parser.tact.

(*Eval compute in to_bit_sz (128 - 1).  *)

(* -2^(k-1) <= n *)
Definition sz_to_num_octets (sz : nat) := 
  Nat.div sz 8 + 1. 

(*Eval compute in sz_to_num_octets 8.  *)


(*Eval compute in nat_flip 4 13.  *)

(* Find the binary number for -n. We compute it by
   flipping the bits and then plus 1
 *)
Definition to_2_complement (sz : nat) (n : nat) :=
  (PeanoNat.Nat.lnot n sz) + 1. 

(*Eval compute in to_2_complement 4 8.*)
Definition nat_T := {n | 1 <= n <= 6}.

Definition compare_lt_le_dec lb ub x : {lb <= x <= ub} + {~(lb <= x <= ub)} :=
  sumbool_and1 (Compare_dec.le_dec lb x) (Compare_dec.le_dec x ub). 

Lemma one_le_6 : 1 <= 1 <= 6. lia. Qed.
Lemma two_le_6 : 1 <= 2 <= 6. lia. Qed.
(* The actual size of z should be
   -2^47 <= z <= 2^47 - 1
 *)
Definition z_to_nat_bin (z : Z) : nat_T * nat :=
  (* If z is smaller than 0, then, we find its 2-compliment
     in Nat. First we need to determine how many bits
     it takes. Then compute it as nat
   *)
  if (Z.ltb z 0) then
    let n := (Z.to_nat (-z)) in
    let sz := to_bit_sz (n - 1) in
    let num_octets := sz_to_num_octets sz in
    match compare_lt_le_dec 1 6 num_octets with
    | left pf_n => (exist _ num_octets pf_n, to_2_complement (num_octets * 8) n)
    | right _ => (exist _ 1 one_le_6, 0)
    end
  else
    let n := (Z.to_nat z) in 
    let sz := to_bit_sz n in
    let num_octets := sz_to_num_octets sz in
    match compare_lt_le_dec 1 6 num_octets with
    | left pf_n => (exist _ num_octets pf_n, n)
    | right _ => (exist _ 1 one_le_6, 0)
    end.

(* Invsese of previous function *)
(* n should have a upper bound after we read it, but it should
   also have a lower bound. 
 *)
Definition nat_bin_to_z (z : nat_T * nat) : Z :=
  let (num_octets, n) := z in 
  let sz := proj1_sig num_octets * 8 in
  if (Nat.ltb n (Nat.pow 2 (sz - 1)))
  then Z.of_nat n
  else Z.opp (Z.of_nat (to_2_complement sz n)).

(*Eval compute in z_to_nat_bin (-10).
Eval compute in nat_bin_to_z ((exist _ 2 two_le_6), 1).  *)

(* Basically, do not allow anything too big
   the first term shall encode the number of
   octets used, which is actually less or
   equal to 6
 *)
(* length det specifically for integers,
   which is restricted to 6.
 *)
Lemma eight_le_sz : 8 <= INT_MAX_LEN.
  unfold INT_MAX_LEN. lia.
Qed.

Lemma int_len_det_helper :
  (forall a : nat,
      (fun n : nat => 1 <= n <= 6) a -> (fun z : nat => z < Nat.pow 2 8) a).
Proof. intros. simpl in *. lia. Qed.

Definition int_len_det :=
  restrict_format
    (fun n => 1 <= n <= 6)
    (basic_n_bit_format 8 eight_le_sz)
    (int_len_det_helper)
    (fun a => compare_lt_le_dec 1 6 a).

(* The only way to bypass this problem
   it to make A itself a sigma type
 *)
Definition T := {n | n < 6}.

Require Import ProofIrrelevance.


Lemma int_len_det_helper1 :
  (forall a : nat_T,
      (fun _ => True) a ->
      (fun n : nat => 1 <= n <= 6) ((fun z  => proj1_sig z) a) /\
        (fun x : nat =>
           match compare_lt_le_dec 1 6 x with
           | left pf_le => exist _ x pf_le
           | right _ => exist _ 1 one_le_6
           end) ((fun z  => proj1_sig z) a) = a).
Proof.
  intros. destruct a. simpl in *. split_and. split; auto.
  destruct (compare_lt_le_dec 1 6 x).
  - apply subset_eq_compat. auto.
  - lia. 
Qed.

Lemma int_len_det_helper2 :
  (forall a' : nat,
      (fun n : nat => 1 <= n <= 6) a' ->
      (fun _ : nat_T => True)
        ((fun x : nat =>
            match compare_lt_le_dec 1 6 x with
            | left pf_le => exist _ x pf_le
            | right _ => exist _ 1 one_le_6
            end) a') /\
        (fun z  => proj1_sig z)
          ((fun x : nat =>
            match compare_lt_le_dec 1 6 x with
            | left pf_le => exist _ x pf_le
            | right _ => exist (fun n => 1 <= n <= 6) 1 one_le_6
            end) a') = a').
Proof.
  intros. simpl in *. split; auto.
  destruct (compare_lt_le_dec 1 6 a'); try lia. 
  simpl. auto. 
Qed.

Definition int_len_det_sig :=
  proj_format
    (fun z : nat_T => True)
    int_len_det
    (fun z => proj1_sig z)
    (fun x =>
       match compare_lt_le_dec 1 6 x with
       | left pf_le =>  exist _ x pf_le
       | right _ => exist _ 1 one_le_6
       end)
    int_len_det_helper1
    int_len_det_helper2
    (fun _ => left I).

Lemma nat_len_det_le_int_max :
  forall z : nat_T,
    proj1_sig z * 8 <= INT_MAX_LEN.
Proof.
  intros. destruct z. simpl. unfold INT_MAX_LEN.
  lia.
Qed.

(* One question remain for the encoding of 0
   It states that the leading 9 bits of the field
   shall not all be 0 and shall not all be 1's.
 *)
(*Eval compute in z_to_nat_bin 0. *)

Definition restrict_nat_pair_helper sz : 
  (forall a : nat,
      (fun n : nat =>
         if Nat.eqb sz 1
         then 0 <= n < Nat.pow 2 (sz * 8)
         else Nat.pow 2 ((sz - 1) * 8 - 1) <= n <
                Nat.pow 2 (sz * 8) - Nat.pow 2 ((sz - 1) * 8 - 1)) a ->
      (fun z : nat => z < Nat.pow 2 (sz * 8)) a).
Proof.
  intros. simpl in *.
  destruct (Nat.eqb sz 1); lia. 
Qed.

Definition restrict_nat_pair_dec sz :
  (forall a, {(fun n : nat =>
       if Nat.eqb sz 1
       then 0 <= n < Nat.pow 2 (sz * 8)
       else Nat.pow 2 ((sz - 1) * 8 - 1) <= n <
              Nat.pow 2 (sz * 8) -  Nat.pow 2 ((sz - 1) * 8 - 1)) a} +
     {~
        (fun n : nat =>
           if Nat.eqb sz 1
           then 0 <= n < Nat.pow 2 (sz * 8)
           else Nat.pow 2 ((sz - 1) * 8 - 1) <= n <
                  Nat.pow 2 (sz * 8) -  Nat.pow 2 ((sz - 1) * 8 - 1)) a}).
Proof.
  intros.
  destruct (Nat.eqb sz 1) eqn:E.
  - apply sumbool_and1.
    + apply Compare_dec.le_dec.
    + apply Compare_dec.lt_dec.
  - apply sumbool_and1.
    + apply Compare_dec.le_dec.
    + apply Compare_dec.lt_dec.
Defined.
      
Definition restrict_nat_pair (sz : nat) (pf_sz : sz * 8 <= INT_MAX_LEN) :=
  restrict_format
    (fun n => if (Nat.eqb sz 1) then
                0 <= n < Nat.pow 2 (sz * 8)
              else
                Nat.pow 2 ((sz - 1) * 8 - 1) <= n <
                  Nat.pow 2 (sz * 8) -  Nat.pow 2 ((sz - 1) * 8 - 1))
    (basic_n_bit_format (sz * 8) pf_sz)
    (restrict_nat_pair_helper sz)
    (restrict_nat_pair_dec sz).
    
Definition nat_pair_format :=
  sigma_format
    int_len_det_sig
    _
    (fun z => restrict_nat_pair (proj1_sig z) (nat_len_det_le_int_max z)).

Lemma to_bit_sz_range (n a : nat) :
  0 < a -> 
  a < Nat.pow 2 n ->  
  to_bit_sz a <= n.
Proof.
  intros. unfold to_bit_sz.
  assert (G := PeanoNat.Nat.log2_lt_pow2 a n H). 
  lia.
Qed.

Lemma sz_to_num_octets_range n sz :
  0 < n ->
  sz <=  n * 8 - 1  ->
  sz_to_num_octets sz <= n.
Proof.
  intros. 
  unfold sz_to_num_octets.
  assert (sz < 8 * n). {  lia. } 
  assert (G :=  PeanoNat.Nat.Div0.div_lt_upper_bound sz 8 n H1).
  lia.
Qed.

Definition f a' := sz_to_num_octets (to_bit_sz (a' - 1)) * 8.
(*Eval compute in f 129. *)

(* Some basic idea for proof.
   a should not be 0.
   by simply flipping a, it should not exceed 2^k.
   
 *)
Lemma lnot_eq a k :
  0 < a < Nat.pow 2 (k) -> 
  PeanoNat.Nat.lnot a k = (Nat.pow 2 k - 1) - a.
Proof.
  intros.
  assert (PeanoNat.Nat.log2 a < k).
  { rewrite <- PeanoNat.Nat.log2_lt_pow2; try lia. } 
  assert (G := PeanoNat.Nat.add_lnot_diag_low a k H0).
  rewrite PeanoNat.Nat.ones_equiv, PeanoNat.pred_of_minus in G.
  rewrite <- G.
  lia. 
Qed.
  
Lemma two_comp_le1 a k:
  0 < k -> 
  0 < a <= Nat.pow 2 (k - 1) -> 
  PeanoNat.Nat.lnot a k + 1 < Nat.pow 2 k.
Proof.
  intros. 

  assert (a < Nat.pow 2 k).
  { assert (k = S (k - 1)). { lia. }
    rewrite H1, PeanoNat.Nat.pow_succ_r'.
    lia. } 
  
  rewrite lnot_eq; lia.
Qed.

Lemma num_octets_le a k :
  0 < a -> 
  k = sz_to_num_octets (to_bit_sz (a - 1)) * 8 -> 
  a <= Nat.pow 2 (k - 1).
Proof.
  intros.
  unfold sz_to_num_octets, to_bit_sz in *.
  assert (a - 1 < Nat.pow 2 (k - 1)).
  - destruct (PeanoNat.Nat.eq_dec a 1).
    + subst. simpl. lia.
    + rewrite PeanoNat.Nat.log2_lt_pow2; auto. 
      * remember (Nat.log2 (a - 1)) as l.
        rewrite H0.
        rewrite PeanoNat.Nat.mul_add_distr_r. 
        assert (G := PeanoNat.Nat.Div0.div_mod (l + 1) 8).
        assert (G' : 8 <> 0). { auto. }
        assert (G1 := PeanoNat.Nat.mod_upper_bound (l + 1) 8 G').
        lia.
      * lia.
  - lia.
Qed.


Lemma num_octets_le2 a k :
  k = sz_to_num_octets (to_bit_sz a) -> 
  a < Nat.pow 2 (k * 8 - 1).
Proof.
  intros. unfold sz_to_num_octets, to_bit_sz in *. 
  destruct a.
  - assert (2 <> 0). { lia. }
    simpl in H. rewrite H. simpl; auto. lia. 
  - rewrite  PeanoNat.Nat.log2_lt_pow2.
    + remember (Nat.log2 (S a)) as l.
      rewrite H. rewrite PeanoNat.Nat.mul_add_distr_r.
      assert (G := PeanoNat.Nat.Div0.div_mod (l + 1) 8).
      assert (G' : 8 <> 0). { auto. }
      assert (G1 := PeanoNat.Nat.mod_upper_bound (l + 1) 8 G').
      lia.
    + lia.
Qed.

Lemma num_octets_le3 a k :
  1 <= k -> 
  k = sz_to_num_octets (to_bit_sz a) -> 
  a < Nat.pow 2 (k * 8).
Proof.
  intros. 
  assert (G := num_octets_le2 a k H0).
  assert (G1 := PeanoNat.Nat.pow_le_mono_r 2 (k * 8 - 1) (k * 8)).
  lia.
Qed.

Lemma num_octets_le3_helper a' k :
  2 <= k -> 
  a' < Nat.pow 2 (k * 8 - 1) -> 
  a' < Nat.pow 2 (k * 8) - Nat.pow 2 (k * 8 - 9).
Proof.
  intros. 
  assert (G : k * 8 = (k * 8 - 9) + 9). { lia. } 
  assert (G1 : k * 8 - 1 = (k * 8 - 9) + 8). { lia. }

  rewrite G at 1. rewrite G1 in H0.
  remember (k * 8 - 9) as l.
  assert ( PeanoNat.Nat.pow 2 9 = 512). { 
    Transparent Nat.pow. simpl. auto. }
  assert ( PeanoNat.Nat.pow 2 8 = 256). { 
    simpl. auto. }
  assert (K : Nat.pow 2 (l + 9) = 512 * Nat.pow 2 l ).
  { rewrite PeanoNat.Nat.pow_add_r. lia. } 
  assert (K1 : Nat.pow 2 (l + 8) = 256 * Nat.pow 2 l ).
  { rewrite PeanoNat.Nat.pow_add_r. lia. } 
  lia.
Qed.
  
Lemma num_octets_ge a k :
  0 < a -> 
  2 <= k -> 
  k = sz_to_num_octets (to_bit_sz a) -> 
  Nat.pow 2 (k * 8 - 9) <= a.
Proof.
  intros. unfold sz_to_num_octets, to_bit_sz in *.
  rewrite H1.
  assert ((Nat.div (Nat.log2 a + 1) 8 + 1) * 8 - 9 =
            8 * Nat.div (Nat.log2 a + 1) 8 - 1).
  { lia. }
  rewrite H2.
  assert (G := PeanoNat.Nat.Div0.div_mod (Nat.log2 a + 1) 8).
  
  rewrite PeanoNat.Nat.log2_le_pow2; auto.
  lia.
Qed.
  
(* Eval compute in to_bit_sz 8. *)
Lemma two_comp_le a' k :
  0 < a' -> 
  k = sz_to_num_octets (to_bit_sz (a' - 1)) * 8
  -> to_2_complement k a' < Nat.pow 2 k.
Proof.
  (* First we need to find what is the range of a',
     aka, a' relation with Nat.pow 2 k
   *)
  intros.
  unfold sz_to_num_octets, to_bit_sz, to_2_complement in *.
  assert (G := num_octets_le a' k H H0). 
  
  apply two_comp_le1; auto. lia.
Qed.

Lemma two_comp_le2 a k:
  1 < a ->
  2 <= k ->
  k =  sz_to_num_octets (to_bit_sz (a - 1)) -> 
  to_2_complement (k * 8) a < Nat.pow 2 (k * 8) - Nat.pow 2 (k * 8 - 9).
Proof.
  intros. unfold to_2_complement.
  assert (a < Nat.pow 2 (k * 8)).
  { assert (K :=  num_octets_le a (k * 8)).
    assert (G2 := PeanoNat.Nat.pow_lt_mono_r 2 (k * 8 - 1) (k * 8)).
    lia. } 
    
  rewrite lnot_eq; try lia. 
  - assert (G := num_octets_ge (a-1) k). 
    assert (G1 := PeanoNat.Nat.pow_nonzero 2 (k * 8)).
    assert (G2 := PeanoNat.Nat.pow_lt_mono_r 2 (k * 8 - 9) (k * 8)).
    lia. 
Qed.

Lemma two_comp_ge_finer a' k :
  0 < a' -> 
  k = sz_to_num_octets (to_bit_sz (a' - 1)) * 8
  -> Nat.pow 2 (k - 1) <= to_2_complement k a'.
Proof.
  intros.
  unfold sz_to_num_octets, to_bit_sz, to_2_complement in *.
  assert (G := num_octets_le a' k H H0).
  assert (k = S (k - 1)). { lia. }
  rewrite lnot_eq.
  - rewrite H1 at 2.
    rewrite PeanoNat.Nat.pow_succ_r; lia.
  -  rewrite H1, PeanoNat.Nat.pow_succ_r; lia.
Qed.
  
Lemma two_comp_ge a' k :
  0 < a' -> 
  k = sz_to_num_octets (to_bit_sz (a' - 1)) * 8 -> 
  16 <= k ->
  Nat.pow 2 (k - 9) <= to_2_complement k a'.
Proof.
  intros.
  assert (Nat.pow 2 (k - 9) < Nat.pow 2 (k - 1)).
  { apply PeanoNat.Nat.pow_lt_mono_r; lia.  }   

  assert (G := two_comp_ge_finer a' k H H0).
  lia. 
Qed.

Lemma two_comp_inv a k :
  0 < a < Nat.pow 2 k -> 
  (to_2_complement k (to_2_complement k a)) = a.
Proof.
  intros. unfold to_2_complement.
  repeat rewrite lnot_eq; auto; lia. 
Qed.

  (* Now we prove the property with 2-complement *)

Lemma int_format_helper1 :
  (forall a : Z,
      (fun z : Z => (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z) a ->
      (fun z : nat_T * nat =>
         (fun _ : nat_T => True) (fst z) /\
            (fun (z0 : nat_T) (n : nat) =>
          if Nat.eqb (proj1_sig z0) 1
          then 0 <= n < Nat.pow 2 (proj1_sig z0 * 8)
          else
           Nat.pow 2 ((proj1_sig z0 - 1) * 8 - 1) <= n <
             Nat.pow 2 (proj1_sig z0 * 8) - Nat.pow 2 ((proj1_sig z0 - 1) * 8 - 1))
              (fst z) (snd z)) 
        (z_to_nat_bin a) /\ nat_bin_to_z (z_to_nat_bin a) = a).
Proof.
 intros. Opaque Z.pow.
  simpl in *. 
  unfold z_to_nat_bin. 
  destruct (a <? 0)%Z eqn:Ez.
  (* Case where z is smaller than 0 *)
  - remember (Z.to_nat (-a)) as a'.
    assert (a' <= Nat.pow 2 47).
    { assert ((Z.opp a <= Z.pow 2 47)%Z).
      { lia. }
      assert (G := Znat.Nat2Z.inj_pow 2 47). 
      assert (E1 : Z.of_nat 2 = 2%Z). { lia. } 
      assert (E2 : Z.of_nat 47 = 47%Z). { lia. }
      rewrite E1, E2 in G.
      rewrite <- G in H0. lia. }
    rewrite Z.ltb_lt in Ez.
    assert (0 < a').
    { lia. }
    
    assert (to_bit_sz (a' - 1) <= 47).
    { destruct a'; try lia.
      destruct a'.
      - simpl. unfold to_bit_sz. simpl. lia.
      - apply to_bit_sz_range; try lia.
    }

    assert (G := sz_to_num_octets_range 6
                   (to_bit_sz (a' - 1))
                   (PeanoNat.Nat.lt_0_succ _ ) H2).
    assert (G1 : 1 <= sz_to_num_octets (to_bit_sz (a' - 1)) <= 6).
    { split; auto. unfold sz_to_num_octets. lia. }  
    
    destruct (compare_lt_le_dec 1 6 (sz_to_num_octets (to_bit_sz (a' - 1))));
      try lia. 
    simpl. remember (sz_to_num_octets (to_bit_sz (a' - 1))) as k.
    split; auto.
    + split; auto.  
      destruct (Nat.eqb k 1) eqn:E.
      * split; try lia. apply two_comp_le; auto.
      * assert ((k- 1) * 8 - 1 = k * 8 - 9).
          { lia. } 
        split.
        { rewrite H3. apply two_comp_ge; auto.
          rewrite PeanoNat.Nat.eqb_neq in E.
          lia.
        } 
        { rewrite H3. rewrite PeanoNat.Nat.eqb_neq in E. 
          apply two_comp_le2; try lia. 

          destruct (PeanoNat.Nat.eq_dec a' 1).
          - unfold to_bit_sz, sz_to_num_octets in Heqk.  rewrite e in Heqk. simpl in Heqk. lia.
          - lia. 
        }     
    + destruct (Nat.ltb (to_2_complement (k * 8) a') (Nat.pow 2 (k * 8 - 1))) eqn:E.
      * rewrite PeanoNat.Nat.ltb_lt in E. 
        assert (E_inv :=  two_comp_ge_finer a' (k * 8) H1). lia. 
      * rewrite two_comp_inv.
        { lia. }
        { split; auto. 
          assert (K := num_octets_le a' (k * 8) H1).
          assert (k * 8 = S (k * 8 - 1)). { lia. }
          rewrite H3. rewrite PeanoNat.Nat.pow_succ_r; lia. }
        
  - remember (Z.to_nat a) as a'.

    assert (a' < Nat.pow 2 47).
    { destruct H. assert (a < Z.pow 2 47)%Z. { lia. }
      assert (E1 : Z.of_nat 2 = 2%Z). { lia. } 
      assert (E2 : Z.of_nat 47 = 47%Z). { lia. }
      assert (G := Znat.Nat2Z.inj_pow 2 47). 
      rewrite E1, E2 in G.
      lia. }
    
    assert  (to_bit_sz a' <= 47).
    { destruct a'.
      - compute. lia.
      - apply to_bit_sz_range; lia. } 
    
    assert (G := sz_to_num_octets_range 6  (to_bit_sz a')
                   (PeanoNat.Nat.lt_0_succ _ ) H1).
    assert (1 <= sz_to_num_octets (to_bit_sz a') <= 6).
    { split; auto. unfold sz_to_num_octets. lia. }

    destruct ( compare_lt_le_dec 1 6 (sz_to_num_octets (to_bit_sz a'))).
    + simpl. remember ( sz_to_num_octets (to_bit_sz a') ) as k.
      split; auto.
      * split; auto.
        destruct (Nat.eqb k 1) eqn:Ek.
        { split; try lia. apply num_octets_le3; auto. destruct H2; auto. }
        { assert ((k - 1) * 8 - 1 = k * 8 - 9). { lia. }
          rewrite H3. 
          split.
          - rewrite PeanoNat.Nat.eqb_neq in Ek.
            apply num_octets_ge; auto; try lia.
            destruct a'; try lia.
            unfold sz_to_num_octets, to_bit_sz in Heqk. simpl in Heqk.
            lia. 
          - assert (L := num_octets_le2 a' k Heqk).
            rewrite PeanoNat.Nat.eqb_neq in Ek.
            apply num_octets_le3_helper; try lia. 
        }
      * destruct (Nat.ltb a' (Nat.pow 2 (k * 8 - 1))) eqn:Ea.
        { lia. }
        { rewrite PeanoNat.Nat.ltb_ge in Ea.
          assert (E_inv := num_octets_le2 a' k Heqk).
          lia. }
    + lia.
Qed.

Lemma tb_sz_octets1 n0 x :
  1 <= x -> 
  n0 < Nat.pow 2 (x * 8 - 1) -> 
  Nat.div (Nat.log2 (n0) + 1) 8 + 1 <= x.
Proof.
  intros.
  destruct n0.
  - simpl.  auto. 
  - assert (G1 := PeanoNat.Nat.Div0.div_mod (Nat.log2 (S n0) + 1) 8). 
    rewrite (PeanoNat.Nat.log2_lt_pow2) in H0; try lia.
Qed.

Lemma tb_sz_octets2 n0 x :
  2 <= x -> 
  Nat.pow 2 ((x - 1) * 8 - 1) <= n0 -> 
  x <= Nat.div (Nat.log2 n0 + 1) 8 + 1.
Proof.
  intros.
  destruct n0.
  - assert (G := PeanoNat.Nat.pow_nonzero 2 ((x - 1) * 8 - 1)). lia.
  - assert (G1 := PeanoNat.Nat.Div0.div_mod (Nat.log2 (S n0) + 1) 8).
    split_and. 
    rewrite ( PeanoNat.Nat.log2_le_pow2) in H0; try lia.

    assert (G2 : (x - 1) * 8 <= Nat.log2 (S n0) + 1).
    { lia. }
    rewrite G1 in G2. 
    assert (G3 := PeanoNat.Nat.mod_upper_bound (Nat.log2 (S n0) + 1) 8).
    lia.
Qed.


Lemma  int_format_helper2 :
  (forall a' : nat_T * nat,
      (fun z : nat_T * nat =>
         (fun _ : nat_T => True) (fst z) /\
           (fun (z0 : nat_T) (n : nat) =>
              if Nat.eqb (proj1_sig z0) 1
              then 0 <= n < Nat.pow 2 (proj1_sig z0 * 8)
              else
                Nat.pow 2 ((proj1_sig z0 - 1) * 8 - 1) <= n <
                  Nat.pow 2 (proj1_sig z0 * 8) - Nat.pow 2 ((proj1_sig z0 - 1) * 8 - 1))
             (fst z) (snd z)) a' ->
      (fun z : Z => (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z) (nat_bin_to_z a') /\
        z_to_nat_bin (nat_bin_to_z a') = a').
Proof.
  intros. Opaque Nat.pow.
  destruct a', n. split_and.
  simpl in H1.
  assert (n0 < Nat.pow 2 (x * 8)).
  { destruct (Nat.eqb x 1); split_and; lia.  }
  split.
  - simpl.
    assert (E1 : Z.of_nat 2 = 2%Z). { lia. } 
    assert (E2 : Z.of_nat 47 = 47%Z). { lia. }
    assert (G' := Znat.Nat2Z.inj_pow 2 47). 
    rewrite E1, E2 in G'.
    
    destruct (Nat.ltb n0 (Nat.pow 2 (x * 8 - 1))) eqn:En0.
    + assert (n0 < Nat.pow 2 47).
      { rewrite PeanoNat.Nat.ltb_lt in En0.
        assert (G := PeanoNat.Nat.pow_le_mono_r 2 (x * 8 - 1) 47).
        lia.
      }
      { lia. }
    + rewrite PeanoNat.Nat.ltb_ge in En0.
      assert (to_2_complement (x * 8) n0 <= Nat.pow 2 47).
      { unfold to_2_complement.
        destruct n0.
        - assert (G := PeanoNat.Nat.pow_nonzero 2 (x * 8 - 1)).
          lia. 
        - rewrite lnot_eq; try lia.
          assert (Nat.pow 2 (x * 8) - 1 - S n0 + 1 = Nat.pow 2 (x * 8) - S n0).
          { lia. } 
          rewrite H4. 
          assert (Nat.pow 2 (x * 8) - S n0 <= Nat.pow 2 (x * 8 - 1)).
          { assert (x * 8 = S (x * 8 - 1)).
            { lia. }
            rewrite H5 at 1. rewrite PeanoNat.Nat.pow_succ_r; try lia.
          }
          assert (M :=  PeanoNat.Nat.pow_le_mono_r 2 (x * 8 - 1) 47).
          lia.
      } 
      split; lia.
  - simpl.
    destruct (Nat.ltb n0 (Nat.pow 2 (x * 8 - 1))) eqn:En0. 
    + unfold z_to_nat_bin.
      assert (Z.ltb (Z.of_nat n0) 0 = false).
      { rewrite Z.ltb_ge. lia. } 
      rewrite H4.
      rewrite Znat.Nat2Z.id.
      rewrite Z.ltb_ge in H4.
      rewrite PeanoNat.Nat.ltb_lt in En0. 

      assert ((sz_to_num_octets (to_bit_sz n0)) = x).
      { unfold to_bit_sz, sz_to_num_octets.
        destruct n0 eqn:En1.
        - simpl. destruct (Nat.eqb x 1) eqn:Ex. 
          + rewrite PeanoNat.Nat.eqb_eq in Ex. subst. auto.
          + assert (E_inv := PeanoNat.Nat.pow_nonzero 2 ((x - 1) * 8 - 1)).
            lia.
        - apply PeanoNat.Nat.le_antisymm. 
          + apply tb_sz_octets1; auto; lia. 
          + destruct (Nat.eqb x 1) eqn:Ex.
            * rewrite PeanoNat.Nat.eqb_eq in Ex. lia.
            * rewrite PeanoNat.Nat.eqb_neq in Ex. 
              apply tb_sz_octets2; auto; lia.
      }         
      rewrite H5. 
      destruct (compare_lt_le_dec 1 6 x) eqn:E.
      * f_equal.
        apply subset_eq_compat. auto.
      * lia.
    + unfold z_to_nat_bin.

      assert ((- Z.of_nat (to_2_complement (x * 8) n0) <? 0)%Z = true).
      { rewrite Z.ltb_lt.
        unfold to_2_complement. lia. } 
      rewrite H4.

      rewrite Z.ltb_lt in H4. rewrite PeanoNat.Nat.ltb_ge in En0.

      rewrite Z.opp_involutive, Znat.Nat2Z.id.
      assert (0 < n0).
      {   assert (G1 := PeanoNat.Nat.pow_nonzero 2 (x * 8 - 1)). lia. }
      
      assert ((sz_to_num_octets
                 (to_bit_sz ((to_2_complement (x * 8) n0) - 1))) = x).
      { unfold to_2_complement. 
        rewrite  PeanoNat.Nat.add_sub.
        (* Need to cosider the case where n0 = 0 *)
        rewrite lnot_eq.
        - apply PeanoNat.Nat.le_antisymm.
          + apply tb_sz_octets1; try lia.
            assert (x * 8 = S (x * 8 - 1)).
            { lia. }
            rewrite H6 at 1. rewrite PeanoNat.Nat.pow_succ_r; try lia.
            assert (NE0 := PeanoNat.Nat.pow_nonzero 2 (x * 8 - 1)). lia. 
          + destruct (Nat.eqb x 1) eqn:Ex.
            * rewrite PeanoNat.Nat.eqb_eq in Ex. subst. simpl.
              unfold sz_to_num_octets. lia.
            * apply tb_sz_octets2.

              rewrite PeanoNat.Nat.eqb_neq in Ex; lia.

              assert (G1 := PeanoNat.Nat.pow_nonzero 2 (x * 8 )).
              assert (G2 := PeanoNat.Nat.pow_lt_mono_r 2 ((x - 1) * 8 - 1)
                              (x * 8)).
              lia. 
        - lia.
      }

      rewrite H6.

      destruct (compare_lt_le_dec 1 6 x) eqn:Ex.
      { f_equal.
        - apply subset_eq_compat. auto.
        - apply two_comp_inv; split; try lia. 
      } 
      { lia. } 
Qed.

Definition int_format :=
  proj_format
    (fun z : Z => (Z.opp (Z.pow 2 47) <= z <= Z.pow 2 47 - 1)%Z)
    nat_pair_format
    z_to_nat_bin
    nat_bin_to_z
    int_format_helper1
    int_format_helper2
    (fun z => sumbool_and1
                (ZArith_dec.Z_le_dec (- Z.pow 2 47) z)
                (ZArith_dec.Z_le_dec z (Z.pow 2 47 - 1))). 

(* This is for ranged extension integer format 
   aka, INTEGER (lb..ub, ...)

   Here, If an extension marker is present, then encode 
   the value as an unconstrained integer. 
   
   Otherwise, encode it normally
 *)
Require Import ASN1Parser.Formats.Term.Boolean. 


(* It needs to be constructed similarly to 
   choose_norm_small_det
 *)
Require Import ASN1Parser.Formats.Term.NormExtFormat.

Definition int_format_ranged_ext (lb ub : Z) (pf : (lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)%Z) <= INT_MAX_LEN )
  := normal_ext_format (ranged_int_format lb ub pf pf2)
       int_format
       (fun a => (sumbool_and1 (ZArith_dec.Z_le_dec lb a)
                    (ZArith_dec.Z_le_dec a ub)))
       (fun a => (sumbool_and1 (ZArith_dec.Z_le_dec (- 2 ^ 47) a)
                    (ZArith_dec.Z_le_dec a (2 ^ 47 - 1)))). 


(*
Definition int_format_ranged_ext_base (lb ub : Z) (pf : (lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)%Z) <= INT_MAX_LEN ) (a : bool):
  T_Format Z
    ((fun (z : Z) =>
        if a
        then ~(lb <= z <= ub)%Z /\ (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z
        else (lb <= z <= ub)%Z)).
  destruct a. 
  - apply (restrict_format
             (fun z => ~(lb <= z <= ub)%Z /\ (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z)
             (int_format)).
    + intros. apply (proj2 H).
    + intros. apply sumbool_and1.
      * apply sumbool_neg.
        apply sumbool_and1; apply ZArith_dec.Z_le_dec. 
      * apply sumbool_and1; apply ZArith_dec.Z_le_dec. 
  - apply ( ranged_int_format lb ub pf pf2).
Defined.

Definition choose_int_format_ranged_ext  (lb ub : Z) (pf : (lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)%Z) <= INT_MAX_LEN )  :=
  sigma_format bool_format
    (*(fun b z => if b then
                  ((- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z)
                else
                  (lb <= z <= ub)%Z) *)
    _ 
    (int_format_ranged_ext_base lb ub pf pf2). 

Lemma int_format_ranged_ext_helper1
  (lb ub : Z) :
  (forall a : Z,
      (fun z : Z =>
         (lb <= z <= ub)%Z \/
           ~ (lb <= z <= ub)%Z /\
             (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z) a ->
      (fun z : bool * Z =>
         (fun _ : bool => True) (fst z) /\
           (fun (b : bool) (z0 : Z) =>
              if b
              then
                ~ (lb <= z0 <= ub)%Z /\
                  (- 2 ^ 47 <= z0 <= 2 ^ 47 - 1)%Z
              else (lb <= z0 <= ub)%Z) (fst z) 
             (snd z))
        ((fun z : Z =>
            if ((lb <=? z)%Z && (z <=? ub)%Z)%bool
            then (false, z)
            else (true, z)) a) /\
        (fun x : bool * Z => snd x)
          ((fun z : Z =>
              if ((lb <=? z)%Z && (z <=? ub)%Z)%bool
              then (false, z)
              else (true, z)) a) = a).
  intros.
  destruct ((lb <=? a)%Z && (a <=? ub)%Z)%bool eqn:E; rewrite E. 
  - apply eq_sym in E. 
    apply Bool.andb_true_eq in E. split_and.
    apply eq_sym, Zbool.Zle_bool_imp_le in H0, H1.
    repeat split; simpl; auto. 
    
  - simpl. apply Bool.andb_false_iff in E.
    simpl in H.
    repeat rewrite Z.leb_gt in E.
    destruct H.
    + lia.
    + destruct H. repeat split; auto; lia. 
Qed.

Lemma int_format_ranged_ext_helper2
  (lb ub : Z) :
  (forall b : bool * Z,
      (fun z : bool * Z =>
         (fun _ : bool => True) (fst z) /\
           (fun (b0 : bool) (z0 : Z) =>
              if b0
              then
                ~ (lb <= z0 <= ub)%Z /\
                  (- 2 ^ 47 <= z0 <= 2 ^ 47 - 1)%Z
              else (lb <= z0 <= ub)%Z) (fst z) 
             (snd z)) b ->
      (fun z : Z =>
         (lb <= z <= ub)%Z \/
           ~ (lb <= z <= ub)%Z /\
             (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z)
        ((fun x : bool * Z => snd x) b) /\
        (fun z : Z =>
           if ((lb <=? z)%Z && (z <=? ub)%Z)%bool
           then (false, z)
           else (true, z)) ((fun x : bool * Z => snd x) b) =
          b).
Proof.
  intros. destruct b.  simpl in *. split_and.
  destruct b eqn:Eb.
  - split.
    + destruct ( z_range_dec lb ub z).
      * left; auto.
      * right. auto.
    + split_and.
      destruct ((lb <=? z)%Z && (z <=? ub)%Z)%bool eqn:Ez; auto.
      apply eq_sym in Ez. 
      apply Bool.andb_true_eq in Ez. split_and.
    apply eq_sym,  Zbool.Zle_bool_imp_le in H2, H4. 
    lia.
  - split; auto.
    destruct ((lb <=? z)%Z && (z <=? ub)%Z)%bool eqn:Ez; auto.
    apply Bool.andb_false_iff in Ez.
    repeat rewrite Z.leb_gt in Ez.
    lia.
Qed.

Definition int_format_ranged_ext_dec lb ub :
  dec_P
    (fun z : Z =>
       (lb <= z <= ub)%Z \/
         ~ (lb <= z <= ub)%Z /\
           (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z).
  unfold dec_P.
  intros.
  apply sumbool_or1.
  - apply sumbool_and1; apply ZArith_dec.Z_le_dec.
  - apply sumbool_and1.
    + apply sumbool_neg.
      apply sumbool_and1; apply ZArith_dec.Z_le_dec.
    + apply sumbool_and1; apply ZArith_dec.Z_le_dec.
Defined.

Definition int_format_ranged_ext (lb ub : Z) (pf : (lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)%Z) <= INT_MAX_LEN )
(*  : T_Format Z (fun z =>  (lb <= z <= ub)%Z  \/ ((- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z)) *)  :=
  proj_format
     (fun z =>  (lb <= z <= ub)%Z  \/ (( ~(lb <= z <= ub)%Z) /\  (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%Z))
     (choose_int_format_ranged_ext lb ub pf pf2)
     (fun z => if andb (lb <=? z)%Z (z <=? ub)%Z  then
                 (false, z) else (true, z))
     (fun x => snd x) 
     (int_format_ranged_ext_helper1 lb ub )
     (int_format_ranged_ext_helper2 lb ub )
     (int_format_ranged_ext_dec lb ub ).
*)

