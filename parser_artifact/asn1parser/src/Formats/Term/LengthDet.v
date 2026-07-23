Require Import 
        Lia
        Coq.Logic.FunctionalExtensionality
        ASN1Parser.Formats.Comb
        ASN1Parser.Formats.CombFormat
        ASN1Parser.Formats.Term.NonNeg
        ASN1Parser.Formats.Term.Boolean.

(* Unconstrained length or large 'upper bound' *)
(* Note that we do not consider the case where
   n > 16K
 *)

(* We probably need another combinator that will encode a 
   fixed thing, that is equivalent to a Unit type. 
 *)
Definition fix_format {A : Set} {P : A -> Prop} (fmt : T_Format A P)
  (a : A) (pfa : P a)
  (A_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  : T_Format A (fun a' => a' = a) :=
  restrict_format
    (fun a' => a' = a)
    fmt
    (fun a0 eq_a => eq_ind a P pfa a0 (eq_sym eq_a))
    (fun a0 => A_dec a0 a). 

Definition ONE_BYTE_LMT := Nat.pow 2 7.
Definition TWO_BYTE_LMT := Nat.pow 2 14.

Ltac le_int_max := unfold INT_MAX_LEN; lia. 


(* Here, since we are not considering anything larger than 
   2^14, we need to have a way to represent a fixed format. 
   That is some format that is just there, but does not 
   actually serve a purpose. 
 *)

(* This is the one-bit plus 14 nat format. 
   Here we have to force this format to only take 
   n >= Nat.pow 2 7.
 *)

Lemma fifteen_le_sz : 15 <= INT_MAX_LEN.
  unfold INT_MAX_LEN. lia. Qed.

Definition large_det_helper3 :
  (forall a : nat, (fun n : nat => n < Nat.pow 2 14) a ->
            (fun z : nat => z < Nat.pow 2 15) a).
Proof.
  intros. Opaque Nat.pow. simpl in *.
  assert (G := PeanoNat.Nat.pow_le_mono_r 2 14 15).
  lia.
Qed.

Definition large_det_format1 :=
    restrict_format
      (fun n => n < Nat.pow 2 14)
      (basic_n_bit_format 15 fifteen_le_sz)
      large_det_helper3
      (fun a => Compare_dec.lt_dec a (Nat.pow 2 14)).

Lemma choose_len_det_helper (a : bool) : (if a then 15 else 7) <= INT_MAX_LEN.
  unfold INT_MAX_LEN. destruct a; lia. Qed.

Lemma choose_len_det_helper2 (a : bool) : (forall a0 : nat,
   (if a then Nat.pow 2 7 <= a0 < Nat.pow 2 14 else a0 < Nat.pow 2 7) ->
   a0 < Nat.pow 2 (if a then 15 else 7)).
Proof.
  intros. destruct a.
  - assert (G := PeanoNat.Nat.pow_le_mono_r 2 14 15).
    lia.
  - assumption.
Qed.

Definition choose_len_det_helper3 (a : bool) a0 :
  {if a then Nat.pow 2 7 <= a0 < Nat.pow 2 14 else a0 < Nat.pow 2 7} +
    {~ (if a then Nat.pow 2 7 <= a0 < Nat.pow 2 14 else a0 < Nat.pow 2 7)}.
  destruct a.
  - apply (sumbool_and1
                   (Compare_dec.le_dec (Nat.pow 2 7) a0)
                   (Compare_dec.lt_dec a0 (Nat.pow 2 14))).
  - apply (Compare_dec.lt_dec a0 (Nat.pow 2 7)).
Defined.



Definition choose_len_det_format (a : bool)
  : T_Format nat (fun (n : nat) =>
                if a then Nat.pow 2 7 <= n < (Nat.pow 2 14)
                else n < (Nat.pow 2 7)) :=
    restrict_format
      (fun (n : nat) =>
         if a then Nat.pow 2 7 <= n < (Nat.pow 2 14)
         else n < (Nat.pow 2 7))
      (basic_n_bit_format (if a then 15 else 7) (choose_len_det_helper a))
      (choose_len_det_helper2 a)
      (choose_len_det_helper3 a).

(* This is a intermediate format that has both the 
   bit-chooser and the length. 
 *)

Definition bit_len_format :=
   sigma_format
    (bool_format)
    (fun b n => if b then Nat.pow 2 7 <= n < (Nat.pow 2 14)
                    else n < (Nat.pow 2 7))
    choose_len_det_format.

(* Here, we are a lot more stricter than ASN1tools. 
   It seems that in ASN1tools, they do not care about 
 *)

Require Import ASN1Parser.tact.

Definition det_le_helper :
  (forall a : nat,
      (fun n : nat => n < Nat.pow 2 14) a ->
      (fun z : bool * nat =>
         (fun _ : bool => True) (fst z) /\
           (fun (b : bool) (n : nat) =>
              if b then Nat.pow 2 7 <= n < Nat.pow 2 14 else n < Nat.pow 2 7)
             (fst z) (snd z))
        ((fun n : nat =>
            if Nat.ltb n (Nat.pow 2 7) then (false, n) else (true, n)) a) /\
        (fun z : bool * nat => snd z)
          ((fun n : nat =>
              if Nat.ltb n (Nat.pow 2 7) then (false, n) else (true, n)) a) = a).
Proof.
  intros.
  destruct (Nat.ltb a (Nat.pow 2 7)) eqn:E; rewrite E; unfold fst, snd.
  - rewrite PeanoNat.Nat.ltb_lt in E.
    split; auto.
  - rewrite PeanoNat.Nat.ltb_ge in E.
    split; auto.
Qed.

Lemma det_le_helper2 :
  (forall a' : bool * nat,
      (fun z : bool * nat =>
         (fun _ : bool => True) (fst z) /\
           (fun (b : bool) (n : nat) =>
              if b then Nat.pow 2 7 <= n < Nat.pow 2 14 else n < Nat.pow 2 7)
             (fst z) (snd z)) a' ->
      (fun n : nat => n < Nat.pow 2 14) ((fun z : bool * nat => snd z) a') /\
        (fun n : nat =>
           if Nat.ltb n (Nat.pow 2 7) then (false, n) else (true, n))
          ((fun z : bool * nat => snd z) a') = a').
  intros.
  destruct a'. unfold snd, fst in *.
  destruct b; split_and. 
  - split; auto. rewrite <- PeanoNat.Nat.ltb_ge in H.
    rewrite H. auto.
  - split.
    + eapply PeanoNat.Nat.lt_trans.
      * apply H1.
      * apply PeanoNat.Nat.pow_lt_mono_r; lia.
    + rewrite <-  PeanoNat.Nat.ltb_lt in H1.
      rewrite H1. auto.
Qed.

(* This is the unconstrained-length-determinant *)

Opaque Nat.pow Nat.add Nat.leb.
Opaque Compare_dec.lt_dec Compare_dec.le_dec.
Opaque ByteBuffer.put_n_nat ByteBuffer.read_n_nat.
Opaque proj_serialize sigma_serialize append_serialize restrict_serialize
  proj_parse bind_parse restrict_parse sigma_parse append_parse.
Opaque fst snd. 

Definition uncons_len_det_format :=
  proj_format
    (fun n => n < Nat.pow 2 14)
    bit_len_format
    (fun n => if (Nat.ltb n (Nat.pow 2 7)) then
                (false, n) else
                (true, n))
    (fun z => snd z)
    det_le_helper
    det_le_helper2
    (fun n => Compare_dec.lt_dec n (Nat.pow 2 14)).

Opaque bool_format. 
Require Import ASN1Parser.Formats.SameVerProp.
Lemma det_SameVer :
  parse_to_SameVer (T_Parse _ _ uncons_len_det_format).
Proof.
  simpl. apply proj_SameVer. 
  assert (G := sigma_SameVer
                 (T_Parse bool (fun _ : bool => True) bool_format)
                 (fun (b : bool) (n : nat) =>
                    if b then Nat.pow 2 7 <= n < Nat.pow 2 14 else n < Nat.pow 2 7)
                 (fun (a : bool) (_ : True) =>
                    restrict_parse (choose_len_det_helper3 a)
                      (ByteBuffer.read_n_nat (if a then 15 else 7))))
  .
  apply G.
  - apply proj_SameVer. 
    apply (basic_bit_SameVer 1).
  - intros. apply restrict_SameVer.
    apply basic_bit_SameVer.
Qed.
  
(* Sanity test *)
(*
Example test1 := encode_len_det_un 20.
Eval compute in test1.
Eval compute in test_decoder decode_len_det_un test1.
*)

(* Normally small length determinant. 
   
   The thing about normally small length det is that
   usually it should be smaller than 64. And the 
   encoding is from (1..64) in 6 bits.
   
   But sometimes it  might be large, in which case we 
   would use the unconstrained-len-det. But here the 
   encoding is n instead of (n-1).

   Also, don't confuse it with the normally small whole
   number. 
 *)
Lemma one_le_64 : 1 <= 64. lia. Qed.

Transparent Nat.sub Nat.leb Nat.pow.

Lemma sixty_four_le_max :  to_bit_sz (64 - 1) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. simpl. compute. lia. Qed.

Definition choose_norm_small_det (b : bool) : 
  T_Format nat (fun n : nat => if b then 65 <= n < Nat.pow 2 14 else 1 <= n <= 64 ).
  destruct b. 
  - apply (restrict_format
             (fun n => 65 <= n < Nat.pow 2 14)
             uncons_len_det_format
             (fun a pf => proj2 pf)
             (fun a => sumbool_and1
                         (Compare_dec.le_dec 65 a)
                         (Compare_dec.lt_dec a (Nat.pow 2 14)))).
  - apply  (nat_range_format 1 64 one_le_64 sixty_four_le_max).
Defined.


Opaque Nat.sub Nat.leb Nat.pow Nat.log2.
Opaque uncons_len_det_format.

Require Import ASN1Parser.Formats.Term.NormExtFormat.

(* Here is the format of the bit and the format definition *)
Definition bit_norm_small_len_format :=
  sigma_format
    bool_format
    (fun b n => if b then  
                  (65 <= n < Nat.pow 2 14)
                else
                  1 <= n <= 64)
    (fun b => choose_norm_small_det b).

Transparent fst snd. 

Lemma norm_small_helper1
  : (forall a : nat,
        (fun n : nat => 1 <= n < Nat.pow 2 14) a ->
        (fun z : bool * nat =>
           (fun _ : bool => True) (fst z) /\
             (fun (b : bool) (n : nat) =>
                if b then 65 <= n < Nat.pow 2 14 else 1 <= n <= 64) 
               (fst z) (snd z))
          ((fun n : nat =>
              if (Nat.leb 1 n && Nat.leb n 64)%bool then (false, n) else (true, n)) a) /\
          (fun z : bool * nat => snd z)
            ((fun n : nat =>
                if (Nat.leb 1 n && Nat.leb n 64)%bool then (false, n) else (true, n)) a) =
            a).
Proof.
  intros.
  destruct ((Nat.leb 1 a && Nat.leb a 64)%bool) eqn:E; split; unfold fst, snd; rewrite E; auto.
  - apply andb_prop in E.
    repeat rewrite PeanoNat.Nat.leb_le in E.
    split; auto.
  - destruct H.
    rewrite <- PeanoNat.Nat.leb_le in H.
    rewrite H in E. 
    rewrite Bool.andb_true_l in E.
    rewrite  PeanoNat.Nat.leb_gt in E.
    split; auto.
Qed.

Lemma norm_small_helper2
  : (forall a' : bool * nat,
        (fun z : bool * nat =>
           (fun _ : bool => True) (fst z) /\
             (fun (b : bool) (n : nat) =>
                if b then 65 <= n < Nat.pow 2 14 else 1 <= n <= 64) 
               (fst z) (snd z)) a' ->
        (fun n : nat => 1 <= n < Nat.pow 2 14) ((fun z : bool * nat => snd z) a') /\
          (fun n : nat =>
             if (Nat.leb 1 n && Nat.leb n 64)%bool then (false, n) else (true, n))
            ((fun z : bool * nat => snd z) a') = a').
Proof.
  intros.
  destruct a'. unfold fst, snd in *. destruct H.
  destruct (andb (Nat.leb 1 n) (Nat.leb n 64)) eqn:E1. 
  - apply andb_prop in E1.
    repeat rewrite PeanoNat.Nat.leb_le in E1.
    destruct b; try lia.
    split; auto.
    assert (64 = Nat.pow 2 6). { simpl. reflexivity. }
    destruct E1.
    split; auto.
    eapply PeanoNat.Nat.le_lt_trans.
    + rewrite H1 in H3.
      apply H3. 
    + apply PeanoNat.Nat.pow_lt_mono_r; lia. 
  - destruct b.
    + split; auto. lia.
    + repeat rewrite <- PeanoNat.Nat.leb_le in H0.
      destruct H0.
      rewrite H0, H1 in E1.
      simpl in E1. discriminate.
Qed.


(* Normally small length determinant *)
Definition normally_small_len_det_format :=
  proj_format
    (fun n => 1 <= n < Nat.pow 2 14)
    bit_norm_small_len_format
    (fun n => if andb (Nat.leb 1 n) (Nat.leb n 64)
              then (false, n) else (true, n))
    (fun z => snd z)
    norm_small_helper1
    norm_small_helper2
    (fun n => sumbool_and1
                (Compare_dec.le_dec 1 n)
                (Compare_dec.lt_dec n (Nat.pow 2 14))). 

Definition small_enc := T_Serial _ _ normally_small_len_det_format.
Definition small_dec := T_Parse _ _ normally_small_len_det_format.

Lemma small_det_SameVer :
  parse_to_SameVer (T_Parse _ _ normally_small_len_det_format).
Proof.
  apply proj_SameVer.
  unfold bit_norm_small_len_format. 
  eassert (G :=  sigma_SameVer
                   (T_Parse bool (fun _ : bool => True) bool_format)
                   (fun (b : bool) (n : nat) =>
                      if b then 65 <= n < Nat.pow 2 14 else 1 <= n <= 64)
                   (fun (a : bool) (_ : True) =>
                      T_Parse nat
                        (fun n : nat =>
                           if a then 65 <= n < Nat.pow 2 14 else 1 <= n <= 64)
                        (choose_norm_small_det a))).
  apply G. 

  apply proj_SameVer.
  - apply (basic_bit_SameVer 1).
  - intros.
    destruct a.
    + apply restrict_SameVer.
      apply det_SameVer.
    + apply proj_SameVer.
      apply restrict_SameVer.
      apply basic_bit_SameVer.
Qed.

Definition len_det_ranged_ext (lb ub : nat) (pf : (lb <= ub))
  (pf2 : to_bit_sz (ub - lb) <= INT_MAX_LEN )
  := normal_ext_format (nat_range_format lb ub pf pf2)
       uncons_len_det_format
       (fun a => (sumbool_and1 (Compare_dec.le_dec lb a)
                    (Compare_dec.le_dec a ub)))
       (fun a => Compare_dec.lt_dec a (Nat.pow 2 14)).


(* This part is for size constraint, which is used in BIT 
   STRING, OCTET STRING, and SEQUENCE OF. We would ignore the
   extension for SIZE constraint for now.
 *)
(* Sanity test *)
(* 
Example test2 := encode_len_det_nm 42.
Eval compute in test2. 
Eval compute in test_decoder decode_len_det_nm test2.
*)


(* 
Example t3 := encode_constrained_nat 5 99 6. 
Eval compute in t3.
Eval compute in test_decoder (decode_constrained_nat 5 99) t3. 
*)

(* Here is about the abstraction of size_constraint. Because that 
   Octet, Bit and seq-of all use size_constraint. Potentially there 
   is a unified way of representing it. Ignore the extension for now
   
   The idea is (ub upper bound, lb lower bound)
   
   1. Constrained to be same length (ub < 64K), no length det is 
      encoded and the list of components shall be appended one by one. 
   
   2. Constrained Whole Number length det if ub is set (ub < 64K), 
      encode the length as Constrained_length_det and then encode the 
      list. 

   3. No constraints (Or the cases where ub >= 64K), then lb would be 
      set to zero. And it would be encoded as a unconstrained length 
      det. 

 *)

(*Inductive SIZE_Cons :=
| Fixed_Size (n : nat)
| Ranged_Size (lb ub : nat)
| No_Cons.
*)

