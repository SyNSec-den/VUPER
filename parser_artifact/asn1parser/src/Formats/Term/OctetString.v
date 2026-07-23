Require Import
  BinInt
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.LengthDet
  ASN1Parser.Formats.Term.NonNeg
  ASN1Parser.Formats.Term.Integer
  ASN1Parser.Formats.Term.ByteList.

(* we do not need encode octet string simple because it is just 
   encode_byte_list and decode_byte_list.

   Octet String is represented as list byte.
 *)

(* One of the things we need to note is about the wierd 
   constraint where it could be another type value, whose 
   length would be a multiple of 8 (i.e., it shall be 
   represented in some octets. 

   And the problem is that you need to figure out this 
   information at compile time. So we shelve this problem for now.
 *)
Opaque Nat.pow.

Definition octet_string := list Byte.byte. 

Definition list_true {A : Type} (a : list A) :
  ListFormat.list_and (fun _  => True) a.
Proof.
  induction a.
  - simpl. auto.
  - simpl.  split; auto.
Qed.

Definition os_no_cons_helper1 :
  (forall a : list Byte.byte,
      (fun bs : list Byte.byte => (fun n : nat => n < Nat.pow 2 14) (length bs))
        a ->
      (fun z : nat * list Byte.byte =>
         (fun n : nat => n < Nat.pow 2 14) (fst z) /\
           (fun (n : nat) (l : list Byte.byte) =>
              ListFormat.list_and (fun _ : Byte.byte => True) l /\ length l = n)
             (fst z) (snd z)) ((fun bs : list Byte.byte => (length bs, bs)) a) /\
        (fun z : nat * list Byte.byte => snd z)
          ((fun bs : list Byte.byte => (length bs, bs)) a) = a).
Proof. intros. simpl in *. repeat split; auto.
       apply list_true .
Qed.

Definition os_no_cons_helper2 :
  (forall a' : nat * list Byte.byte,
      (fun z : nat * list Byte.byte =>
         (fun n : nat => n < Nat.pow 2 14) (fst z) /\
           (fun (n : nat) (l : list Byte.byte) =>
              ListFormat.list_and (fun _ : Byte.byte => True) l /\ length l = n)
             (fst z) (snd z)) a' ->
      (fun bs : list Byte.byte => (fun n : nat => n < Nat.pow 2 14) (length bs))
        ((fun z : nat * list Byte.byte => snd z) a') /\
        (fun bs : list Byte.byte => (length bs, bs))
          ((fun z : nat * list Byte.byte => snd z) a') = a').
Proof.
  intros. destruct a'. simpl in *. tact.split_and. subst.  split; auto.
Qed.

(* No Explicit Constraint *)
Definition octet_string_no_cons_format :=
  proj_format
    (fun bs : list Byte.byte =>
       (length bs < Nat.pow 2 14))
    (sigma_format
       uncons_len_det_format
       _
       (fun n => byte_list_format n))
    (fun bs => (length bs, bs))
    (fun z => snd z)
    os_no_cons_helper1
    os_no_cons_helper2
    (fun bs => Compare_dec.lt_dec (length bs) (Nat.pow 2 14))
.

Lemma os_ranged_helper1 lb ub :
  (forall a : list Byte.byte,
        (fun bs : list Byte.byte => (lb <= Z.of_nat (length bs) <= ub)%Z) a ->
        (fun z : Z * list Byte.byte =>
         (fun z0 : Z => (lb <= z0 <= ub)%Z) (fst z) /\
         (fun (n : Z) (la : list Byte.byte) =>
          ListFormat.list_and (fun _ : Byte.byte => True) la /\
          length la = Z.to_nat n) (fst z) (snd z))
          ((fun bs : list Byte.byte => (Z.of_nat (length bs), bs)) a) /\
        (fun z : Z * list Byte.byte => snd z)
          ((fun bs : list Byte.byte => (Z.of_nat (length bs), bs)) a) = a).
Proof.
  intros. simpl in *. destruct H. repeat split; auto.
  apply list_true.
  rewrite Znat.Nat2Z.id. auto. 
Qed.

Lemma os_ranged_helper2 lb ub (pf : (0 <= lb <= ub)%Z) : 
  (forall b : Z * list Byte.byte,
        (fun z : Z * list Byte.byte =>
         (fun z0 : Z => (lb <= z0 <= ub)%Z) (fst z) /\
         (fun (n : Z) (la : list Byte.byte) =>
          ListFormat.list_and (fun _ : Byte.byte => True) la /\
          length la = Z.to_nat n) (fst z) (snd z)) b ->
        (fun bs : list Byte.byte => (lb <= Z.of_nat (length bs) <= ub)%Z)
          ((fun z : Z * list Byte.byte => snd z) b) /\
        (fun bs : list Byte.byte => (Z.of_nat (length bs), bs))
          ((fun z : Z * list Byte.byte => snd z) b) = b).
Proof.
  intros. destruct b. simpl in *. tact.split_and. rewrite H2.
  rewrite Znat.Z2Nat.id; try Lia.lia. 
  repeat split; auto.
Qed.
  
Definition octet_string_ranged_format (lb ub : Z) (pf : (0 <= lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat(ub - lb)) <= INT_MAX_LEN ) :=
  proj_format
    (fun bs => (lb <= Z.of_nat (length bs) <= ub)%Z)
  (sigma_format
    (ranged_int_format lb ub (proj2 pf) pf2)
    _
    (fun n => byte_list_format (Z.to_nat n)))
  (fun bs => (Z.of_nat (length bs), bs))
  (fun z => snd z)
  (os_ranged_helper1 lb ub)
  (os_ranged_helper2 lb ub pf)
  (fun bs => sumbool_and1 (ZArith_dec.Z_le_dec lb (Z.of_nat (length bs))) (ZArith_dec.Z_le_dec (Z.of_nat (length bs)) ub)).


Lemma os_fixed_helper n : (forall a : list Byte.byte,
        (fun bs : list Byte.byte => Z.of_nat (length bs) = n) a ->
        (fun la : list Byte.byte =>
         ListFormat.list_and (fun _ : Byte.byte => True) la /\ length la = Z.to_nat n) a).
Proof.
  intros. simpl in *. split; auto. apply list_true.
  rewrite <- H. rewrite Znat.Nat2Z.id. auto. 
Qed.

Definition octet_string_fixed_format (n : Z) :=
  restrict_format
    (fun bs => Z.of_nat (length bs) = n)
    (byte_list_format (Z.to_nat n))
    (os_fixed_helper n)
    (fun bs => Z.eq_dec (Z.of_nat (length bs)) n).
