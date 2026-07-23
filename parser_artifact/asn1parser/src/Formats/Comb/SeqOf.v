Require Import
  BinInt
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Formats.Term.LengthDet
  ASN1Parser.Formats.Term.NonNeg
  ASN1Parser.Formats.Term.BitString
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.ListFormat
  ASN1Parser.Formats.Comb.ListFormatProp.


(* For sequence-of the problem is that there are several 
   different combinations.

   We will define all situations.
 *)


(* 1. For fixed size sequence-of, there is nothing 
      to it. It is exactly the same as list_comb 
 *)

(* 2. For Constrained, the length is encoded in a 
      nat_ranged. 
 *)

(* Now for convinence reason, we only consider the
   cons_size, with both upper bound and lower bound
 *)
Require Import  ASN1Parser.tact.

Lemma seq_of_helper1 A P lb ub :
   (forall a : list A,
        (fun bs : list A => (lb <= Z.of_nat (length bs) <= ub)%Z /\ list_and P bs)
          a ->
        (fun z : nat * list A =>
         (fun n : nat => (lb <= Z.of_nat n <= ub)%Z) (fst z) /\
         (fun (n : nat) (la : list A) => list_and P la /\ length la = n) 
           (fst z) (snd z)) ((fun bs : list A => (length bs, bs)) a)).
  intros. simpl in *. split_and.   repeat (split; auto).
Qed.

Lemma seq_of_helper2 A :
  (forall a : list A,
        (fun z : nat * list A => snd z) ((fun bs : list A => (length bs, bs)) a) =
        a).
Proof. intros.  simpl.  auto. Qed.

Lemma seq_of_helper3 A P lb ub :
  (forall b : nat * list A,
        (fun z : nat * list A =>
         (fun n : nat => (lb <= Z.of_nat n <= ub)%Z) (fst z) /\
         (fun (n : nat) (la : list A) => list_and P la /\ length la = n) 
           (fst z) (snd z)) b ->
        (fun bs : list A => (lb <= Z.of_nat (length bs) <= ub)%Z /\ list_and P bs)
          ((fun z : nat * list A => snd z) b) /\
        (fun bs : list A => (length bs, bs)) ((fun z : nat * list A => snd z) b) =
        b).
  intros. destruct b.  simpl in *.  split_and.  subst.  repeat (split; auto).
Qed.


Definition seq_of_format
  {A : Set} {P : A -> Prop}
  (fmt : T_Format A P)
  (lb ub : Z)
  (pf1 : (0 <= lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)) <= INT_MAX_LEN) :=
  proj2_format
    (fun bs => (lb <= Z.of_nat (length bs) <= ub)%Z /\ list_and P bs)
    (sigma_format
       (ranged_nat_format lb ub pf1 pf2)
       _
       (fun n => list_format fmt n))
    (fun bs => (length bs, bs))
    (fun z => snd z)
    (seq_of_helper1 A P lb ub)
    (seq_of_helper2 A)
    (seq_of_helper3 A P lb ub).

(* A generalized form of seq-of, where we have a length + value, 
   but only the value is provided here. Can be generalized to octet string
   and possibly bit string
 *)
Lemma len_val_helper1  {A : Set} {P : A -> Prop}  {P_len : nat -> Prop} : 
  (forall a : list A,
        (fun la : list A => P_len (length la) /\ list_and P la) a ->
        (fun z : nat * list A =>
         P_len (fst z) /\
         (fun (n : nat) (la : list A) => list_and P la /\ length la = n) (fst z) (snd z))
          ((fun bs : list A => (length bs, bs)) a)).
Proof.
  intros. simpl in *.
  split_and. 
  repeat split; auto.
Qed.

Lemma len_val_helper2  {A : Set}  :
  (forall a : list A,
        (fun z : nat * list A => snd z) ((fun bs : list A => (length bs, bs)) a) = a).
Proof.
  intros. simpl in *. auto. 
Qed.

Lemma len_val_helper3 {A : Set} {P : A -> Prop}
  {P_len : nat -> Prop} :
  (forall b : nat * list A,
        (fun z : nat * list A =>
         P_len (fst z) /\
         (fun (n : nat) (la : list A) => list_and P la /\ length la = n) (fst z) (snd z)) b ->
        (fun la : list A => P_len (length la) /\ list_and P la)
          ((fun z : nat * list A => snd z) b) /\
          (fun bs : list A => (length bs, bs)) ((fun z : nat * list A => snd z) b) = b).
Proof.
  intros.  simpl in *.  split_and.
  destruct b.  simpl in *. subst.  split; auto. Qed.
  
Definition length_value_format
  {A : Set} {P : A -> Prop}
  {P_len : nat -> Prop}
  (fmt : T_Format A P)
  (len_fmt : T_Format nat P_len)
  :=
  proj2_format
    (fun la : list A => P_len (length la) /\ list_and P la) 
    (sigma_format
       len_fmt
       _
       (fun n => list_format fmt n))
    (fun bs => (length bs, bs))
    (fun z => snd z)
    len_val_helper1
    len_val_helper2
    len_val_helper3.


(* Fixed length  *)
Definition seq_of_fixed_format
  {A : Set} {P : A -> Prop}
  (fmt : T_Format A P) (n : Z) :=
  list_format fmt (Z.to_nat n).

(* Reason for using Z: ub, lb can be very large, thus making compiling to OCaml 
   almost impossible. Here since in our case, the test cases in 
   ITS (so is J2735) format is not very large, we ignore it.
 *)
Definition seq_of_ext_format
  {A : Set} {P : A -> Prop}
  (fmt : T_Format A P)
  (lb ub : nat)
  (pf1 : (lb <= ub))
  (pf2 : to_bit_sz ( (ub - lb)) <= INT_MAX_LEN) :=
  length_value_format
    fmt
    (len_det_ranged_ext lb ub pf1 pf2)
.
