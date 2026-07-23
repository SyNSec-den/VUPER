Require Import   
          Lia
          ASN1Parser.Formats.Comb
          ASN1Parser.Formats.CombFormat.
 
(* Here, we will have the encoding of 'non-negative' integers, 
   they will be represented as 'nat' in Coq, and extracted 
   to 'int' in OCaml.
 *)

(* This function turns a range from a to b into the number of bits 
   range = b - a + 1 (if b < a, then it is bad we output 0)
   if 2^m < range <= 2^{m+1} then sz = m + 1
 *)
Definition to_bit_sz (n : nat) : nat :=
   Nat.log2 (n) + 1.

(* First we have a simple nat format from that has range 
   [0..n]. Note that they are closed brackets. 
 *)

Lemma nat_le (n : nat) :
  (forall a : nat, a <= n -> a < Nat.pow 2 (to_bit_sz n)).
Proof.
  intros. unfold to_bit_sz.
  destruct n eqn:E.
  - simpl. lia.
  - rewrite PeanoNat.Nat.add_1_r. 
    assert (G := proj2 (PeanoNat.Nat.log2_spec (S n0)
                          (PeanoNat.Nat.lt_0_succ n0))).
    eapply PeanoNat.Nat.le_lt_trans; eauto.
Qed.

Definition nat_format (n : nat) (pf : to_bit_sz n <= INT_MAX_LEN) :
  T_Format nat (fun z => z <= n) := restrict_format
        (fun z => z <= n)
        (basic_n_bit_format (to_bit_sz n) pf)
        (nat_le n)
        (fun a => Compare_dec.le_dec a n).

Require Import ASN1Parser.Formats.Term.Unit.

Lemma nat_enum_helper1 : (forall a : nat, a <= 0 -> True /\ 0 = a).
Proof.  intros. split; auto.   lia.
Qed.

Lemma nat_enum_helper2 : (forall b : unit, True -> 0 <= 0 /\ tt = b).
Proof. intros. destruct b.  split; auto. Qed.

Definition nat_enum_format (n : nat) (pf : to_bit_sz n <= INT_MAX_LEN) :
  T_Format nat (fun z => z <= n).
  destruct n.
  - apply (proj_format
             (fun z => z <= 0)
             unit_format
             (fun _ => tt)
             (fun _ => 0)
             nat_enum_helper1
             nat_enum_helper2
             (fun z => Compare_dec.le_dec z 0)).
  - apply (nat_format (S n) pf). 
Defined.

Require Import ASN1Parser.tact.

Lemma nat_format_SameVer (n : nat) (pf : to_bit_sz n <= INT_MAX_LEN) : 
  forall  a bf pos pos' flg,
    (T_Parse _ _  (nat_format n pf)) bf pos = Some (a, pos', flg)
    -> flg = SameVer.
Proof.
  intros. simpl in H. unfold restrict_parse in H.
  destruct_enc. destruct_match_dec_new. inversion H. subst. 
  apply ByteBufferProp.BPP.read_n_nat_SameVer in E.
  subst. reflexivity.
Qed.
  
Definition nat_range_helper1 (lb ub : nat)
  : (forall a : nat, lb <= a <= ub -> a - lb <= ub - lb /\ a - lb + lb = a) .
Proof. intros.  split; lia. Qed.

Definition nat_range_helper2 (lb ub : nat) (pf : lb <= ub)
  : (forall a' : nat,
        a' <= ub - lb -> lb <= a' + lb <= ub /\ a' + lb - lb = a').
Proof. intros. split; try lia. Qed.

(* We should add nat-range-format as well for the convinence of 
   length determinants. 
 *)
Definition nat_range_format (lb ub : nat) (pf : (lb <= ub))
  (pf2 : to_bit_sz ((ub - lb)) <= INT_MAX_LEN )
  : T_Format nat (fun z => lb <= z <= ub) :=
  proj_format
    (fun z => lb <= z <= ub)
    (nat_format (ub - lb) pf2)
    (fun z => z - lb)
    (fun z => z + lb)
    (nat_range_helper1 lb ub)
    (nat_range_helper2 lb ub pf)
    (fun a => sumbool_and1
                (Compare_dec.le_dec lb a)
                (Compare_dec.le_dec a ub)).


Lemma nat_range_format_SameVer (lb ub : nat) (pf : lb <= ub)
  (pf2 : to_bit_sz ((ub - lb)) <= INT_MAX_LEN ) :
  forall  a bf pos pos' flg,
    (T_Parse _ _  (nat_range_format lb ub pf pf2)) bf pos = Some (a, pos', flg)
    -> flg = SameVer.
Proof.
  intros. simpl in H.
  unfold proj_parse, restrict_parse in H.
  repeat destruct_enc.
  destruct_match_dec_new. inversion E. inversion H.
  subst. apply ByteBufferProp.BPP.read_n_nat_SameVer in E0.
  subst. reflexivity. 
Qed.

Definition small_integer_helper : 7 <= INT_MAX_LEN.
  unfold INT_MAX_LEN. Lia.lia. Qed.

Lemma small_integer_helper1 :
  (forall a : nat,
      (fun n : nat => n <= 63) a -> (fun z : nat => z < Nat.pow 2 7) a).
Proof. intros. simpl in *. Lia.lia. Qed.

Definition small_integer_format :=
  restrict_format
    (fun n => n <= 63)
    (basic_n_bit_format 7 small_integer_helper)
    small_integer_helper1
    (fun n => Compare_dec.le_dec n 63).
