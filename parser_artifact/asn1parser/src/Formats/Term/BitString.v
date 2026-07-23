Require Import
  Lia
  BinInt
  Coq.Strings.Byte
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.LengthDet
  ASN1Parser.Formats.Term.NonNeg
  ASN1Parser.Formats.Term.Integer
  ASN1Parser.Formats.Term.ByteList
  ASN1Parser.Formats.Term.OctetString
  ASN1Parser.tact.

(* We could follow the pycrate or the ASN1C version. 
   
   In pycrate, the idea is that the things to encode is rep as
   a tuple of (n, m). Here, we encode n into m bits. If, 
   however n >= 2^m, it would just encode 2^m - 1. 

   Here, it is better to use the notation in ASN1c. That is 
   use a tuple of (list byte, tail, total_length).

   Here, tail is the remaining bits, 0-7 bits, total_length
   is the total length of the encoding. 
         
   Potential problem, the last few bits shall be 0 (unfilled) 
   in order that the proofs of correctness would be correct. 
   
   Or we can represent it in a list of bytes (initial)
   and a number between 0 and 255 which represents the last
   byte.

   So it is easier to encode and decode.
   First encode the byte list then encode the integer.
 *)
Definition bit_string := (nat * ((list byte) * nat)) %type.

Definition bit_string_fixed := (nat * ((list byte) * nat)) %type. 

Definition get_list_len (n : nat) :=
  Nat.div n 8.

Definition get_tail_len (n : nat) :=
  Nat.modulo n 8. 

Lemma tail_len_le_max n : get_tail_len n <= INT_MAX_LEN.
Proof.
  unfold get_tail_len, INT_MAX_LEN.
  assert (8 <> 0). { lia. }
  assert (G := PeanoNat.Nat.mod_upper_bound n 8 H). 
  lia. 
Qed.

Definition bit_string_len_prop (n : nat) (z : list byte * nat) : Prop :=
  let (bs, tail) := z in 
  length bs = get_list_len n /\ tail < Nat.pow 2 (get_tail_len n).

Lemma bit_string_helper n :
  (forall a : list byte * nat,
      bit_string_len_prop n a ->
      (fun z : list byte * nat =>
         (fun l : list byte =>
            ListFormat.list_and (fun _ : byte => True) l /\ length l = get_list_len n)
           (fst z) /\ (fun z0 : nat => z0 < Nat.pow 2 (get_tail_len n)) (snd z)) a).
Proof.
  intros. destruct a.  simpl in *. split_and. repeat split; auto. 
  apply list_true.
Qed.

Definition bit_string_len_prop_dec n :
  (forall a : list byte * nat,
      {bit_string_len_prop n a} + {~ bit_string_len_prop n a}).
  intro. destruct a. 
  unfold bit_string_len_prop. apply sumbool_and1.
  - apply PeanoNat.Nat.eq_dec.
  - apply Compare_dec.lt_dec.
Defined.


Definition bit_string_format (n : nat) :=
  restrict_format
    (bit_string_len_prop n)
    (append_format
       (byte_list_format (get_list_len n))
       (basic_n_bit_format (get_tail_len n) (tail_len_le_max n)))
    (bit_string_helper n)
    (bit_string_len_prop_dec n).

Definition bit_string_nc_cond :=
  (fun z : bit_string =>
          ((fst z) < Nat.pow 2 14) /\
          bit_string_len_prop (fst z) (snd z)).

Definition bit_string_no_cons_format : T_Format bit_string bit_string_nc_cond :=
  (sigma_format
     uncons_len_det_format
     _
     (fun n => bit_string_format n)).

Lemma ranged_nat_helper1 lb ub  (pf : (0 <= lb <= ub)%Z) :
 forall a : nat, (lb <= Z.of_nat a <= ub)%Z -> (lb <= Z.of_nat a <= ub)%Z /\ Z.to_nat (Z.of_nat a) = a.
Proof.
  intros. simpl in *.  split; try lia.
Qed.

Lemma ranged_nat_helper2 lb ub (pf : (0 <= lb <= ub)%Z) :
  forall b : Z, (lb <= b <= ub)%Z -> (lb <= Z.of_nat (Z.to_nat b) <= ub)%Z /\ Z.of_nat (Z.to_nat b) = b. 
Proof.
  intros. simpl in *.  split; try lia. 
Qed.

Definition ranged_nat_format  lb ub (pf : (0 <= lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)) <= INT_MAX_LEN ) :=
  proj_format
    (fun n => (lb <= Z.of_nat n <= ub)%Z)
    (ranged_int_format lb ub (proj2 pf) pf2)
    (Z.of_nat)
    (Z.to_nat)
    (ranged_nat_helper1 lb ub pf)
    (ranged_nat_helper2 lb ub pf)
    (fun n => sumbool_and1 (ZArith_dec.Z_le_dec lb (Z.of_nat n))
                (ZArith_dec.Z_le_dec (Z.of_nat n) ub)).

Definition bit_string_ranged_format lb ub (pf : (0 <= lb <= ub)%Z)
  (pf2 : to_bit_sz (Z.to_nat (ub - lb)) <= INT_MAX_LEN ) :=
  (sigma_format
     (ranged_nat_format lb ub pf pf2)
     _
     (fun n => bit_string_format n)).

Lemma fix_nat_helper1 n : (forall a : nat, a = n -> True /\ n = a) .
Proof. intros. split; auto. Qed.

Lemma fix_nat_helper2 (n : nat) : (forall a' : unit, True -> n = n /\ tt = a').
Proof. intros. destruct a'. split; auto. Qed.

Require Import ASN1Parser.Formats.Term.Unit.

Definition fixed_nat_format (n : nat) : T_Format nat (fun z : nat => z = n) :=
  proj_format
    (fun z => z = n)
    unit_format
    (fun _ => tt)
    (fun _ => n)
    (fix_nat_helper1 n)
    (fix_nat_helper2 n)
    (fun z => PeanoNat.Nat.eq_dec z n).

Definition bit_string_fixed_format (n : Z) :=
   (sigma_format
     (fixed_nat_format (Z.to_nat n))
     _
     (fun n => bit_string_format n)). 


(* Another way to represent bit string is to simply use
   a list of bool. 

   We only consider the case where the length is fixed
 *)
(*Fixpoint bl_to_bs (bl : list bool) : bit_string :=
  let len := length bl in
  if (Nat.leb len 7)
  then (0, (nil, 10))
  else

Definition bool_list_format (n : nat) :=
  Proj
    (fun bl : list bool => length bl = n)
    (bit_string_fixed_format n). *)
