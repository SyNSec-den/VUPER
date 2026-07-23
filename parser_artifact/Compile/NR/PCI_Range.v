Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Inductive PCI_Range__range__Type : Set :=
 | PCI_Range__range__n4
 | PCI_Range__range__n8
 | PCI_Range__range__n12
 | PCI_Range__range__n16
 | PCI_Range__range__n24
 | PCI_Range__range__n32
 | PCI_Range__range__n48
 | PCI_Range__range__n64
 | PCI_Range__range__n84
 | PCI_Range__range__n96
 | PCI_Range__range__n128
 | PCI_Range__range__n168
 | PCI_Range__range__n252
 | PCI_Range__range__n504
 | PCI_Range__range__n1008
 | PCI_Range__range__spare1
.
Definition PCI_Range__range__cond := (fun (_ : PCI_Range__range__Type) => True).
Lemma PCI_Range__range__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PCI_Range__range__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PCI_Range__range__nat__helper.

Definition PCI_Range__range__F1 t :=
  match t with
  | PCI_Range__range__n4 => 0
  | PCI_Range__range__n8 => 1
  | PCI_Range__range__n12 => 2
  | PCI_Range__range__n16 => 3
  | PCI_Range__range__n24 => 4
  | PCI_Range__range__n32 => 5
  | PCI_Range__range__n48 => 6
  | PCI_Range__range__n64 => 7
  | PCI_Range__range__n84 => 8
  | PCI_Range__range__n96 => 9
  | PCI_Range__range__n128 => 10
  | PCI_Range__range__n168 => 11
  | PCI_Range__range__n252 => 12
  | PCI_Range__range__n504 => 13
  | PCI_Range__range__n1008 => 14
  | PCI_Range__range__spare1 => 15
  end.
Definition PCI_Range__range__F2 n :=
  match n with
  | 0 => PCI_Range__range__n4
  | 1 => PCI_Range__range__n8
  | 2 => PCI_Range__range__n12
  | 3 => PCI_Range__range__n16
  | 4 => PCI_Range__range__n24
  | 5 => PCI_Range__range__n32
  | 6 => PCI_Range__range__n48
  | 7 => PCI_Range__range__n64
  | 8 => PCI_Range__range__n84
  | 9 => PCI_Range__range__n96
  | 10 => PCI_Range__range__n128
  | 11 => PCI_Range__range__n168
  | 12 => PCI_Range__range__n252
  | 13 => PCI_Range__range__n504
  | 14 => PCI_Range__range__n1008
  | 15 => PCI_Range__range__spare1
  | _ => PCI_Range__range__n4
  end.
Lemma PCI_Range__range__F1F2 : forall x : PCI_Range__range__Type, (PCI_Range__range__F1 x <= 15) /\ PCI_Range__range__F2 (PCI_Range__range__F1 x) = x. imp_solve. Qed.
Lemma PCI_Range__range__F2F1 : forall (y : nat) (H : y <= 15), PCI_Range__range__F1 (PCI_Range__range__F2 y) = y. enum_solve H y. Qed.

Record PCI_Range__Type : Set :=
  make__PCI_Range__Type {
    PCI_Range__start : PhysCellId__Type ;
    PCI_Range__range : option PCI_Range__range__Type ;
}.
Definition PCI_Range__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Opt PCI_Range__range__Type PCI_Range__range__cond ::
 nil).
Definition PCI_Range__cond z := 
  PhysCellId__cond (PCI_Range__start z) /\
  opt_cond PCI_Range__range__cond (PCI_Range__range z) /\
  True.


Opaque Byte.to_nat Byte.of_nat.
Opaque bind_parse restrict_parse proj_parse return_parse.
Opaque restrict_serialize proj_serialize sigma_serialize append_serialize proj2_serialize.

Opaque read_n_nat read_unit.
Opaque put_n_nat put_unit. 

Opaque opt_bind opt_serialize dft_serialize prepend_serialize list_serial.
Opaque opt_parse list_parse dft_parse fail_parse append_parse
  bind_parse return_parse.

Opaque Z.to_nat Z.of_nat Z.sub Z.add Z.le Z.lt Z.pow Z.opp Z.ltb.
Opaque Nat.mul Nat.shiftr Nat.shiftl Nat.div Nat.modulo Nat.leb Nat.ltb Nat.add
  Nat.sub Nat.land Nat.lor Nat.eqb  Nat.log2 Nat.pow Nat.even PeanoNat.Nat.lnot.
Opaque Compare_dec.le_dec Compare_dec.le_lt_dec ZArith_dec.Z_le_dec lt_eq_lt_dec_new. 
Opaque sumbool_and1 list_and list_and_cons list_cons_S flg_add. 

Opaque list_to_len.
   Opaque length Compare_dec.le_dec Compare_dec.lt_dec PeanoNat.Nat.eq_dec.
   Opaque bool__Format int__Format octet_string_nc__Format bit_string_nc__Format.

   Opaque ByteIdx_to_nat nat_to_ByteIdx add_opt list_bool_format normally_small_len_det_format
  get_byte_len to_parse_skip  open_typ_serialize open_typ_parse open_type_to_len.
  

Opaque seq_cond seq_ext_cond choice_cond.
Definition PCI_Range__range__Format : T_Format PCI_Range__range__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PCI_Range__range__nat__Format PCI_Range__range__F1 PCI_Range__range__F2 PCI_Range__range__F1F2 PCI_Range__range__F2F1.

Opaque PCI_Range__range__cond PCI_Range__range__Format.


Definition PCI_Range__Format_Type := Eval cbn in seq_format_prod PCI_Range__list.
Definition PCI_Range__Format_list : PCI_Range__Format_Type :=
  (PhysCellId__Format, (PCI_Range__range__Format, unit_format)).
Definition PCI_Range__list__Format := (*Eval compute in *) seq_format PCI_Range__list PCI_Range__Format_list.
Definition PCI_Range__F1 z :=
  (PCI_Range__start z, (PCI_Range__range z, tt)).
Definition PCI_Range__F2 (y : seq_type PCI_Range__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PCI_Range__Type i0 i1
  end.
Lemma PCI_Range__F1F2_cond (z : PCI_Range__Type)
  : PCI_Range__cond z ->
  (seq_cond PCI_Range__list (PCI_Range__F1 z)).
intro H. unfold PCI_Range__cond in H. simpl. auto. Qed.
Lemma PCI_Range__F1F2_cond2 (z : PCI_Range__Type)
 : PCI_Range__F2 (PCI_Range__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PCI_Range__F2F1_cond (y : seq_type PCI_Range__list)
  : seq_cond PCI_Range__list y ->
 (PCI_Range__cond (PCI_Range__F2 y)) /\  PCI_Range__F1 (PCI_Range__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PCI_Range__cond. simpl in *. auto.
 - simpl. unfold PCI_Range__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PCI_Range__Format : T_Format PCI_Range__Type PCI_Range__cond :=
        proj2_format  PCI_Range__cond PCI_Range__list__Format
    PCI_Range__F1 PCI_Range__F2 PCI_Range__F1F2_cond  PCI_Range__F1F2_cond2 PCI_Range__F2F1_cond.
Opaque PCI_Range__cond PCI_Range__Format.

