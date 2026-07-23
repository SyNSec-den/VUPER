Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Inductive EUTRA_PhysCellIdRange__range__Type : Set :=
 | EUTRA_PhysCellIdRange__range__n4
 | EUTRA_PhysCellIdRange__range__n8
 | EUTRA_PhysCellIdRange__range__n12
 | EUTRA_PhysCellIdRange__range__n16
 | EUTRA_PhysCellIdRange__range__n24
 | EUTRA_PhysCellIdRange__range__n32
 | EUTRA_PhysCellIdRange__range__n48
 | EUTRA_PhysCellIdRange__range__n64
 | EUTRA_PhysCellIdRange__range__n84
 | EUTRA_PhysCellIdRange__range__n96
 | EUTRA_PhysCellIdRange__range__n128
 | EUTRA_PhysCellIdRange__range__n168
 | EUTRA_PhysCellIdRange__range__n252
 | EUTRA_PhysCellIdRange__range__n504
 | EUTRA_PhysCellIdRange__range__spare2
 | EUTRA_PhysCellIdRange__range__spare1
.
Definition EUTRA_PhysCellIdRange__range__cond := (fun (_ : EUTRA_PhysCellIdRange__range__Type) => True).
Lemma EUTRA_PhysCellIdRange__range__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_PhysCellIdRange__range__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 EUTRA_PhysCellIdRange__range__nat__helper.

Definition EUTRA_PhysCellIdRange__range__F1 t :=
  match t with
  | EUTRA_PhysCellIdRange__range__n4 => 0
  | EUTRA_PhysCellIdRange__range__n8 => 1
  | EUTRA_PhysCellIdRange__range__n12 => 2
  | EUTRA_PhysCellIdRange__range__n16 => 3
  | EUTRA_PhysCellIdRange__range__n24 => 4
  | EUTRA_PhysCellIdRange__range__n32 => 5
  | EUTRA_PhysCellIdRange__range__n48 => 6
  | EUTRA_PhysCellIdRange__range__n64 => 7
  | EUTRA_PhysCellIdRange__range__n84 => 8
  | EUTRA_PhysCellIdRange__range__n96 => 9
  | EUTRA_PhysCellIdRange__range__n128 => 10
  | EUTRA_PhysCellIdRange__range__n168 => 11
  | EUTRA_PhysCellIdRange__range__n252 => 12
  | EUTRA_PhysCellIdRange__range__n504 => 13
  | EUTRA_PhysCellIdRange__range__spare2 => 14
  | EUTRA_PhysCellIdRange__range__spare1 => 15
  end.
Definition EUTRA_PhysCellIdRange__range__F2 n :=
  match n with
  | 0 => EUTRA_PhysCellIdRange__range__n4
  | 1 => EUTRA_PhysCellIdRange__range__n8
  | 2 => EUTRA_PhysCellIdRange__range__n12
  | 3 => EUTRA_PhysCellIdRange__range__n16
  | 4 => EUTRA_PhysCellIdRange__range__n24
  | 5 => EUTRA_PhysCellIdRange__range__n32
  | 6 => EUTRA_PhysCellIdRange__range__n48
  | 7 => EUTRA_PhysCellIdRange__range__n64
  | 8 => EUTRA_PhysCellIdRange__range__n84
  | 9 => EUTRA_PhysCellIdRange__range__n96
  | 10 => EUTRA_PhysCellIdRange__range__n128
  | 11 => EUTRA_PhysCellIdRange__range__n168
  | 12 => EUTRA_PhysCellIdRange__range__n252
  | 13 => EUTRA_PhysCellIdRange__range__n504
  | 14 => EUTRA_PhysCellIdRange__range__spare2
  | 15 => EUTRA_PhysCellIdRange__range__spare1
  | _ => EUTRA_PhysCellIdRange__range__n4
  end.
Lemma EUTRA_PhysCellIdRange__range__F1F2 : forall x : EUTRA_PhysCellIdRange__range__Type, (EUTRA_PhysCellIdRange__range__F1 x <= 15) /\ EUTRA_PhysCellIdRange__range__F2 (EUTRA_PhysCellIdRange__range__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_PhysCellIdRange__range__F2F1 : forall (y : nat) (H : y <= 15), EUTRA_PhysCellIdRange__range__F1 (EUTRA_PhysCellIdRange__range__F2 y) = y. enum_solve H y. Qed.

Record EUTRA_PhysCellIdRange__Type : Set :=
  make__EUTRA_PhysCellIdRange__Type {
    EUTRA_PhysCellIdRange__start : EUTRA_PhysCellId__Type ;
    EUTRA_PhysCellIdRange__range : option EUTRA_PhysCellIdRange__range__Type ;
}.
Definition EUTRA_PhysCellIdRange__list := (
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Opt EUTRA_PhysCellIdRange__range__Type EUTRA_PhysCellIdRange__range__cond ::
 nil).
Definition EUTRA_PhysCellIdRange__cond z := 
  EUTRA_PhysCellId__cond (EUTRA_PhysCellIdRange__start z) /\
  opt_cond EUTRA_PhysCellIdRange__range__cond (EUTRA_PhysCellIdRange__range z) /\
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
Definition EUTRA_PhysCellIdRange__range__Format : T_Format EUTRA_PhysCellIdRange__range__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_PhysCellIdRange__range__nat__Format EUTRA_PhysCellIdRange__range__F1 EUTRA_PhysCellIdRange__range__F2 EUTRA_PhysCellIdRange__range__F1F2 EUTRA_PhysCellIdRange__range__F2F1.

Opaque EUTRA_PhysCellIdRange__range__cond EUTRA_PhysCellIdRange__range__Format.


Definition EUTRA_PhysCellIdRange__Format_Type := Eval cbn in seq_format_prod EUTRA_PhysCellIdRange__list.
Definition EUTRA_PhysCellIdRange__Format_list : EUTRA_PhysCellIdRange__Format_Type :=
  (EUTRA_PhysCellId__Format, (EUTRA_PhysCellIdRange__range__Format, unit_format)).
Definition EUTRA_PhysCellIdRange__list__Format := (*Eval compute in *) seq_format EUTRA_PhysCellIdRange__list EUTRA_PhysCellIdRange__Format_list.
Definition EUTRA_PhysCellIdRange__F1 z :=
  (EUTRA_PhysCellIdRange__start z, (EUTRA_PhysCellIdRange__range z, tt)).
Definition EUTRA_PhysCellIdRange__F2 (y : seq_type EUTRA_PhysCellIdRange__list) :=
  match y with
  | (i0, (i1, _))=>
    make__EUTRA_PhysCellIdRange__Type i0 i1
  end.
Lemma EUTRA_PhysCellIdRange__F1F2_cond (z : EUTRA_PhysCellIdRange__Type)
  : EUTRA_PhysCellIdRange__cond z ->
  (seq_cond EUTRA_PhysCellIdRange__list (EUTRA_PhysCellIdRange__F1 z)).
intro H. unfold EUTRA_PhysCellIdRange__cond in H. simpl. auto. Qed.
Lemma EUTRA_PhysCellIdRange__F1F2_cond2 (z : EUTRA_PhysCellIdRange__Type)
 : EUTRA_PhysCellIdRange__F2 (EUTRA_PhysCellIdRange__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EUTRA_PhysCellIdRange__F2F1_cond (y : seq_type EUTRA_PhysCellIdRange__list)
  : seq_cond EUTRA_PhysCellIdRange__list y ->
 (EUTRA_PhysCellIdRange__cond (EUTRA_PhysCellIdRange__F2 y)) /\  EUTRA_PhysCellIdRange__F1 (EUTRA_PhysCellIdRange__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EUTRA_PhysCellIdRange__cond. simpl in *. auto.
 - simpl. unfold EUTRA_PhysCellIdRange__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EUTRA_PhysCellIdRange__Format : T_Format EUTRA_PhysCellIdRange__Type EUTRA_PhysCellIdRange__cond :=
        proj2_format  EUTRA_PhysCellIdRange__cond EUTRA_PhysCellIdRange__list__Format
    EUTRA_PhysCellIdRange__F1 EUTRA_PhysCellIdRange__F2 EUTRA_PhysCellIdRange__F1F2_cond  EUTRA_PhysCellIdRange__F1F2_cond2 EUTRA_PhysCellIdRange__F2F1_cond.
Opaque EUTRA_PhysCellIdRange__cond EUTRA_PhysCellIdRange__Format.

