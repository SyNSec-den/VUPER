Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_PowerControlSetInfoId_r17.

Opaque PUCCH_PowerControlSetInfoId_r17__cond PUCCH_PowerControlSetInfoId_r17__Format.

Require Import NR.P0_PUCCH_Id.

Opaque P0_PUCCH_Id__cond P0_PUCCH_Id__Format.

Inductive PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Type : Set :=
 | PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i0
 | PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i1
.
Definition PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__cond := (fun (_ : PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Type) => True).
Lemma PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__nat__helper.

Definition PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1 t :=
  match t with
  | PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i0 => 0
  | PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i1 => 1
  end.
Definition PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F2 n :=
  match n with
  | 0 => PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i0
  | 1 => PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i1
  | _ => PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__i0
  end.
Lemma PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1F2 : forall x : PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Type, (PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1 x <= 1) /\ PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F2 (PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1 (PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_PathlossReferenceRS_Id_r17.

Opaque PUCCH_PathlossReferenceRS_Id_r17__cond PUCCH_PathlossReferenceRS_Id_r17__Format.

Record PUCCH_PowerControlSetInfo_r17__Type : Set :=
  make__PUCCH_PowerControlSetInfo_r17__Type {
    PUCCH_PowerControlSetInfo_r17__pucch_PowerControlSetInfoId_r17 : PUCCH_PowerControlSetInfoId_r17__Type ;
    PUCCH_PowerControlSetInfo_r17__p0_PUCCH_Id_r17 : P0_PUCCH_Id__Type ;
    PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17 : PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Type ;
    PUCCH_PowerControlSetInfo_r17__pucch_PathlossReferenceRS_Id_r17 : PUCCH_PathlossReferenceRS_Id_r17__Type ;
}.
Definition PUCCH_PowerControlSetInfo_r17__list := (
 Nor PUCCH_PowerControlSetInfoId_r17__Type PUCCH_PowerControlSetInfoId_r17__cond ::
 Nor P0_PUCCH_Id__Type P0_PUCCH_Id__cond ::
 Nor PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Type PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__cond ::
 Nor PUCCH_PathlossReferenceRS_Id_r17__Type PUCCH_PathlossReferenceRS_Id_r17__cond ::
 nil).
Definition PUCCH_PowerControlSetInfo_r17__cond z := 
  PUCCH_PowerControlSetInfoId_r17__cond (PUCCH_PowerControlSetInfo_r17__pucch_PowerControlSetInfoId_r17 z) /\
  P0_PUCCH_Id__cond (PUCCH_PowerControlSetInfo_r17__p0_PUCCH_Id_r17 z) /\
  PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__cond (PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17 z) /\
  PUCCH_PathlossReferenceRS_Id_r17__cond (PUCCH_PowerControlSetInfo_r17__pucch_PathlossReferenceRS_Id_r17 z) /\
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
Definition PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Format : T_Format PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__nat__Format PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1 PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F2 PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F1F2 PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__F2F1.

Opaque PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__cond PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Format.


Definition PUCCH_PowerControlSetInfo_r17__Format_Type := Eval cbn in seq_format_prod PUCCH_PowerControlSetInfo_r17__list.
Definition PUCCH_PowerControlSetInfo_r17__Format_list : PUCCH_PowerControlSetInfo_r17__Format_Type :=
  (PUCCH_PowerControlSetInfoId_r17__Format, (P0_PUCCH_Id__Format, (PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17__Format, (PUCCH_PathlossReferenceRS_Id_r17__Format, unit_format)))).
Definition PUCCH_PowerControlSetInfo_r17__list__Format := (*Eval compute in *) seq_format PUCCH_PowerControlSetInfo_r17__list PUCCH_PowerControlSetInfo_r17__Format_list.
Definition PUCCH_PowerControlSetInfo_r17__F1 z :=
  (PUCCH_PowerControlSetInfo_r17__pucch_PowerControlSetInfoId_r17 z, (PUCCH_PowerControlSetInfo_r17__p0_PUCCH_Id_r17 z, (PUCCH_PowerControlSetInfo_r17__pucch_ClosedLoopIndex_r17 z, (PUCCH_PowerControlSetInfo_r17__pucch_PathlossReferenceRS_Id_r17 z, tt)))).
Definition PUCCH_PowerControlSetInfo_r17__F2 (y : seq_type PUCCH_PowerControlSetInfo_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PUCCH_PowerControlSetInfo_r17__Type i0 i1 i2 i3
  end.
Lemma PUCCH_PowerControlSetInfo_r17__F1F2_cond (z : PUCCH_PowerControlSetInfo_r17__Type)
  : PUCCH_PowerControlSetInfo_r17__cond z ->
  (seq_cond PUCCH_PowerControlSetInfo_r17__list (PUCCH_PowerControlSetInfo_r17__F1 z)).
intro H. unfold PUCCH_PowerControlSetInfo_r17__cond in H. simpl. auto. Qed.
Lemma PUCCH_PowerControlSetInfo_r17__F1F2_cond2 (z : PUCCH_PowerControlSetInfo_r17__Type)
 : PUCCH_PowerControlSetInfo_r17__F2 (PUCCH_PowerControlSetInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_PowerControlSetInfo_r17__F2F1_cond (y : seq_type PUCCH_PowerControlSetInfo_r17__list)
  : seq_cond PUCCH_PowerControlSetInfo_r17__list y ->
 (PUCCH_PowerControlSetInfo_r17__cond (PUCCH_PowerControlSetInfo_r17__F2 y)) /\  PUCCH_PowerControlSetInfo_r17__F1 (PUCCH_PowerControlSetInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_PowerControlSetInfo_r17__cond. simpl in *. auto.
 - simpl. unfold PUCCH_PowerControlSetInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_PowerControlSetInfo_r17__Format : T_Format PUCCH_PowerControlSetInfo_r17__Type PUCCH_PowerControlSetInfo_r17__cond :=
        proj2_format  PUCCH_PowerControlSetInfo_r17__cond PUCCH_PowerControlSetInfo_r17__list__Format
    PUCCH_PowerControlSetInfo_r17__F1 PUCCH_PowerControlSetInfo_r17__F2 PUCCH_PowerControlSetInfo_r17__F1F2_cond  PUCCH_PowerControlSetInfo_r17__F1F2_cond2 PUCCH_PowerControlSetInfo_r17__F2F1_cond.
Opaque PUCCH_PowerControlSetInfo_r17__cond PUCCH_PowerControlSetInfo_r17__Format.

