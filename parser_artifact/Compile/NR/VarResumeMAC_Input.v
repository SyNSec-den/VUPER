Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.CellIdentity.

Opaque CellIdentity__cond CellIdentity__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Record VarResumeMAC_Input__Type : Set :=
  make__VarResumeMAC_Input__Type {
    VarResumeMAC_Input__sourcePhysCellId : PhysCellId__Type ;
    VarResumeMAC_Input__targetCellIdentity : CellIdentity__Type ;
    VarResumeMAC_Input__source_c_RNTI : RNTI_Value__Type ;
}.
Definition VarResumeMAC_Input__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor CellIdentity__Type CellIdentity__cond ::
 Nor RNTI_Value__Type RNTI_Value__cond ::
 nil).
Definition VarResumeMAC_Input__cond z := 
  PhysCellId__cond (VarResumeMAC_Input__sourcePhysCellId z) /\
  CellIdentity__cond (VarResumeMAC_Input__targetCellIdentity z) /\
  RNTI_Value__cond (VarResumeMAC_Input__source_c_RNTI z) /\
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

Definition VarResumeMAC_Input__Format_Type := Eval cbn in seq_format_prod VarResumeMAC_Input__list.
Definition VarResumeMAC_Input__Format_list : VarResumeMAC_Input__Format_Type :=
  (PhysCellId__Format, (CellIdentity__Format, (RNTI_Value__Format, unit_format))).
Definition VarResumeMAC_Input__list__Format := (*Eval compute in *) seq_format VarResumeMAC_Input__list VarResumeMAC_Input__Format_list.
Definition VarResumeMAC_Input__F1 z :=
  (VarResumeMAC_Input__sourcePhysCellId z, (VarResumeMAC_Input__targetCellIdentity z, (VarResumeMAC_Input__source_c_RNTI z, tt))).
Definition VarResumeMAC_Input__F2 (y : seq_type VarResumeMAC_Input__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__VarResumeMAC_Input__Type i0 i1 i2
  end.
Lemma VarResumeMAC_Input__F1F2_cond (z : VarResumeMAC_Input__Type)
  : VarResumeMAC_Input__cond z ->
  (seq_cond VarResumeMAC_Input__list (VarResumeMAC_Input__F1 z)).
intro H. unfold VarResumeMAC_Input__cond in H. simpl. auto. Qed.
Lemma VarResumeMAC_Input__F1F2_cond2 (z : VarResumeMAC_Input__Type)
 : VarResumeMAC_Input__F2 (VarResumeMAC_Input__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarResumeMAC_Input__F2F1_cond (y : seq_type VarResumeMAC_Input__list)
  : seq_cond VarResumeMAC_Input__list y ->
 (VarResumeMAC_Input__cond (VarResumeMAC_Input__F2 y)) /\  VarResumeMAC_Input__F1 (VarResumeMAC_Input__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarResumeMAC_Input__cond. simpl in *. auto.
 - simpl. unfold VarResumeMAC_Input__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarResumeMAC_Input__Format : T_Format VarResumeMAC_Input__Type VarResumeMAC_Input__cond :=
        proj2_format  VarResumeMAC_Input__cond VarResumeMAC_Input__list__Format
    VarResumeMAC_Input__F1 VarResumeMAC_Input__F2 VarResumeMAC_Input__F1F2_cond  VarResumeMAC_Input__F1F2_cond2 VarResumeMAC_Input__F2F1_cond.
Opaque VarResumeMAC_Input__cond VarResumeMAC_Input__Format.

