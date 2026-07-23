Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.SuccessHO_Report_r17.

Opaque SuccessHO_Report_r17__cond SuccessHO_Report_r17__Format.

Require Import NR.PLMN_IdentityList2_r16.

Opaque PLMN_IdentityList2_r16__cond PLMN_IdentityList2_r16__Format.

Record VarSuccessHO_Report_r17_IEs__Type : Set :=
  make__VarSuccessHO_Report_r17_IEs__Type {
    VarSuccessHO_Report_r17_IEs__successHO_Report_r17 : SuccessHO_Report_r17__Type ;
    VarSuccessHO_Report_r17_IEs__plmn_IdentityList_r17 : PLMN_IdentityList2_r16__Type ;
}.
Definition VarSuccessHO_Report_r17_IEs__list := (
 Nor SuccessHO_Report_r17__Type SuccessHO_Report_r17__cond ::
 Nor PLMN_IdentityList2_r16__Type PLMN_IdentityList2_r16__cond ::
 nil).
Definition VarSuccessHO_Report_r17_IEs__cond z := 
  SuccessHO_Report_r17__cond (VarSuccessHO_Report_r17_IEs__successHO_Report_r17 z) /\
  PLMN_IdentityList2_r16__cond (VarSuccessHO_Report_r17_IEs__plmn_IdentityList_r17 z) /\
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

Definition VarSuccessHO_Report_r17_IEs__Format_Type := Eval cbn in seq_format_prod VarSuccessHO_Report_r17_IEs__list.
Definition VarSuccessHO_Report_r17_IEs__Format_list : VarSuccessHO_Report_r17_IEs__Format_Type :=
  (SuccessHO_Report_r17__Format, (PLMN_IdentityList2_r16__Format, unit_format)).
Definition VarSuccessHO_Report_r17_IEs__list__Format := (*Eval compute in *) seq_format VarSuccessHO_Report_r17_IEs__list VarSuccessHO_Report_r17_IEs__Format_list.
Definition VarSuccessHO_Report_r17_IEs__F1 z :=
  (VarSuccessHO_Report_r17_IEs__successHO_Report_r17 z, (VarSuccessHO_Report_r17_IEs__plmn_IdentityList_r17 z, tt)).
Definition VarSuccessHO_Report_r17_IEs__F2 (y : seq_type VarSuccessHO_Report_r17_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__VarSuccessHO_Report_r17_IEs__Type i0 i1
  end.
Lemma VarSuccessHO_Report_r17_IEs__F1F2_cond (z : VarSuccessHO_Report_r17_IEs__Type)
  : VarSuccessHO_Report_r17_IEs__cond z ->
  (seq_cond VarSuccessHO_Report_r17_IEs__list (VarSuccessHO_Report_r17_IEs__F1 z)).
intro H. unfold VarSuccessHO_Report_r17_IEs__cond in H. simpl. auto. Qed.
Lemma VarSuccessHO_Report_r17_IEs__F1F2_cond2 (z : VarSuccessHO_Report_r17_IEs__Type)
 : VarSuccessHO_Report_r17_IEs__F2 (VarSuccessHO_Report_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarSuccessHO_Report_r17_IEs__F2F1_cond (y : seq_type VarSuccessHO_Report_r17_IEs__list)
  : seq_cond VarSuccessHO_Report_r17_IEs__list y ->
 (VarSuccessHO_Report_r17_IEs__cond (VarSuccessHO_Report_r17_IEs__F2 y)) /\  VarSuccessHO_Report_r17_IEs__F1 (VarSuccessHO_Report_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarSuccessHO_Report_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold VarSuccessHO_Report_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarSuccessHO_Report_r17_IEs__Format : T_Format VarSuccessHO_Report_r17_IEs__Type VarSuccessHO_Report_r17_IEs__cond :=
        proj2_format  VarSuccessHO_Report_r17_IEs__cond VarSuccessHO_Report_r17_IEs__list__Format
    VarSuccessHO_Report_r17_IEs__F1 VarSuccessHO_Report_r17_IEs__F2 VarSuccessHO_Report_r17_IEs__F1F2_cond  VarSuccessHO_Report_r17_IEs__F1F2_cond2 VarSuccessHO_Report_r17_IEs__F2F1_cond.
Opaque VarSuccessHO_Report_r17_IEs__cond VarSuccessHO_Report_r17_IEs__Format.

