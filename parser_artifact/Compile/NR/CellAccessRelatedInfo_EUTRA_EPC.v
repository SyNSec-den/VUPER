Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_IdentityList_EUTRA_EPC.

Opaque PLMN_IdentityList_EUTRA_EPC__cond PLMN_IdentityList_EUTRA_EPC__Format.

Definition CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type := bit_string_fixed.
Definition CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type := bit_string_fixed.
Definition CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 28 /\ bit_string_len_prop (fst z) (snd z)).
Record CellAccessRelatedInfo_EUTRA_EPC__Type : Set :=
  make__CellAccessRelatedInfo_EUTRA_EPC__Type {
    CellAccessRelatedInfo_EUTRA_EPC__plmn_IdentityList_eutra_epc : PLMN_IdentityList_EUTRA_EPC__Type ;
    CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc : CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type ;
    CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc : CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type ;
}.
Definition CellAccessRelatedInfo_EUTRA_EPC__list := (
 Nor PLMN_IdentityList_EUTRA_EPC__Type PLMN_IdentityList_EUTRA_EPC__cond ::
 Nor CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__cond ::
 Nor CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__cond ::
 nil).
Definition CellAccessRelatedInfo_EUTRA_EPC__cond z := 
  PLMN_IdentityList_EUTRA_EPC__cond (CellAccessRelatedInfo_EUTRA_EPC__plmn_IdentityList_eutra_epc z) /\
  CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__cond (CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc z) /\
  CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__cond (CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc z) /\
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
Definition CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Format : T_Format CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__cond CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Format.

Definition CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Format : T_Format CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__cond := (* Eval compute in *) bit_string_fixed_format 28.
Opaque CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__cond CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Format.


Definition CellAccessRelatedInfo_EUTRA_EPC__Format_Type := Eval cbn in seq_format_prod CellAccessRelatedInfo_EUTRA_EPC__list.
Definition CellAccessRelatedInfo_EUTRA_EPC__Format_list : CellAccessRelatedInfo_EUTRA_EPC__Format_Type :=
  (PLMN_IdentityList_EUTRA_EPC__Format, (CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Format, (CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Format, unit_format))).
Definition CellAccessRelatedInfo_EUTRA_EPC__list__Format := (*Eval compute in *) seq_format CellAccessRelatedInfo_EUTRA_EPC__list CellAccessRelatedInfo_EUTRA_EPC__Format_list.
Definition CellAccessRelatedInfo_EUTRA_EPC__F1 z :=
  (CellAccessRelatedInfo_EUTRA_EPC__plmn_IdentityList_eutra_epc z, (CellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc z, (CellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc z, tt))).
Definition CellAccessRelatedInfo_EUTRA_EPC__F2 (y : seq_type CellAccessRelatedInfo_EUTRA_EPC__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CellAccessRelatedInfo_EUTRA_EPC__Type i0 i1 i2
  end.
Lemma CellAccessRelatedInfo_EUTRA_EPC__F1F2_cond (z : CellAccessRelatedInfo_EUTRA_EPC__Type)
  : CellAccessRelatedInfo_EUTRA_EPC__cond z ->
  (seq_cond CellAccessRelatedInfo_EUTRA_EPC__list (CellAccessRelatedInfo_EUTRA_EPC__F1 z)).
intro H. unfold CellAccessRelatedInfo_EUTRA_EPC__cond in H. simpl. auto. Qed.
Lemma CellAccessRelatedInfo_EUTRA_EPC__F1F2_cond2 (z : CellAccessRelatedInfo_EUTRA_EPC__Type)
 : CellAccessRelatedInfo_EUTRA_EPC__F2 (CellAccessRelatedInfo_EUTRA_EPC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellAccessRelatedInfo_EUTRA_EPC__F2F1_cond (y : seq_type CellAccessRelatedInfo_EUTRA_EPC__list)
  : seq_cond CellAccessRelatedInfo_EUTRA_EPC__list y ->
 (CellAccessRelatedInfo_EUTRA_EPC__cond (CellAccessRelatedInfo_EUTRA_EPC__F2 y)) /\  CellAccessRelatedInfo_EUTRA_EPC__F1 (CellAccessRelatedInfo_EUTRA_EPC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellAccessRelatedInfo_EUTRA_EPC__cond. simpl in *. auto.
 - simpl. unfold CellAccessRelatedInfo_EUTRA_EPC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellAccessRelatedInfo_EUTRA_EPC__Format : T_Format CellAccessRelatedInfo_EUTRA_EPC__Type CellAccessRelatedInfo_EUTRA_EPC__cond :=
        proj2_format  CellAccessRelatedInfo_EUTRA_EPC__cond CellAccessRelatedInfo_EUTRA_EPC__list__Format
    CellAccessRelatedInfo_EUTRA_EPC__F1 CellAccessRelatedInfo_EUTRA_EPC__F2 CellAccessRelatedInfo_EUTRA_EPC__F1F2_cond  CellAccessRelatedInfo_EUTRA_EPC__F1F2_cond2 CellAccessRelatedInfo_EUTRA_EPC__F2F1_cond.
Opaque CellAccessRelatedInfo_EUTRA_EPC__cond CellAccessRelatedInfo_EUTRA_EPC__Format.

