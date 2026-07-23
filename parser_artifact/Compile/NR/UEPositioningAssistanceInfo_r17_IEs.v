Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UE_TxTEG_AssociationList_r17.

Opaque UE_TxTEG_AssociationList_r17__cond UE_TxTEG_AssociationList_r17__Format.

Require Import NR.UEPositioningAssistanceInfo_v1720_IEs.

Opaque UEPositioningAssistanceInfo_v1720_IEs__cond UEPositioningAssistanceInfo_v1720_IEs__Format.

Record UEPositioningAssistanceInfo_r17_IEs__Type : Set :=
  make__UEPositioningAssistanceInfo_r17_IEs__Type {
    UEPositioningAssistanceInfo_r17_IEs__ue_TxTEG_AssociationList_r17 : option UE_TxTEG_AssociationList_r17__Type ;
    UEPositioningAssistanceInfo_r17_IEs__lateNonCriticalExtension : option octet_string ;
    UEPositioningAssistanceInfo_r17_IEs__nonCriticalExtension : option UEPositioningAssistanceInfo_v1720_IEs__Type ;
}.
Definition UEPositioningAssistanceInfo_r17_IEs__list := (
 Opt UE_TxTEG_AssociationList_r17__Type UE_TxTEG_AssociationList_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UEPositioningAssistanceInfo_v1720_IEs__Type UEPositioningAssistanceInfo_v1720_IEs__cond ::
 nil).
Definition UEPositioningAssistanceInfo_r17_IEs__cond z := 
  opt_cond UE_TxTEG_AssociationList_r17__cond (UEPositioningAssistanceInfo_r17_IEs__ue_TxTEG_AssociationList_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UEPositioningAssistanceInfo_r17_IEs__lateNonCriticalExtension z) /\
  opt_cond UEPositioningAssistanceInfo_v1720_IEs__cond (UEPositioningAssistanceInfo_r17_IEs__nonCriticalExtension z) /\
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

Definition UEPositioningAssistanceInfo_r17_IEs__Format_Type := Eval cbn in seq_format_prod UEPositioningAssistanceInfo_r17_IEs__list.
Definition UEPositioningAssistanceInfo_r17_IEs__Format_list : UEPositioningAssistanceInfo_r17_IEs__Format_Type :=
  (UE_TxTEG_AssociationList_r17__Format, (octet_string_nc__Format, (UEPositioningAssistanceInfo_v1720_IEs__Format, unit_format))).
Definition UEPositioningAssistanceInfo_r17_IEs__list__Format := (*Eval compute in *) seq_format UEPositioningAssistanceInfo_r17_IEs__list UEPositioningAssistanceInfo_r17_IEs__Format_list.
Definition UEPositioningAssistanceInfo_r17_IEs__F1 z :=
  (UEPositioningAssistanceInfo_r17_IEs__ue_TxTEG_AssociationList_r17 z, (UEPositioningAssistanceInfo_r17_IEs__lateNonCriticalExtension z, (UEPositioningAssistanceInfo_r17_IEs__nonCriticalExtension z, tt))).
Definition UEPositioningAssistanceInfo_r17_IEs__F2 (y : seq_type UEPositioningAssistanceInfo_r17_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UEPositioningAssistanceInfo_r17_IEs__Type i0 i1 i2
  end.
Lemma UEPositioningAssistanceInfo_r17_IEs__F1F2_cond (z : UEPositioningAssistanceInfo_r17_IEs__Type)
  : UEPositioningAssistanceInfo_r17_IEs__cond z ->
  (seq_cond UEPositioningAssistanceInfo_r17_IEs__list (UEPositioningAssistanceInfo_r17_IEs__F1 z)).
intro H. unfold UEPositioningAssistanceInfo_r17_IEs__cond in H. simpl. auto. Qed.
Lemma UEPositioningAssistanceInfo_r17_IEs__F1F2_cond2 (z : UEPositioningAssistanceInfo_r17_IEs__Type)
 : UEPositioningAssistanceInfo_r17_IEs__F2 (UEPositioningAssistanceInfo_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEPositioningAssistanceInfo_r17_IEs__F2F1_cond (y : seq_type UEPositioningAssistanceInfo_r17_IEs__list)
  : seq_cond UEPositioningAssistanceInfo_r17_IEs__list y ->
 (UEPositioningAssistanceInfo_r17_IEs__cond (UEPositioningAssistanceInfo_r17_IEs__F2 y)) /\  UEPositioningAssistanceInfo_r17_IEs__F1 (UEPositioningAssistanceInfo_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEPositioningAssistanceInfo_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold UEPositioningAssistanceInfo_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEPositioningAssistanceInfo_r17_IEs__Format : T_Format UEPositioningAssistanceInfo_r17_IEs__Type UEPositioningAssistanceInfo_r17_IEs__cond :=
        proj2_format  UEPositioningAssistanceInfo_r17_IEs__cond UEPositioningAssistanceInfo_r17_IEs__list__Format
    UEPositioningAssistanceInfo_r17_IEs__F1 UEPositioningAssistanceInfo_r17_IEs__F2 UEPositioningAssistanceInfo_r17_IEs__F1F2_cond  UEPositioningAssistanceInfo_r17_IEs__F1F2_cond2 UEPositioningAssistanceInfo_r17_IEs__F2F1_cond.
Opaque UEPositioningAssistanceInfo_r17_IEs__cond UEPositioningAssistanceInfo_r17_IEs__Format.

