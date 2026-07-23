Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.MBS_FSAI_List_r17.

Opaque MBS_FSAI_List_r17__cond MBS_FSAI_List_r17__Format.

Record MBS_FSAI_InterFreq_r17__Type : Set :=
  make__MBS_FSAI_InterFreq_r17__Type {
    MBS_FSAI_InterFreq_r17__dl_CarrierFreq_r17 : ARFCN_ValueNR__Type ;
    MBS_FSAI_InterFreq_r17__mbs_FSAI_List_r17 : MBS_FSAI_List_r17__Type ;
}.
Definition MBS_FSAI_InterFreq_r17__list := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor MBS_FSAI_List_r17__Type MBS_FSAI_List_r17__cond ::
 nil).
Definition MBS_FSAI_InterFreq_r17__cond z := 
  ARFCN_ValueNR__cond (MBS_FSAI_InterFreq_r17__dl_CarrierFreq_r17 z) /\
  MBS_FSAI_List_r17__cond (MBS_FSAI_InterFreq_r17__mbs_FSAI_List_r17 z) /\
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

Definition MBS_FSAI_InterFreq_r17__Format_Type := Eval cbn in seq_format_prod MBS_FSAI_InterFreq_r17__list.
Definition MBS_FSAI_InterFreq_r17__Format_list : MBS_FSAI_InterFreq_r17__Format_Type :=
  (ARFCN_ValueNR__Format, (MBS_FSAI_List_r17__Format, unit_format)).
Definition MBS_FSAI_InterFreq_r17__list__Format := (*Eval compute in *) seq_format MBS_FSAI_InterFreq_r17__list MBS_FSAI_InterFreq_r17__Format_list.
Definition MBS_FSAI_InterFreq_r17__F1 z :=
  (MBS_FSAI_InterFreq_r17__dl_CarrierFreq_r17 z, (MBS_FSAI_InterFreq_r17__mbs_FSAI_List_r17 z, tt)).
Definition MBS_FSAI_InterFreq_r17__F2 (y : seq_type MBS_FSAI_InterFreq_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MBS_FSAI_InterFreq_r17__Type i0 i1
  end.
Lemma MBS_FSAI_InterFreq_r17__F1F2_cond (z : MBS_FSAI_InterFreq_r17__Type)
  : MBS_FSAI_InterFreq_r17__cond z ->
  (seq_cond MBS_FSAI_InterFreq_r17__list (MBS_FSAI_InterFreq_r17__F1 z)).
intro H. unfold MBS_FSAI_InterFreq_r17__cond in H. simpl. auto. Qed.
Lemma MBS_FSAI_InterFreq_r17__F1F2_cond2 (z : MBS_FSAI_InterFreq_r17__Type)
 : MBS_FSAI_InterFreq_r17__F2 (MBS_FSAI_InterFreq_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MBS_FSAI_InterFreq_r17__F2F1_cond (y : seq_type MBS_FSAI_InterFreq_r17__list)
  : seq_cond MBS_FSAI_InterFreq_r17__list y ->
 (MBS_FSAI_InterFreq_r17__cond (MBS_FSAI_InterFreq_r17__F2 y)) /\  MBS_FSAI_InterFreq_r17__F1 (MBS_FSAI_InterFreq_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MBS_FSAI_InterFreq_r17__cond. simpl in *. auto.
 - simpl. unfold MBS_FSAI_InterFreq_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MBS_FSAI_InterFreq_r17__Format : T_Format MBS_FSAI_InterFreq_r17__Type MBS_FSAI_InterFreq_r17__cond :=
        proj2_format  MBS_FSAI_InterFreq_r17__cond MBS_FSAI_InterFreq_r17__list__Format
    MBS_FSAI_InterFreq_r17__F1 MBS_FSAI_InterFreq_r17__F2 MBS_FSAI_InterFreq_r17__F1F2_cond  MBS_FSAI_InterFreq_r17__F1F2_cond2 MBS_FSAI_InterFreq_r17__F2F1_cond.
Opaque MBS_FSAI_InterFreq_r17__cond MBS_FSAI_InterFreq_r17__Format.

