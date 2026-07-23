Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_InterestedFreqList_r16.

Opaque SL_InterestedFreqList_r16__cond SL_InterestedFreqList_r16__Format.

Require Import NR.SL_TxResourceReqList_r16.

Opaque SL_TxResourceReqList_r16__cond SL_TxResourceReqList_r16__Format.

Require Import NR.SL_FailureList_r16.

Opaque SL_FailureList_r16__cond SL_FailureList_r16__Format.

Require Import NR.SidelinkUEInformationNR_v1700_IEs.

Opaque SidelinkUEInformationNR_v1700_IEs__cond SidelinkUEInformationNR_v1700_IEs__Format.

Record SidelinkUEInformationNR_r16_IEs__Type : Set :=
  make__SidelinkUEInformationNR_r16_IEs__Type {
    SidelinkUEInformationNR_r16_IEs__sl_RxInterestedFreqList_r16 : option SL_InterestedFreqList_r16__Type ;
    SidelinkUEInformationNR_r16_IEs__sl_TxResourceReqList_r16 : option SL_TxResourceReqList_r16__Type ;
    SidelinkUEInformationNR_r16_IEs__sl_FailureList_r16 : option SL_FailureList_r16__Type ;
    SidelinkUEInformationNR_r16_IEs__lateNonCriticalExtension : option octet_string ;
    SidelinkUEInformationNR_r16_IEs__nonCriticalExtension : option SidelinkUEInformationNR_v1700_IEs__Type ;
}.
Definition SidelinkUEInformationNR_r16_IEs__list := (
 Opt SL_InterestedFreqList_r16__Type SL_InterestedFreqList_r16__cond ::
 Opt SL_TxResourceReqList_r16__Type SL_TxResourceReqList_r16__cond ::
 Opt SL_FailureList_r16__Type SL_FailureList_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SidelinkUEInformationNR_v1700_IEs__Type SidelinkUEInformationNR_v1700_IEs__cond ::
 nil).
Definition SidelinkUEInformationNR_r16_IEs__cond z := 
  opt_cond SL_InterestedFreqList_r16__cond (SidelinkUEInformationNR_r16_IEs__sl_RxInterestedFreqList_r16 z) /\
  opt_cond SL_TxResourceReqList_r16__cond (SidelinkUEInformationNR_r16_IEs__sl_TxResourceReqList_r16 z) /\
  opt_cond SL_FailureList_r16__cond (SidelinkUEInformationNR_r16_IEs__sl_FailureList_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SidelinkUEInformationNR_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond SidelinkUEInformationNR_v1700_IEs__cond (SidelinkUEInformationNR_r16_IEs__nonCriticalExtension z) /\
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

Definition SidelinkUEInformationNR_r16_IEs__Format_Type := Eval cbn in seq_format_prod SidelinkUEInformationNR_r16_IEs__list.
Definition SidelinkUEInformationNR_r16_IEs__Format_list : SidelinkUEInformationNR_r16_IEs__Format_Type :=
  (SL_InterestedFreqList_r16__Format, (SL_TxResourceReqList_r16__Format, (SL_FailureList_r16__Format, (octet_string_nc__Format, (SidelinkUEInformationNR_v1700_IEs__Format, unit_format))))).
Definition SidelinkUEInformationNR_r16_IEs__list__Format := (*Eval compute in *) seq_format SidelinkUEInformationNR_r16_IEs__list SidelinkUEInformationNR_r16_IEs__Format_list.
Definition SidelinkUEInformationNR_r16_IEs__F1 z :=
  (SidelinkUEInformationNR_r16_IEs__sl_RxInterestedFreqList_r16 z, (SidelinkUEInformationNR_r16_IEs__sl_TxResourceReqList_r16 z, (SidelinkUEInformationNR_r16_IEs__sl_FailureList_r16 z, (SidelinkUEInformationNR_r16_IEs__lateNonCriticalExtension z, (SidelinkUEInformationNR_r16_IEs__nonCriticalExtension z, tt))))).
Definition SidelinkUEInformationNR_r16_IEs__F2 (y : seq_type SidelinkUEInformationNR_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SidelinkUEInformationNR_r16_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma SidelinkUEInformationNR_r16_IEs__F1F2_cond (z : SidelinkUEInformationNR_r16_IEs__Type)
  : SidelinkUEInformationNR_r16_IEs__cond z ->
  (seq_cond SidelinkUEInformationNR_r16_IEs__list (SidelinkUEInformationNR_r16_IEs__F1 z)).
intro H. unfold SidelinkUEInformationNR_r16_IEs__cond in H. simpl. auto. Qed.
Lemma SidelinkUEInformationNR_r16_IEs__F1F2_cond2 (z : SidelinkUEInformationNR_r16_IEs__Type)
 : SidelinkUEInformationNR_r16_IEs__F2 (SidelinkUEInformationNR_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SidelinkUEInformationNR_r16_IEs__F2F1_cond (y : seq_type SidelinkUEInformationNR_r16_IEs__list)
  : seq_cond SidelinkUEInformationNR_r16_IEs__list y ->
 (SidelinkUEInformationNR_r16_IEs__cond (SidelinkUEInformationNR_r16_IEs__F2 y)) /\  SidelinkUEInformationNR_r16_IEs__F1 (SidelinkUEInformationNR_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SidelinkUEInformationNR_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold SidelinkUEInformationNR_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SidelinkUEInformationNR_r16_IEs__Format : T_Format SidelinkUEInformationNR_r16_IEs__Type SidelinkUEInformationNR_r16_IEs__cond :=
        proj2_format  SidelinkUEInformationNR_r16_IEs__cond SidelinkUEInformationNR_r16_IEs__list__Format
    SidelinkUEInformationNR_r16_IEs__F1 SidelinkUEInformationNR_r16_IEs__F2 SidelinkUEInformationNR_r16_IEs__F1F2_cond  SidelinkUEInformationNR_r16_IEs__F1F2_cond2 SidelinkUEInformationNR_r16_IEs__F2F1_cond.
Opaque SidelinkUEInformationNR_r16_IEs__cond SidelinkUEInformationNR_r16_IEs__Format.

