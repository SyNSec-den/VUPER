Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SL_MeasResults_r16.

Opaque SL_MeasResults_r16__cond SL_MeasResults_r16__Format.

Record MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type : Set := make__MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type {}.
Definition MeasurementReportSidelink_r16_IEs__nonCriticalExtension__cond (z : MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type) := True.
Record MeasurementReportSidelink_r16_IEs__Type : Set :=
  make__MeasurementReportSidelink_r16_IEs__Type {
    MeasurementReportSidelink_r16_IEs__sl_measResults_r16 : SL_MeasResults_r16__Type ;
    MeasurementReportSidelink_r16_IEs__lateNonCriticalExtension : option octet_string ;
    MeasurementReportSidelink_r16_IEs__nonCriticalExtension : option MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type ;
}.
Definition MeasurementReportSidelink_r16_IEs__list := (
 Nor SL_MeasResults_r16__Type SL_MeasResults_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type MeasurementReportSidelink_r16_IEs__nonCriticalExtension__cond ::
 nil).
Definition MeasurementReportSidelink_r16_IEs__cond z := 
  SL_MeasResults_r16__cond (MeasurementReportSidelink_r16_IEs__sl_measResults_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MeasurementReportSidelink_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond MeasurementReportSidelink_r16_IEs__nonCriticalExtension__cond (MeasurementReportSidelink_r16_IEs__nonCriticalExtension z) /\
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
Definition MeasurementReportSidelink_r16_IEs__nonCriticalExtension__helper : forall a : MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type, True -> True /\ make__MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Format : T_Format MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type MeasurementReportSidelink_r16_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Type)
    MeasurementReportSidelink_r16_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque MeasurementReportSidelink_r16_IEs__nonCriticalExtension__cond MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Format.


Definition MeasurementReportSidelink_r16_IEs__Format_Type := Eval cbn in seq_format_prod MeasurementReportSidelink_r16_IEs__list.
Definition MeasurementReportSidelink_r16_IEs__Format_list : MeasurementReportSidelink_r16_IEs__Format_Type :=
  (SL_MeasResults_r16__Format, (octet_string_nc__Format, (MeasurementReportSidelink_r16_IEs__nonCriticalExtension__Format, unit_format))).
Definition MeasurementReportSidelink_r16_IEs__list__Format := (*Eval compute in *) seq_format MeasurementReportSidelink_r16_IEs__list MeasurementReportSidelink_r16_IEs__Format_list.
Definition MeasurementReportSidelink_r16_IEs__F1 z :=
  (MeasurementReportSidelink_r16_IEs__sl_measResults_r16 z, (MeasurementReportSidelink_r16_IEs__lateNonCriticalExtension z, (MeasurementReportSidelink_r16_IEs__nonCriticalExtension z, tt))).
Definition MeasurementReportSidelink_r16_IEs__F2 (y : seq_type MeasurementReportSidelink_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasurementReportSidelink_r16_IEs__Type i0 i1 i2
  end.
Lemma MeasurementReportSidelink_r16_IEs__F1F2_cond (z : MeasurementReportSidelink_r16_IEs__Type)
  : MeasurementReportSidelink_r16_IEs__cond z ->
  (seq_cond MeasurementReportSidelink_r16_IEs__list (MeasurementReportSidelink_r16_IEs__F1 z)).
intro H. unfold MeasurementReportSidelink_r16_IEs__cond in H. simpl. auto. Qed.
Lemma MeasurementReportSidelink_r16_IEs__F1F2_cond2 (z : MeasurementReportSidelink_r16_IEs__Type)
 : MeasurementReportSidelink_r16_IEs__F2 (MeasurementReportSidelink_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasurementReportSidelink_r16_IEs__F2F1_cond (y : seq_type MeasurementReportSidelink_r16_IEs__list)
  : seq_cond MeasurementReportSidelink_r16_IEs__list y ->
 (MeasurementReportSidelink_r16_IEs__cond (MeasurementReportSidelink_r16_IEs__F2 y)) /\  MeasurementReportSidelink_r16_IEs__F1 (MeasurementReportSidelink_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasurementReportSidelink_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold MeasurementReportSidelink_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasurementReportSidelink_r16_IEs__Format : T_Format MeasurementReportSidelink_r16_IEs__Type MeasurementReportSidelink_r16_IEs__cond :=
        proj2_format  MeasurementReportSidelink_r16_IEs__cond MeasurementReportSidelink_r16_IEs__list__Format
    MeasurementReportSidelink_r16_IEs__F1 MeasurementReportSidelink_r16_IEs__F2 MeasurementReportSidelink_r16_IEs__F1F2_cond  MeasurementReportSidelink_r16_IEs__F1F2_cond2 MeasurementReportSidelink_r16_IEs__F2F1_cond.
Opaque MeasurementReportSidelink_r16_IEs__cond MeasurementReportSidelink_r16_IEs__Format.

