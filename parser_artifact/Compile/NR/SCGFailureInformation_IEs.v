Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FailureReportSCG.

Opaque FailureReportSCG__cond FailureReportSCG__Format.

Require Import NR.SCGFailureInformation_v1590_IEs.

Opaque SCGFailureInformation_v1590_IEs__cond SCGFailureInformation_v1590_IEs__Format.

Record SCGFailureInformation_IEs__Type : Set :=
  make__SCGFailureInformation_IEs__Type {
    SCGFailureInformation_IEs__failureReportSCG : option FailureReportSCG__Type ;
    SCGFailureInformation_IEs__nonCriticalExtension : option SCGFailureInformation_v1590_IEs__Type ;
}.
Definition SCGFailureInformation_IEs__list := (
 Opt FailureReportSCG__Type FailureReportSCG__cond ::
 Opt SCGFailureInformation_v1590_IEs__Type SCGFailureInformation_v1590_IEs__cond ::
 nil).
Definition SCGFailureInformation_IEs__cond z := 
  opt_cond FailureReportSCG__cond (SCGFailureInformation_IEs__failureReportSCG z) /\
  opt_cond SCGFailureInformation_v1590_IEs__cond (SCGFailureInformation_IEs__nonCriticalExtension z) /\
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

Definition SCGFailureInformation_IEs__Format_Type := Eval cbn in seq_format_prod SCGFailureInformation_IEs__list.
Definition SCGFailureInformation_IEs__Format_list : SCGFailureInformation_IEs__Format_Type :=
  (FailureReportSCG__Format, (SCGFailureInformation_v1590_IEs__Format, unit_format)).
Definition SCGFailureInformation_IEs__list__Format := (*Eval compute in *) seq_format SCGFailureInformation_IEs__list SCGFailureInformation_IEs__Format_list.
Definition SCGFailureInformation_IEs__F1 z :=
  (SCGFailureInformation_IEs__failureReportSCG z, (SCGFailureInformation_IEs__nonCriticalExtension z, tt)).
Definition SCGFailureInformation_IEs__F2 (y : seq_type SCGFailureInformation_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SCGFailureInformation_IEs__Type i0 i1
  end.
Lemma SCGFailureInformation_IEs__F1F2_cond (z : SCGFailureInformation_IEs__Type)
  : SCGFailureInformation_IEs__cond z ->
  (seq_cond SCGFailureInformation_IEs__list (SCGFailureInformation_IEs__F1 z)).
intro H. unfold SCGFailureInformation_IEs__cond in H. simpl. auto. Qed.
Lemma SCGFailureInformation_IEs__F1F2_cond2 (z : SCGFailureInformation_IEs__Type)
 : SCGFailureInformation_IEs__F2 (SCGFailureInformation_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCGFailureInformation_IEs__F2F1_cond (y : seq_type SCGFailureInformation_IEs__list)
  : seq_cond SCGFailureInformation_IEs__list y ->
 (SCGFailureInformation_IEs__cond (SCGFailureInformation_IEs__F2 y)) /\  SCGFailureInformation_IEs__F1 (SCGFailureInformation_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCGFailureInformation_IEs__cond. simpl in *. auto.
 - simpl. unfold SCGFailureInformation_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCGFailureInformation_IEs__Format : T_Format SCGFailureInformation_IEs__Type SCGFailureInformation_IEs__cond :=
        proj2_format  SCGFailureInformation_IEs__cond SCGFailureInformation_IEs__list__Format
    SCGFailureInformation_IEs__F1 SCGFailureInformation_IEs__F2 SCGFailureInformation_IEs__F1F2_cond  SCGFailureInformation_IEs__F1F2_cond2 SCGFailureInformation_IEs__F2F1_cond.
Opaque SCGFailureInformation_IEs__cond SCGFailureInformation_IEs__Format.

