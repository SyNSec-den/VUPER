Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SRS_ResourceListConfigCLI_r16.
Definition CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Type := SetupRelease__Type SRS_ResourceListConfigCLI_r16__Type.
Definition CLI_ResourceConfig_r16__srs_ResourceConfig_r16__cond := SetupRelease__cond _ SRS_ResourceListConfigCLI_r16__cond.
Definition CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Format : T_Format CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Type CLI_ResourceConfig_r16__srs_ResourceConfig_r16__cond := SetupRelease__Format _ _ SRS_ResourceListConfigCLI_r16__Format.
Opaque CLI_ResourceConfig_r16__srs_ResourceConfig_r16__cond CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.RSSI_ResourceListConfigCLI_r16.
Definition CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Type := SetupRelease__Type RSSI_ResourceListConfigCLI_r16__Type.
Definition CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__cond := SetupRelease__cond _ RSSI_ResourceListConfigCLI_r16__cond.
Definition CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Format : T_Format CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Type CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__cond := SetupRelease__Format _ _ RSSI_ResourceListConfigCLI_r16__Format.
Opaque CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__cond CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Format.

Record CLI_ResourceConfig_r16__Type : Set :=
  make__CLI_ResourceConfig_r16__Type {
    CLI_ResourceConfig_r16__srs_ResourceConfig_r16 : option CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Type ;
    CLI_ResourceConfig_r16__rssi_ResourceConfig_r16 : option CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Type ;
}.
Definition CLI_ResourceConfig_r16__list := (
 Opt CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Type CLI_ResourceConfig_r16__srs_ResourceConfig_r16__cond ::
 Opt CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Type CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__cond ::
 nil).
Definition CLI_ResourceConfig_r16__cond z := 
  opt_cond CLI_ResourceConfig_r16__srs_ResourceConfig_r16__cond (CLI_ResourceConfig_r16__srs_ResourceConfig_r16 z) /\
  opt_cond CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__cond (CLI_ResourceConfig_r16__rssi_ResourceConfig_r16 z) /\
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
Opaque CLI_ResourceConfig_r16__srs_ResourceConfig_r16__cond CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Format.

Opaque CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__cond CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Format.


Definition CLI_ResourceConfig_r16__Format_Type := Eval cbn in seq_format_prod CLI_ResourceConfig_r16__list.
Definition CLI_ResourceConfig_r16__Format_list : CLI_ResourceConfig_r16__Format_Type :=
  (CLI_ResourceConfig_r16__srs_ResourceConfig_r16__Format, (CLI_ResourceConfig_r16__rssi_ResourceConfig_r16__Format, unit_format)).
Definition CLI_ResourceConfig_r16__list__Format := (*Eval compute in *) seq_format CLI_ResourceConfig_r16__list CLI_ResourceConfig_r16__Format_list.
Definition CLI_ResourceConfig_r16__F1 z :=
  (CLI_ResourceConfig_r16__srs_ResourceConfig_r16 z, (CLI_ResourceConfig_r16__rssi_ResourceConfig_r16 z, tt)).
Definition CLI_ResourceConfig_r16__F2 (y : seq_type CLI_ResourceConfig_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CLI_ResourceConfig_r16__Type i0 i1
  end.
Lemma CLI_ResourceConfig_r16__F1F2_cond (z : CLI_ResourceConfig_r16__Type)
  : CLI_ResourceConfig_r16__cond z ->
  (seq_cond CLI_ResourceConfig_r16__list (CLI_ResourceConfig_r16__F1 z)).
intro H. unfold CLI_ResourceConfig_r16__cond in H. simpl. auto. Qed.
Lemma CLI_ResourceConfig_r16__F1F2_cond2 (z : CLI_ResourceConfig_r16__Type)
 : CLI_ResourceConfig_r16__F2 (CLI_ResourceConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CLI_ResourceConfig_r16__F2F1_cond (y : seq_type CLI_ResourceConfig_r16__list)
  : seq_cond CLI_ResourceConfig_r16__list y ->
 (CLI_ResourceConfig_r16__cond (CLI_ResourceConfig_r16__F2 y)) /\  CLI_ResourceConfig_r16__F1 (CLI_ResourceConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CLI_ResourceConfig_r16__cond. simpl in *. auto.
 - simpl. unfold CLI_ResourceConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CLI_ResourceConfig_r16__Format : T_Format CLI_ResourceConfig_r16__Type CLI_ResourceConfig_r16__cond :=
        proj2_format  CLI_ResourceConfig_r16__cond CLI_ResourceConfig_r16__list__Format
    CLI_ResourceConfig_r16__F1 CLI_ResourceConfig_r16__F2 CLI_ResourceConfig_r16__F1F2_cond  CLI_ResourceConfig_r16__F1F2_cond2 CLI_ResourceConfig_r16__F2F1_cond.
Opaque CLI_ResourceConfig_r16__cond CLI_ResourceConfig_r16__Format.

