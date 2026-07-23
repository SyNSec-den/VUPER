Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.WLAN_Identifiers_r16.

Opaque WLAN_Identifiers_r16__cond WLAN_Identifiers_r16__Format.

Require Import NR.WLAN_RSSI_Range_r16.

Opaque WLAN_RSSI_Range_r16__cond WLAN_RSSI_Range_r16__Format.

Require Import NR.WLAN_RTT_r16.

Opaque WLAN_RTT_r16__cond WLAN_RTT_r16__Format.

Record LogMeasResultWLAN_r16__Type : Set :=
  make__LogMeasResultWLAN_r16__Type {
    LogMeasResultWLAN_r16__wlan_Identifiers_r16 : WLAN_Identifiers_r16__Type ;
    LogMeasResultWLAN_r16__rssiWLAN_r16 : option WLAN_RSSI_Range_r16__Type ;
    LogMeasResultWLAN_r16__rtt_WLAN_r16 : option WLAN_RTT_r16__Type ;
}.
Definition LogMeasResultWLAN_r16__root_list : list seq_elem := (
 Nor WLAN_Identifiers_r16__Type WLAN_Identifiers_r16__cond ::
 Opt WLAN_RSSI_Range_r16__Type WLAN_RSSI_Range_r16__cond ::
 Opt WLAN_RTT_r16__Type WLAN_RTT_r16__cond ::
 nil).
Definition LogMeasResultWLAN_r16__ext_list : list typ := (
  nil).
Definition LogMeasResultWLAN_r16__cond (z : LogMeasResultWLAN_r16__Type) := 
(  WLAN_Identifiers_r16__cond (LogMeasResultWLAN_r16__wlan_Identifiers_r16 z) /\
  opt_cond WLAN_RSSI_Range_r16__cond (LogMeasResultWLAN_r16__rssiWLAN_r16 z) /\
  opt_cond WLAN_RTT_r16__cond (LogMeasResultWLAN_r16__rtt_WLAN_r16 z) /\
  True) /\ 
(  True).


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

Definition LogMeasResultWLAN_r16__root_Format_Type := Eval cbn in seq_format_prod LogMeasResultWLAN_r16__root_list.
Definition LogMeasResultWLAN_r16__root_Format_list : LogMeasResultWLAN_r16__root_Format_Type :=
  (WLAN_Identifiers_r16__Format, (WLAN_RSSI_Range_r16__Format, (WLAN_RTT_r16__Format, unit_format))).

Definition LogMeasResultWLAN_r16__ext_Format_Type := Eval cbn in get_formats LogMeasResultWLAN_r16__ext_list.
Definition LogMeasResultWLAN_r16__ext_Format_list : LogMeasResultWLAN_r16__ext_Format_Type :=
  unit__Format.

Definition LogMeasResultWLAN_r16__list_type : Set := (seq_type LogMeasResultWLAN_r16__root_list) * (seq_ext_type LogMeasResultWLAN_r16__ext_list).
Definition LogMeasResultWLAN_r16__list_cond (z : LogMeasResultWLAN_r16__list_type) : Prop :=
        (seq_cond LogMeasResultWLAN_r16__root_list (fst z)) /\ (seq_ext_cond LogMeasResultWLAN_r16__ext_list (snd z)).
Definition LogMeasResultWLAN_r16__list_format : T_Format LogMeasResultWLAN_r16__list_type LogMeasResultWLAN_r16__list_cond :=
 (* Eval compute in *) seq_ext_format LogMeasResultWLAN_r16__root_list LogMeasResultWLAN_r16__root_Format_list LogMeasResultWLAN_r16__ext_list LogMeasResultWLAN_r16__ext_Format_list.

Opaque LogMeasResultWLAN_r16__list_format.
Definition LogMeasResultWLAN_r16__F1 (z : LogMeasResultWLAN_r16__Type) : LogMeasResultWLAN_r16__list_type :=
  (((LogMeasResultWLAN_r16__wlan_Identifiers_r16 z, (LogMeasResultWLAN_r16__rssiWLAN_r16 z, (LogMeasResultWLAN_r16__rtt_WLAN_r16 z, tt)))), (
tt)).
Definition LogMeasResultWLAN_r16__F2 (y : LogMeasResultWLAN_r16__list_type) : LogMeasResultWLAN_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__LogMeasResultWLAN_r16__Type j0 j1 j2
  end.
Definition LogMeasResultWLAN_r16__helper1 : (forall a : LogMeasResultWLAN_r16__Type, LogMeasResultWLAN_r16__cond a -> LogMeasResultWLAN_r16__list_cond (LogMeasResultWLAN_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LogMeasResultWLAN_r16__helper2 : (forall a : LogMeasResultWLAN_r16__Type, LogMeasResultWLAN_r16__F2 (LogMeasResultWLAN_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LogMeasResultWLAN_r16__helper3 : (forall b : LogMeasResultWLAN_r16__list_type, LogMeasResultWLAN_r16__list_cond b -> LogMeasResultWLAN_r16__cond (LogMeasResultWLAN_r16__F2 b) /\ LogMeasResultWLAN_r16__F1 (LogMeasResultWLAN_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LogMeasResultWLAN_r16__cond, LogMeasResultWLAN_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LogMeasResultWLAN_r16__Format : T_Format LogMeasResultWLAN_r16__Type LogMeasResultWLAN_r16__cond :=
 proj2_format LogMeasResultWLAN_r16__cond LogMeasResultWLAN_r16__list_format  LogMeasResultWLAN_r16__F1 LogMeasResultWLAN_r16__F2 LogMeasResultWLAN_r16__helper1 LogMeasResultWLAN_r16__helper2 LogMeasResultWLAN_r16__helper3.

Opaque LogMeasResultWLAN_r16__cond LogMeasResultWLAN_r16__Format.

