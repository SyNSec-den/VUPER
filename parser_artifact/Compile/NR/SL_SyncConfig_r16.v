Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Type : Set :=
 | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB0
 | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB3
 | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB6
 | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB9
 | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB12
.
Definition SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__cond := (fun (_ : SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Type) => True).
Lemma SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__nat__helper.

Definition SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1 t :=
  match t with
  | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB0 => 0
  | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB3 => 1
  | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB6 => 2
  | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB9 => 3
  | SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB12 => 4
  end.
Definition SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F2 n :=
  match n with
  | 0 => SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB0
  | 1 => SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB3
  | 2 => SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB6
  | 3 => SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB9
  | 4 => SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB12
  | _ => SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__dB0
  end.
Lemma SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1F2 : forall x : SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Type, (SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1 x <= 4) /\ SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F2 (SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F2F1 : forall (y : nat) (H : y <= 4), SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1 (SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Type : Set :=
 | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB0
 | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB3
 | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB6
 | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB9
 | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB12
 | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dBinf
.
Definition SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__cond := (fun (_ : SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Type) => True).
Lemma SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__nat__helper.

Definition SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1 t :=
  match t with
  | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB0 => 0
  | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB3 => 1
  | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB6 => 2
  | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB9 => 3
  | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB12 => 4
  | SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dBinf => 5
  end.
Definition SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F2 n :=
  match n with
  | 0 => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB0
  | 1 => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB3
  | 2 => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB6
  | 3 => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB9
  | 4 => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB12
  | 5 => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dBinf
  | _ => SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__dB0
  end.
Lemma SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1F2 : forall x : SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Type, (SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1 x <= 5) /\ SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F2 (SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F2F1 : forall (y : nat) (H : y <= 5), SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1 (SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.FilterCoefficient.

Opaque FilterCoefficient__cond FilterCoefficient__Format.

Require Import NR.SL_SSB_TimeAllocation_r16.

Opaque SL_SSB_TimeAllocation_r16__cond SL_SSB_TimeAllocation_r16__Format.

Require Import NR.SL_SSB_TimeAllocation_r16.

Opaque SL_SSB_TimeAllocation_r16__cond SL_SSB_TimeAllocation_r16__Format.

Require Import NR.SL_SSB_TimeAllocation_r16.

Opaque SL_SSB_TimeAllocation_r16__cond SL_SSB_TimeAllocation_r16__Format.

Lemma SL_SyncConfig_r16__sl_SSID_r16__helper1 : (0 <= 671)%Z.  lia. Qed.
Lemma SL_SyncConfig_r16__sl_SSID_r16__helper2 : to_bit_sz (Z.to_nat (671 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (671 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_SyncConfig_r16__sl_SSID_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_SyncConfig_r16__sl_SSID_r16__Type := Z.
Definition SL_SyncConfig_r16__sl_SSID_r16__cond := (fun z => (0 <= z <= 671)%Z).
Require Import NR.SL_RSRP_Range_r16.

Opaque SL_RSRP_Range_r16__cond SL_RSRP_Range_r16__Format.

Require Import NR.SL_RSRP_Range_r16.

Opaque SL_RSRP_Range_r16__cond SL_RSRP_Range_r16__Format.

Definition SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Type := bit_string_fixed.
Definition SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Record SL_SyncConfig_r16__txParameters_r16__Type : Set :=
  make__SL_SyncConfig_r16__txParameters_r16__Type {
    SL_SyncConfig_r16__txParameters_r16__syncTxThreshIC_r16 : option SL_RSRP_Range_r16__Type ;
    SL_SyncConfig_r16__txParameters_r16__syncTxThreshOoC_r16 : option SL_RSRP_Range_r16__Type ;
    SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16 : option SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Type ;
}.
Definition SL_SyncConfig_r16__txParameters_r16__list := (
 Opt SL_RSRP_Range_r16__Type SL_RSRP_Range_r16__cond ::
 Opt SL_RSRP_Range_r16__Type SL_RSRP_Range_r16__cond ::
 Opt SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Type SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__cond ::
 nil).
Definition SL_SyncConfig_r16__txParameters_r16__cond z := 
  opt_cond SL_RSRP_Range_r16__cond (SL_SyncConfig_r16__txParameters_r16__syncTxThreshIC_r16 z) /\
  opt_cond SL_RSRP_Range_r16__cond (SL_SyncConfig_r16__txParameters_r16__syncTxThreshOoC_r16 z) /\
  opt_cond SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__cond (SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16 z) /\
  True.

Inductive SL_SyncConfig_r16__gnss_Sync_r16__Type : Set :=
 | SL_SyncConfig_r16__gnss_Sync_r16__true
.
Definition SL_SyncConfig_r16__gnss_Sync_r16__cond := (fun (_ : SL_SyncConfig_r16__gnss_Sync_r16__Type) => True).
Lemma SL_SyncConfig_r16__gnss_Sync_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SyncConfig_r16__gnss_Sync_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_SyncConfig_r16__gnss_Sync_r16__nat__helper.

Definition SL_SyncConfig_r16__gnss_Sync_r16__F1 t :=
  match t with
  | SL_SyncConfig_r16__gnss_Sync_r16__true => 0
  end.
Definition SL_SyncConfig_r16__gnss_Sync_r16__F2 n :=
  match n with
  | 0 => SL_SyncConfig_r16__gnss_Sync_r16__true
  | _ => SL_SyncConfig_r16__gnss_Sync_r16__true
  end.
Lemma SL_SyncConfig_r16__gnss_Sync_r16__F1F2 : forall x : SL_SyncConfig_r16__gnss_Sync_r16__Type, (SL_SyncConfig_r16__gnss_Sync_r16__F1 x <= 0) /\ SL_SyncConfig_r16__gnss_Sync_r16__F2 (SL_SyncConfig_r16__gnss_Sync_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_SyncConfig_r16__gnss_Sync_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_SyncConfig_r16__gnss_Sync_r16__F1 (SL_SyncConfig_r16__gnss_Sync_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_SyncConfig_r16__Type : Set :=
  make__SL_SyncConfig_r16__Type {
    SL_SyncConfig_r16__sl_SyncRefMinHyst_r16 : option SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Type ;
    SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16 : option SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Type ;
    SL_SyncConfig_r16__sl_filterCoefficient_r16 : option FilterCoefficient__Type ;
    SL_SyncConfig_r16__sl_SSB_TimeAllocation1_r16 : option SL_SSB_TimeAllocation_r16__Type ;
    SL_SyncConfig_r16__sl_SSB_TimeAllocation2_r16 : option SL_SSB_TimeAllocation_r16__Type ;
    SL_SyncConfig_r16__sl_SSB_TimeAllocation3_r16 : option SL_SSB_TimeAllocation_r16__Type ;
    SL_SyncConfig_r16__sl_SSID_r16 : option Z ;
    SL_SyncConfig_r16__txParameters_r16 : SL_SyncConfig_r16__txParameters_r16__Type ;
    SL_SyncConfig_r16__gnss_Sync_r16 : option SL_SyncConfig_r16__gnss_Sync_r16__Type ;
}.
Definition SL_SyncConfig_r16__root_list : list seq_elem := (
 Opt SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Type SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__cond ::
 Opt SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Type SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__cond ::
 Opt FilterCoefficient__Type FilterCoefficient__cond ::
 Opt SL_SSB_TimeAllocation_r16__Type SL_SSB_TimeAllocation_r16__cond ::
 Opt SL_SSB_TimeAllocation_r16__Type SL_SSB_TimeAllocation_r16__cond ::
 Opt SL_SSB_TimeAllocation_r16__Type SL_SSB_TimeAllocation_r16__cond ::
 Opt Z SL_SyncConfig_r16__sl_SSID_r16__cond ::
 Nor SL_SyncConfig_r16__txParameters_r16__Type SL_SyncConfig_r16__txParameters_r16__cond ::
 Opt SL_SyncConfig_r16__gnss_Sync_r16__Type SL_SyncConfig_r16__gnss_Sync_r16__cond ::
 nil).
Definition SL_SyncConfig_r16__ext_list : list typ := (
  nil).
Definition SL_SyncConfig_r16__cond (z : SL_SyncConfig_r16__Type) := 
(  opt_cond SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__cond (SL_SyncConfig_r16__sl_SyncRefMinHyst_r16 z) /\
  opt_cond SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__cond (SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16 z) /\
  opt_cond FilterCoefficient__cond (SL_SyncConfig_r16__sl_filterCoefficient_r16 z) /\
  opt_cond SL_SSB_TimeAllocation_r16__cond (SL_SyncConfig_r16__sl_SSB_TimeAllocation1_r16 z) /\
  opt_cond SL_SSB_TimeAllocation_r16__cond (SL_SyncConfig_r16__sl_SSB_TimeAllocation2_r16 z) /\
  opt_cond SL_SSB_TimeAllocation_r16__cond (SL_SyncConfig_r16__sl_SSB_TimeAllocation3_r16 z) /\
  opt_cond SL_SyncConfig_r16__sl_SSID_r16__cond (SL_SyncConfig_r16__sl_SSID_r16 z) /\
  SL_SyncConfig_r16__txParameters_r16__cond (SL_SyncConfig_r16__txParameters_r16 z) /\
  opt_cond SL_SyncConfig_r16__gnss_Sync_r16__cond (SL_SyncConfig_r16__gnss_Sync_r16 z) /\
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
Definition SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Format : T_Format SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__nat__Format SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1 SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F2 SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F1F2 SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__F2F1.

Opaque SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__cond SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Format.

Definition SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Format : T_Format SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__nat__Format SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1 SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F2 SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F1F2 SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__F2F1.

Opaque SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__cond SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Format.

Definition SL_SyncConfig_r16__sl_SSID_r16__Format : T_Format Z SL_SyncConfig_r16__sl_SSID_r16__cond :=
 ranged_int_format (0) (671) SL_SyncConfig_r16__sl_SSID_r16__helper1 SL_SyncConfig_r16__sl_SSID_r16__helper2.

Opaque SL_SyncConfig_r16__sl_SSID_r16__cond SL_SyncConfig_r16__sl_SSID_r16__Format.

Definition SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Format : T_Format SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Type SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__cond SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Format.


Definition SL_SyncConfig_r16__txParameters_r16__Format_Type := Eval cbn in seq_format_prod SL_SyncConfig_r16__txParameters_r16__list.
Definition SL_SyncConfig_r16__txParameters_r16__Format_list : SL_SyncConfig_r16__txParameters_r16__Format_Type :=
  (SL_RSRP_Range_r16__Format, (SL_RSRP_Range_r16__Format, (SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16__Format, unit_format))).
Definition SL_SyncConfig_r16__txParameters_r16__list__Format := (*Eval compute in *) seq_format SL_SyncConfig_r16__txParameters_r16__list SL_SyncConfig_r16__txParameters_r16__Format_list.
Definition SL_SyncConfig_r16__txParameters_r16__F1 z :=
  (SL_SyncConfig_r16__txParameters_r16__syncTxThreshIC_r16 z, (SL_SyncConfig_r16__txParameters_r16__syncTxThreshOoC_r16 z, (SL_SyncConfig_r16__txParameters_r16__syncInfoReserved_r16 z, tt))).
Definition SL_SyncConfig_r16__txParameters_r16__F2 (y : seq_type SL_SyncConfig_r16__txParameters_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SL_SyncConfig_r16__txParameters_r16__Type i0 i1 i2
  end.
Lemma SL_SyncConfig_r16__txParameters_r16__F1F2_cond (z : SL_SyncConfig_r16__txParameters_r16__Type)
  : SL_SyncConfig_r16__txParameters_r16__cond z ->
  (seq_cond SL_SyncConfig_r16__txParameters_r16__list (SL_SyncConfig_r16__txParameters_r16__F1 z)).
intro H. unfold SL_SyncConfig_r16__txParameters_r16__cond in H. simpl. auto. Qed.
Lemma SL_SyncConfig_r16__txParameters_r16__F1F2_cond2 (z : SL_SyncConfig_r16__txParameters_r16__Type)
 : SL_SyncConfig_r16__txParameters_r16__F2 (SL_SyncConfig_r16__txParameters_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_SyncConfig_r16__txParameters_r16__F2F1_cond (y : seq_type SL_SyncConfig_r16__txParameters_r16__list)
  : seq_cond SL_SyncConfig_r16__txParameters_r16__list y ->
 (SL_SyncConfig_r16__txParameters_r16__cond (SL_SyncConfig_r16__txParameters_r16__F2 y)) /\  SL_SyncConfig_r16__txParameters_r16__F1 (SL_SyncConfig_r16__txParameters_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_SyncConfig_r16__txParameters_r16__cond. simpl in *. auto.
 - simpl. unfold SL_SyncConfig_r16__txParameters_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_SyncConfig_r16__txParameters_r16__Format : T_Format SL_SyncConfig_r16__txParameters_r16__Type SL_SyncConfig_r16__txParameters_r16__cond :=
        proj2_format  SL_SyncConfig_r16__txParameters_r16__cond SL_SyncConfig_r16__txParameters_r16__list__Format
    SL_SyncConfig_r16__txParameters_r16__F1 SL_SyncConfig_r16__txParameters_r16__F2 SL_SyncConfig_r16__txParameters_r16__F1F2_cond  SL_SyncConfig_r16__txParameters_r16__F1F2_cond2 SL_SyncConfig_r16__txParameters_r16__F2F1_cond.
Opaque SL_SyncConfig_r16__txParameters_r16__cond SL_SyncConfig_r16__txParameters_r16__Format.

Definition SL_SyncConfig_r16__gnss_Sync_r16__Format : T_Format SL_SyncConfig_r16__gnss_Sync_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_SyncConfig_r16__gnss_Sync_r16__nat__Format SL_SyncConfig_r16__gnss_Sync_r16__F1 SL_SyncConfig_r16__gnss_Sync_r16__F2 SL_SyncConfig_r16__gnss_Sync_r16__F1F2 SL_SyncConfig_r16__gnss_Sync_r16__F2F1.

Opaque SL_SyncConfig_r16__gnss_Sync_r16__cond SL_SyncConfig_r16__gnss_Sync_r16__Format.


Definition SL_SyncConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_SyncConfig_r16__root_list.
Definition SL_SyncConfig_r16__root_Format_list : SL_SyncConfig_r16__root_Format_Type :=
  (SL_SyncConfig_r16__sl_SyncRefMinHyst_r16__Format, (SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16__Format, (FilterCoefficient__Format, (SL_SSB_TimeAllocation_r16__Format, (SL_SSB_TimeAllocation_r16__Format, (SL_SSB_TimeAllocation_r16__Format, (SL_SyncConfig_r16__sl_SSID_r16__Format, (SL_SyncConfig_r16__txParameters_r16__Format, (SL_SyncConfig_r16__gnss_Sync_r16__Format, unit_format))))))))).

Definition SL_SyncConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_SyncConfig_r16__ext_list.
Definition SL_SyncConfig_r16__ext_Format_list : SL_SyncConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_SyncConfig_r16__list_type : Set := (seq_type SL_SyncConfig_r16__root_list) * (seq_ext_type SL_SyncConfig_r16__ext_list).
Definition SL_SyncConfig_r16__list_cond (z : SL_SyncConfig_r16__list_type) : Prop :=
        (seq_cond SL_SyncConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_SyncConfig_r16__ext_list (snd z)).
Definition SL_SyncConfig_r16__list_format : T_Format SL_SyncConfig_r16__list_type SL_SyncConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_SyncConfig_r16__root_list SL_SyncConfig_r16__root_Format_list SL_SyncConfig_r16__ext_list SL_SyncConfig_r16__ext_Format_list.

Opaque SL_SyncConfig_r16__list_format.
Definition SL_SyncConfig_r16__F1 (z : SL_SyncConfig_r16__Type) : SL_SyncConfig_r16__list_type :=
  (((SL_SyncConfig_r16__sl_SyncRefMinHyst_r16 z, (SL_SyncConfig_r16__sl_SyncRefDiffHyst_r16 z, (SL_SyncConfig_r16__sl_filterCoefficient_r16 z, (SL_SyncConfig_r16__sl_SSB_TimeAllocation1_r16 z, (SL_SyncConfig_r16__sl_SSB_TimeAllocation2_r16 z, (SL_SyncConfig_r16__sl_SSB_TimeAllocation3_r16 z, (SL_SyncConfig_r16__sl_SSID_r16 z, (SL_SyncConfig_r16__txParameters_r16 z, (SL_SyncConfig_r16__gnss_Sync_r16 z, tt)))))))))), (
tt)).
Definition SL_SyncConfig_r16__F2 (y : SL_SyncConfig_r16__list_type) : SL_SyncConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__SL_SyncConfig_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition SL_SyncConfig_r16__helper1 : (forall a : SL_SyncConfig_r16__Type, SL_SyncConfig_r16__cond a -> SL_SyncConfig_r16__list_cond (SL_SyncConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_SyncConfig_r16__helper2 : (forall a : SL_SyncConfig_r16__Type, SL_SyncConfig_r16__F2 (SL_SyncConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_SyncConfig_r16__helper3 : (forall b : SL_SyncConfig_r16__list_type, SL_SyncConfig_r16__list_cond b -> SL_SyncConfig_r16__cond (SL_SyncConfig_r16__F2 b) /\ SL_SyncConfig_r16__F1 (SL_SyncConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_SyncConfig_r16__cond, SL_SyncConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_SyncConfig_r16__Format : T_Format SL_SyncConfig_r16__Type SL_SyncConfig_r16__cond :=
 proj2_format SL_SyncConfig_r16__cond SL_SyncConfig_r16__list_format  SL_SyncConfig_r16__F1 SL_SyncConfig_r16__F2 SL_SyncConfig_r16__helper1 SL_SyncConfig_r16__helper2 SL_SyncConfig_r16__helper3.

Opaque SL_SyncConfig_r16__cond SL_SyncConfig_r16__Format.

