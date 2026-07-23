Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_ConfigCommonNR_r16.

Opaque SL_ConfigCommonNR_r16__cond SL_ConfigCommonNR_r16__Format.

Require Import NR.SL_DRX_ConfigGC_BC_r17.

Opaque SL_DRX_ConfigGC_BC_r17__cond SL_DRX_ConfigGC_BC_r17__Format.

Require Import NR.SL_DiscConfigCommon_r17.

Opaque SL_DiscConfigCommon_r17__cond SL_DiscConfigCommon_r17__Format.

Inductive SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Type : Set :=
 | SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__enabled
.
Definition SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__cond := (fun (_ : SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Type) => True).
Lemma SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__nat__helper.

Definition SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1 t :=
  match t with
  | SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__enabled => 0
  end.
Definition SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F2 n :=
  match n with
  | 0 => SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__enabled
  | _ => SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__enabled
  end.
Lemma SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1F2 : forall x : SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Type, (SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1 x <= 0) /\ SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F2 (SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1 (SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Type : Set :=
 | SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__enabled
.
Definition SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__cond := (fun (_ : SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Type) => True).
Lemma SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__nat__helper.

Definition SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1 t :=
  match t with
  | SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__enabled => 0
  end.
Definition SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F2 n :=
  match n with
  | 0 => SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__enabled
  | _ => SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__enabled
  end.
Lemma SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1F2 : forall x : SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Type, (SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1 x <= 0) /\ SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F2 (SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1 (SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Type : Set :=
 | SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__enabled
.
Definition SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__cond := (fun (_ : SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Type) => True).
Lemma SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__nat__helper.

Definition SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1 t :=
  match t with
  | SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__enabled => 0
  end.
Definition SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F2 n :=
  match n with
  | 0 => SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__enabled
  | _ => SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__enabled
  end.
Lemma SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1F2 : forall x : SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Type, (SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1 x <= 0) /\ SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F2 (SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1 (SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_TimersAndConstantsRemoteUE_r17.

Opaque UE_TimersAndConstantsRemoteUE_r17__cond UE_TimersAndConstantsRemoteUE_r17__Format.

Record SIB12_IEs_r16__ext0O__Type : Set :=
  make__SIB12_IEs_r16__ext0O__Type {
    SIB12_IEs_r16__ext0O__sl_DRX_ConfigCommonGC_BC_r17 : option SL_DRX_ConfigGC_BC_r17__Type ;
    SIB12_IEs_r16__ext0O__sl_DiscConfigCommon_r17 : option SL_DiscConfigCommon_r17__Type ;
    SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17 : option SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Type ;
    SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17 : option SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Type ;
    SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17 : option SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Type ;
    SIB12_IEs_r16__ext0O__sl_TimersAndConstantsRemoteUE_r17 : option UE_TimersAndConstantsRemoteUE_r17__Type ;
}.
Definition SIB12_IEs_r16__ext0O__list := (
 Opt SL_DRX_ConfigGC_BC_r17__Type SL_DRX_ConfigGC_BC_r17__cond ::
 Opt SL_DiscConfigCommon_r17__Type SL_DiscConfigCommon_r17__cond ::
 Opt SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Type SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__cond ::
 Opt SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Type SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__cond ::
 Opt SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Type SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__cond ::
 Opt UE_TimersAndConstantsRemoteUE_r17__Type UE_TimersAndConstantsRemoteUE_r17__cond ::
 nil).
Definition SIB12_IEs_r16__ext0O__cond z := 
  opt_cond SL_DRX_ConfigGC_BC_r17__cond (SIB12_IEs_r16__ext0O__sl_DRX_ConfigCommonGC_BC_r17 z) /\
  opt_cond SL_DiscConfigCommon_r17__cond (SIB12_IEs_r16__ext0O__sl_DiscConfigCommon_r17 z) /\
  opt_cond SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__cond (SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17 z) /\
  opt_cond SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__cond (SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17 z) /\
  opt_cond SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__cond (SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17 z) /\
  opt_cond UE_TimersAndConstantsRemoteUE_r17__cond (SIB12_IEs_r16__ext0O__sl_TimersAndConstantsRemoteUE_r17 z) /\
  True.

Definition SIB12_IEs_r16__ext0__Type := SIB12_IEs_r16__ext0O__Type.
Definition SIB12_IEs_r16__ext0__cond := SIB12_IEs_r16__ext0O__cond.

Record SIB12_IEs_r16__Type : Set :=
  make__SIB12_IEs_r16__Type {
    SIB12_IEs_r16__sl_ConfigCommonNR_r16 : SL_ConfigCommonNR_r16__Type ;
    SIB12_IEs_r16__lateNonCriticalExtension : option octet_string ;
    SIB12_IEs_r16__ext0 : option SIB12_IEs_r16__ext0__Type ;
}.
Definition SIB12_IEs_r16__root_list : list seq_elem := (
 Nor SL_ConfigCommonNR_r16__Type SL_ConfigCommonNR_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB12_IEs_r16__ext_list : list typ := (
  typ_cons SIB12_IEs_r16__ext0__Type SIB12_IEs_r16__ext0__cond ::
  nil).
Definition SIB12_IEs_r16__cond (z : SIB12_IEs_r16__Type) := 
(  SL_ConfigCommonNR_r16__cond (SIB12_IEs_r16__sl_ConfigCommonNR_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB12_IEs_r16__lateNonCriticalExtension z) /\
  True) /\ 
(  opt_cond SIB12_IEs_r16__ext0__cond (SIB12_IEs_r16__ext0 z) /\
  True).


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
Definition SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Format : T_Format SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__nat__Format SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1 SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F2 SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F1F2 SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__F2F1.

Opaque SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__cond SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Format.

Definition SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Format : T_Format SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__nat__Format SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1 SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F2 SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F1F2 SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__F2F1.

Opaque SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__cond SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Format.

Definition SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Format : T_Format SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__nat__Format SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1 SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F2 SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F1F2 SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__F2F1.

Opaque SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__cond SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Format.


Definition SIB12_IEs_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SIB12_IEs_r16__ext0O__list.
Definition SIB12_IEs_r16__ext0O__Format_list : SIB12_IEs_r16__ext0O__Format_Type :=
  (SL_DRX_ConfigGC_BC_r17__Format, (SL_DiscConfigCommon_r17__Format, (SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17__Format, (SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17__Format, (SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17__Format, (UE_TimersAndConstantsRemoteUE_r17__Format, unit_format)))))).
Definition SIB12_IEs_r16__ext0O__list__Format := (*Eval compute in *) seq_format SIB12_IEs_r16__ext0O__list SIB12_IEs_r16__ext0O__Format_list.
Definition SIB12_IEs_r16__ext0O__F1 z :=
  (SIB12_IEs_r16__ext0O__sl_DRX_ConfigCommonGC_BC_r17 z, (SIB12_IEs_r16__ext0O__sl_DiscConfigCommon_r17 z, (SIB12_IEs_r16__ext0O__sl_L2U2N_Relay_r17 z, (SIB12_IEs_r16__ext0O__sl_NonRelayDiscovery_r17 z, (SIB12_IEs_r16__ext0O__sl_L3U2N_RelayDiscovery_r17 z, (SIB12_IEs_r16__ext0O__sl_TimersAndConstantsRemoteUE_r17 z, tt)))))).
Definition SIB12_IEs_r16__ext0O__F2 (y : seq_type SIB12_IEs_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__SIB12_IEs_r16__ext0O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma SIB12_IEs_r16__ext0O__F1F2_cond (z : SIB12_IEs_r16__ext0O__Type)
  : SIB12_IEs_r16__ext0O__cond z ->
  (seq_cond SIB12_IEs_r16__ext0O__list (SIB12_IEs_r16__ext0O__F1 z)).
intro H. unfold SIB12_IEs_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB12_IEs_r16__ext0O__F1F2_cond2 (z : SIB12_IEs_r16__ext0O__Type)
 : SIB12_IEs_r16__ext0O__F2 (SIB12_IEs_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB12_IEs_r16__ext0O__F2F1_cond (y : seq_type SIB12_IEs_r16__ext0O__list)
  : seq_cond SIB12_IEs_r16__ext0O__list y ->
 (SIB12_IEs_r16__ext0O__cond (SIB12_IEs_r16__ext0O__F2 y)) /\  SIB12_IEs_r16__ext0O__F1 (SIB12_IEs_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB12_IEs_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB12_IEs_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB12_IEs_r16__ext0O__Format : T_Format SIB12_IEs_r16__ext0O__Type SIB12_IEs_r16__ext0O__cond :=
        proj2_format  SIB12_IEs_r16__ext0O__cond SIB12_IEs_r16__ext0O__list__Format
    SIB12_IEs_r16__ext0O__F1 SIB12_IEs_r16__ext0O__F2 SIB12_IEs_r16__ext0O__F1F2_cond  SIB12_IEs_r16__ext0O__F1F2_cond2 SIB12_IEs_r16__ext0O__F2F1_cond.
Opaque SIB12_IEs_r16__ext0O__cond SIB12_IEs_r16__ext0O__Format.

Definition SIB12_IEs_r16__ext0__check_all_none (b : SIB12_IEs_r16__ext0O__Type) : bool :=
match b with 
  | make__SIB12_IEs_r16__ext0O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition SIB12_IEs_r16__ext0__Format : T_Format SIB12_IEs_r16__ext0__Type SIB12_IEs_r16__ext0__cond :=
  restrict_add_format SIB12_IEs_r16__ext0__check_all_none SIB12_IEs_r16__ext0O__Format.

Opaque SIB12_IEs_r16__ext0__cond SIB12_IEs_r16__ext0__Format.


Definition SIB12_IEs_r16__root_Format_Type := Eval cbn in seq_format_prod SIB12_IEs_r16__root_list.
Definition SIB12_IEs_r16__root_Format_list : SIB12_IEs_r16__root_Format_Type :=
  (SL_ConfigCommonNR_r16__Format, (octet_string_nc__Format, unit_format)).

Definition SIB12_IEs_r16__ext_Format_Type := Eval cbn in get_formats SIB12_IEs_r16__ext_list.
Definition SIB12_IEs_r16__ext_Format_list : SIB12_IEs_r16__ext_Format_Type :=
  (SIB12_IEs_r16__ext0__Format, unit__Format).

Definition SIB12_IEs_r16__list_type : Set := (seq_type SIB12_IEs_r16__root_list) * (seq_ext_type SIB12_IEs_r16__ext_list).
Definition SIB12_IEs_r16__list_cond (z : SIB12_IEs_r16__list_type) : Prop :=
        (seq_cond SIB12_IEs_r16__root_list (fst z)) /\ (seq_ext_cond SIB12_IEs_r16__ext_list (snd z)).
Definition SIB12_IEs_r16__list_format : T_Format SIB12_IEs_r16__list_type SIB12_IEs_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SIB12_IEs_r16__root_list SIB12_IEs_r16__root_Format_list SIB12_IEs_r16__ext_list SIB12_IEs_r16__ext_Format_list.

Opaque SIB12_IEs_r16__list_format.
Definition SIB12_IEs_r16__F1 (z : SIB12_IEs_r16__Type) : SIB12_IEs_r16__list_type :=
  (((SIB12_IEs_r16__sl_ConfigCommonNR_r16 z, (SIB12_IEs_r16__lateNonCriticalExtension z, tt))), (
(SIB12_IEs_r16__ext0 z, tt))).
Definition SIB12_IEs_r16__F2 (y : SIB12_IEs_r16__list_type) : SIB12_IEs_r16__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__SIB12_IEs_r16__Type j0 j1 i0
  end.
Definition SIB12_IEs_r16__helper1 : (forall a : SIB12_IEs_r16__Type, SIB12_IEs_r16__cond a -> SIB12_IEs_r16__list_cond (SIB12_IEs_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB12_IEs_r16__helper2 : (forall a : SIB12_IEs_r16__Type, SIB12_IEs_r16__F2 (SIB12_IEs_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB12_IEs_r16__helper3 : (forall b : SIB12_IEs_r16__list_type, SIB12_IEs_r16__list_cond b -> SIB12_IEs_r16__cond (SIB12_IEs_r16__F2 b) /\ SIB12_IEs_r16__F1 (SIB12_IEs_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB12_IEs_r16__cond, SIB12_IEs_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB12_IEs_r16__Format : T_Format SIB12_IEs_r16__Type SIB12_IEs_r16__cond :=
 proj2_format SIB12_IEs_r16__cond SIB12_IEs_r16__list_format  SIB12_IEs_r16__F1 SIB12_IEs_r16__F2 SIB12_IEs_r16__helper1 SIB12_IEs_r16__helper2 SIB12_IEs_r16__helper3.

Opaque SIB12_IEs_r16__cond SIB12_IEs_r16__Format.

