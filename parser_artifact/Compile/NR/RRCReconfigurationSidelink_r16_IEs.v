Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SLRB_Config_r16.

Opaque SLRB_Config_r16__cond SLRB_Config_r16__Format.

Definition RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Type := list SLRB_Config_r16__Type.

Lemma RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__cond (z : RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SLRB_Config_r16__cond z) .

Require Import NR.SLRB_PC5_ConfigIndex_r16.

Opaque SLRB_PC5_ConfigIndex_r16__cond SLRB_PC5_ConfigIndex_r16__Format.

Definition RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Type := list SLRB_PC5_ConfigIndex_r16__Type.

Lemma RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__cond (z : RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SLRB_PC5_ConfigIndex_r16__cond z) .

Require Import NR.SetupRelease.
Require Import NR.SL_MeasConfig_r16.
Definition RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Type := SetupRelease__Type SL_MeasConfig_r16__Type.
Definition RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__cond := SetupRelease__cond _ SL_MeasConfig_r16__cond.
Definition RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Format : T_Format RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Type RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__cond := SetupRelease__Format _ _ SL_MeasConfig_r16__Format.
Opaque RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__cond RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_CSI_RS_Config_r16.
Definition RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Type := SetupRelease__Type SL_CSI_RS_Config_r16__Type.
Definition RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__cond := SetupRelease__cond _ SL_CSI_RS_Config_r16__cond.
Definition RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Format : T_Format RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Type RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__cond := SetupRelease__Format _ _ SL_CSI_RS_Config_r16__Format.
Opaque RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__cond RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Format.

Inductive RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Type : Set :=
 | RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__true
.
Definition RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__cond := (fun (_ : RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Type) => True).
Lemma RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__nat__helper.

Definition RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1 t :=
  match t with
  | RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__true => 0
  end.
Definition RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F2 n :=
  match n with
  | 0 => RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__true
  | _ => RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__true
  end.
Lemma RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1F2 : forall x : RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Type, (RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1 x <= 0) /\ RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F2 (RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1 (RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F2 y) = y. enum_solve H y. Qed.

Lemma RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__helper1 : (3 <= 160)%Z.  lia. Qed.
Lemma RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__helper2 : to_bit_sz (Z.to_nat (160 - 3)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (160 - 3))%Z). { apply Zorder.Zle_minus_le_0. apply RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__Type := Z.
Definition RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__cond := (fun z => (3 <= z <= 160)%Z).
Require Import NR.RRCReconfigurationSidelink_v1700_IEs.

Opaque RRCReconfigurationSidelink_v1700_IEs__cond RRCReconfigurationSidelink_v1700_IEs__Format.

Record RRCReconfigurationSidelink_r16_IEs__Type : Set :=
  make__RRCReconfigurationSidelink_r16_IEs__Type {
    RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16 : option RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Type ;
    RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16 : option RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Type ;
    RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16 : option RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Type ;
    RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16 : option RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Type ;
    RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16 : option RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Type ;
    RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16 : option Z ;
    RRCReconfigurationSidelink_r16_IEs__lateNonCriticalExtension : option octet_string ;
    RRCReconfigurationSidelink_r16_IEs__nonCriticalExtension : option RRCReconfigurationSidelink_v1700_IEs__Type ;
}.
Definition RRCReconfigurationSidelink_r16_IEs__list := (
 Opt RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Type RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__cond ::
 Opt RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Type RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__cond ::
 Opt RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Type RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__cond ::
 Opt RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Type RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__cond ::
 Opt RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Type RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__cond ::
 Opt Z RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCReconfigurationSidelink_v1700_IEs__Type RRCReconfigurationSidelink_v1700_IEs__cond ::
 nil).
Definition RRCReconfigurationSidelink_r16_IEs__cond z := 
  opt_cond RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__cond (RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16 z) /\
  opt_cond RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__cond (RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16 z) /\
  opt_cond RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__cond (RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16 z) /\
  opt_cond RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__cond (RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16 z) /\
  opt_cond RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__cond (RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16 z) /\
  opt_cond RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__cond (RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfigurationSidelink_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond RRCReconfigurationSidelink_v1700_IEs__cond (RRCReconfigurationSidelink_r16_IEs__nonCriticalExtension z) /\
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
Definition RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Format : T_Format RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Type RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__cond := seq_of_format SLRB_Config_r16__Format 1 maxNrofSLRB_r16 RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__helper1 RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__helper2.

Opaque RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__cond RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Format.

Definition RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Format : T_Format RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Type RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__cond := seq_of_format SLRB_PC5_ConfigIndex_r16__Format 1 maxNrofSLRB_r16 RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__helper1 RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__helper2.

Opaque RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__cond RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Format.

Opaque RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__cond RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Format.

Opaque RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__cond RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Format.

Definition RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Format : T_Format RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__nat__Format RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1 RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F2 RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F1F2 RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__F2F1.

Opaque RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__cond RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Format.

Definition RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__Format : T_Format Z RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__cond :=
 ranged_int_format (3) (160) RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__helper1 RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__helper2.

Opaque RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__cond RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__Format.


Definition RRCReconfigurationSidelink_r16_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationSidelink_r16_IEs__list.
Definition RRCReconfigurationSidelink_r16_IEs__Format_list : RRCReconfigurationSidelink_r16_IEs__Format_Type :=
  (RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16__Format, (RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16__Format, (RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16__Format, (RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16__Format, (RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16__Format, (RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16__Format, (octet_string_nc__Format, (RRCReconfigurationSidelink_v1700_IEs__Format, unit_format)))))))).
Definition RRCReconfigurationSidelink_r16_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfigurationSidelink_r16_IEs__list RRCReconfigurationSidelink_r16_IEs__Format_list.
Definition RRCReconfigurationSidelink_r16_IEs__F1 z :=
  (RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToAddModList_r16 z, (RRCReconfigurationSidelink_r16_IEs__slrb_ConfigToReleaseList_r16 z, (RRCReconfigurationSidelink_r16_IEs__sl_MeasConfig_r16 z, (RRCReconfigurationSidelink_r16_IEs__sl_CSI_RS_Config_r16 z, (RRCReconfigurationSidelink_r16_IEs__sl_ResetConfig_r16 z, (RRCReconfigurationSidelink_r16_IEs__sl_LatencyBoundCSI_Report_r16 z, (RRCReconfigurationSidelink_r16_IEs__lateNonCriticalExtension z, (RRCReconfigurationSidelink_r16_IEs__nonCriticalExtension z, tt)))))))).
Definition RRCReconfigurationSidelink_r16_IEs__F2 (y : seq_type RRCReconfigurationSidelink_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__RRCReconfigurationSidelink_r16_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma RRCReconfigurationSidelink_r16_IEs__F1F2_cond (z : RRCReconfigurationSidelink_r16_IEs__Type)
  : RRCReconfigurationSidelink_r16_IEs__cond z ->
  (seq_cond RRCReconfigurationSidelink_r16_IEs__list (RRCReconfigurationSidelink_r16_IEs__F1 z)).
intro H. unfold RRCReconfigurationSidelink_r16_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationSidelink_r16_IEs__F1F2_cond2 (z : RRCReconfigurationSidelink_r16_IEs__Type)
 : RRCReconfigurationSidelink_r16_IEs__F2 (RRCReconfigurationSidelink_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationSidelink_r16_IEs__F2F1_cond (y : seq_type RRCReconfigurationSidelink_r16_IEs__list)
  : seq_cond RRCReconfigurationSidelink_r16_IEs__list y ->
 (RRCReconfigurationSidelink_r16_IEs__cond (RRCReconfigurationSidelink_r16_IEs__F2 y)) /\  RRCReconfigurationSidelink_r16_IEs__F1 (RRCReconfigurationSidelink_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationSidelink_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationSidelink_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationSidelink_r16_IEs__Format : T_Format RRCReconfigurationSidelink_r16_IEs__Type RRCReconfigurationSidelink_r16_IEs__cond :=
        proj2_format  RRCReconfigurationSidelink_r16_IEs__cond RRCReconfigurationSidelink_r16_IEs__list__Format
    RRCReconfigurationSidelink_r16_IEs__F1 RRCReconfigurationSidelink_r16_IEs__F2 RRCReconfigurationSidelink_r16_IEs__F1F2_cond  RRCReconfigurationSidelink_r16_IEs__F1F2_cond2 RRCReconfigurationSidelink_r16_IEs__F2F1_cond.
Opaque RRCReconfigurationSidelink_r16_IEs__cond RRCReconfigurationSidelink_r16_IEs__Format.

