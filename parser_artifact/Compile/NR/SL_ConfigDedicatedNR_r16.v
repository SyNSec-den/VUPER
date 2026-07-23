Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_PHY_MAC_RLC_Config_r16.

Opaque SL_PHY_MAC_RLC_Config_r16__cond SL_PHY_MAC_RLC_Config_r16__Format.

Require Import NR.SLRB_Uu_ConfigIndex_r16.

Opaque SLRB_Uu_ConfigIndex_r16__cond SLRB_Uu_ConfigIndex_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Type := list SLRB_Uu_ConfigIndex_r16__Type.

Lemma SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__cond (z : SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SLRB_Uu_ConfigIndex_r16__cond z) .

Require Import NR.SL_RadioBearerConfig_r16.

Opaque SL_RadioBearerConfig_r16__cond SL_RadioBearerConfig_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Type := list SL_RadioBearerConfig_r16__Type.

Lemma SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__cond (z : SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SL_RadioBearerConfig_r16__cond z) .

Require Import NR.SL_DestinationIndex_r16.

Opaque SL_DestinationIndex_r16__cond SL_DestinationIndex_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Type := list SL_DestinationIndex_r16__Type.

Lemma SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofSL_Dest_r16)%Z. unfold maxNrofSL_Dest_r16.
 lia. Qed.
Lemma SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_Dest_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_Dest_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__cond (z : SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_Dest_r16)%Z /\ (list_and SL_DestinationIndex_r16__cond z) .

Require Import NR.SL_MeasConfigInfo_r16.

Opaque SL_MeasConfigInfo_r16__cond SL_MeasConfigInfo_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Type := list SL_MeasConfigInfo_r16__Type.

Lemma SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__helper1 : (0 <= 1 <= maxNrofSL_Dest_r16)%Z. unfold maxNrofSL_Dest_r16.
 lia. Qed.
Lemma SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_Dest_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_Dest_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__cond (z : SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_Dest_r16)%Z /\ (list_and SL_MeasConfigInfo_r16__cond z) .

Inductive SL_ConfigDedicatedNR_r16__t400_r16__Type : Set :=
 | SL_ConfigDedicatedNR_r16__t400_r16__ms100
 | SL_ConfigDedicatedNR_r16__t400_r16__ms200
 | SL_ConfigDedicatedNR_r16__t400_r16__ms300
 | SL_ConfigDedicatedNR_r16__t400_r16__ms400
 | SL_ConfigDedicatedNR_r16__t400_r16__ms600
 | SL_ConfigDedicatedNR_r16__t400_r16__ms1000
 | SL_ConfigDedicatedNR_r16__t400_r16__ms1500
 | SL_ConfigDedicatedNR_r16__t400_r16__ms2000
.
Definition SL_ConfigDedicatedNR_r16__t400_r16__cond := (fun (_ : SL_ConfigDedicatedNR_r16__t400_r16__Type) => True).
Lemma SL_ConfigDedicatedNR_r16__t400_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ConfigDedicatedNR_r16__t400_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_ConfigDedicatedNR_r16__t400_r16__nat__helper.

Definition SL_ConfigDedicatedNR_r16__t400_r16__F1 t :=
  match t with
  | SL_ConfigDedicatedNR_r16__t400_r16__ms100 => 0
  | SL_ConfigDedicatedNR_r16__t400_r16__ms200 => 1
  | SL_ConfigDedicatedNR_r16__t400_r16__ms300 => 2
  | SL_ConfigDedicatedNR_r16__t400_r16__ms400 => 3
  | SL_ConfigDedicatedNR_r16__t400_r16__ms600 => 4
  | SL_ConfigDedicatedNR_r16__t400_r16__ms1000 => 5
  | SL_ConfigDedicatedNR_r16__t400_r16__ms1500 => 6
  | SL_ConfigDedicatedNR_r16__t400_r16__ms2000 => 7
  end.
Definition SL_ConfigDedicatedNR_r16__t400_r16__F2 n :=
  match n with
  | 0 => SL_ConfigDedicatedNR_r16__t400_r16__ms100
  | 1 => SL_ConfigDedicatedNR_r16__t400_r16__ms200
  | 2 => SL_ConfigDedicatedNR_r16__t400_r16__ms300
  | 3 => SL_ConfigDedicatedNR_r16__t400_r16__ms400
  | 4 => SL_ConfigDedicatedNR_r16__t400_r16__ms600
  | 5 => SL_ConfigDedicatedNR_r16__t400_r16__ms1000
  | 6 => SL_ConfigDedicatedNR_r16__t400_r16__ms1500
  | 7 => SL_ConfigDedicatedNR_r16__t400_r16__ms2000
  | _ => SL_ConfigDedicatedNR_r16__t400_r16__ms100
  end.
Lemma SL_ConfigDedicatedNR_r16__t400_r16__F1F2 : forall x : SL_ConfigDedicatedNR_r16__t400_r16__Type, (SL_ConfigDedicatedNR_r16__t400_r16__F1 x <= 7) /\ SL_ConfigDedicatedNR_r16__t400_r16__F2 (SL_ConfigDedicatedNR_r16__t400_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ConfigDedicatedNR_r16__t400_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_ConfigDedicatedNR_r16__t400_r16__F1 (SL_ConfigDedicatedNR_r16__t400_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.SL_PHY_MAC_RLC_Config_v1700.
Definition SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Type := SetupRelease__Type SL_PHY_MAC_RLC_Config_v1700__Type.
Definition SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__cond := SetupRelease__cond _ SL_PHY_MAC_RLC_Config_v1700__cond.
Definition SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Format : T_Format SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Type SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__cond := SetupRelease__Format _ _ SL_PHY_MAC_RLC_Config_v1700__Format.
Opaque SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__cond SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_DiscConfig_r17.
Definition SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Type := SetupRelease__Type SL_DiscConfig_r17__Type.
Definition SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__cond := SetupRelease__cond _ SL_DiscConfig_r17__cond.
Definition SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Format : T_Format SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Type SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__cond := SetupRelease__Format _ _ SL_DiscConfig_r17__Format.
Opaque SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__cond SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Format.

Record SL_ConfigDedicatedNR_r16__ext0O__Type : Set :=
  make__SL_ConfigDedicatedNR_r16__ext0O__Type {
    SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700 : option SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Type ;
    SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17 : option SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Type ;
}.
Definition SL_ConfigDedicatedNR_r16__ext0O__list := (
 Opt SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Type SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__cond ::
 Opt SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Type SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__cond ::
 nil).
Definition SL_ConfigDedicatedNR_r16__ext0O__cond z := 
  opt_cond SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__cond (SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700 z) /\
  opt_cond SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__cond (SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17 z) /\
  True.

Definition SL_ConfigDedicatedNR_r16__ext0__Type := SL_ConfigDedicatedNR_r16__ext0O__Type.
Definition SL_ConfigDedicatedNR_r16__ext0__cond := SL_ConfigDedicatedNR_r16__ext0O__cond.

Record SL_ConfigDedicatedNR_r16__Type : Set :=
  make__SL_ConfigDedicatedNR_r16__Type {
    SL_ConfigDedicatedNR_r16__sl_PHY_MAC_RLC_Config_r16 : option SL_PHY_MAC_RLC_Config_r16__Type ;
    SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16 : option SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Type ;
    SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16 : option SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Type ;
    SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16 : option SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Type ;
    SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16 : option SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Type ;
    SL_ConfigDedicatedNR_r16__t400_r16 : option SL_ConfigDedicatedNR_r16__t400_r16__Type ;
    SL_ConfigDedicatedNR_r16__ext0 : option SL_ConfigDedicatedNR_r16__ext0__Type ;
}.
Definition SL_ConfigDedicatedNR_r16__root_list : list seq_elem := (
 Opt SL_PHY_MAC_RLC_Config_r16__Type SL_PHY_MAC_RLC_Config_r16__cond ::
 Opt SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Type SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__cond ::
 Opt SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Type SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__cond ::
 Opt SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Type SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__cond ::
 Opt SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Type SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__cond ::
 Opt SL_ConfigDedicatedNR_r16__t400_r16__Type SL_ConfigDedicatedNR_r16__t400_r16__cond ::
 nil).
Definition SL_ConfigDedicatedNR_r16__ext_list : list typ := (
  typ_cons SL_ConfigDedicatedNR_r16__ext0__Type SL_ConfigDedicatedNR_r16__ext0__cond ::
  nil).
Definition SL_ConfigDedicatedNR_r16__cond (z : SL_ConfigDedicatedNR_r16__Type) := 
(  opt_cond SL_PHY_MAC_RLC_Config_r16__cond (SL_ConfigDedicatedNR_r16__sl_PHY_MAC_RLC_Config_r16 z) /\
  opt_cond SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__cond (SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16 z) /\
  opt_cond SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__cond (SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16 z) /\
  opt_cond SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__cond (SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16 z) /\
  opt_cond SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__cond (SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16 z) /\
  opt_cond SL_ConfigDedicatedNR_r16__t400_r16__cond (SL_ConfigDedicatedNR_r16__t400_r16 z) /\
  True) /\ 
(  opt_cond SL_ConfigDedicatedNR_r16__ext0__cond (SL_ConfigDedicatedNR_r16__ext0 z) /\
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
Definition SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Format : T_Format SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Type SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__cond := seq_of_format SLRB_Uu_ConfigIndex_r16__Format 1 maxNrofSLRB_r16 SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__helper1 SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__helper2.

Opaque SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__cond SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Format : T_Format SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Type SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__cond := seq_of_format SL_RadioBearerConfig_r16__Format 1 maxNrofSLRB_r16 SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__helper1 SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__helper2.

Opaque SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__cond SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Format : T_Format SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Type SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__cond := seq_of_format SL_DestinationIndex_r16__Format 1 maxNrofSL_Dest_r16 SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__helper1 SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__helper2.

Opaque SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__cond SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Format.

Definition SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Format : T_Format SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Type SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__cond := seq_of_format SL_MeasConfigInfo_r16__Format 1 maxNrofSL_Dest_r16 SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__helper1 SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__helper2.

Opaque SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__cond SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Format.

Definition SL_ConfigDedicatedNR_r16__t400_r16__Format : T_Format SL_ConfigDedicatedNR_r16__t400_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ConfigDedicatedNR_r16__t400_r16__nat__Format SL_ConfigDedicatedNR_r16__t400_r16__F1 SL_ConfigDedicatedNR_r16__t400_r16__F2 SL_ConfigDedicatedNR_r16__t400_r16__F1F2 SL_ConfigDedicatedNR_r16__t400_r16__F2F1.

Opaque SL_ConfigDedicatedNR_r16__t400_r16__cond SL_ConfigDedicatedNR_r16__t400_r16__Format.

Opaque SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__cond SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Format.

Opaque SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__cond SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Format.


Definition SL_ConfigDedicatedNR_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SL_ConfigDedicatedNR_r16__ext0O__list.
Definition SL_ConfigDedicatedNR_r16__ext0O__Format_list : SL_ConfigDedicatedNR_r16__ext0O__Format_Type :=
  (SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700__Format, (SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17__Format, unit_format)).
Definition SL_ConfigDedicatedNR_r16__ext0O__list__Format := (*Eval compute in *) seq_format SL_ConfigDedicatedNR_r16__ext0O__list SL_ConfigDedicatedNR_r16__ext0O__Format_list.
Definition SL_ConfigDedicatedNR_r16__ext0O__F1 z :=
  (SL_ConfigDedicatedNR_r16__ext0O__sl_PHY_MAC_RLC_Config_v1700 z, (SL_ConfigDedicatedNR_r16__ext0O__sl_DiscConfig_r17 z, tt)).
Definition SL_ConfigDedicatedNR_r16__ext0O__F2 (y : seq_type SL_ConfigDedicatedNR_r16__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SL_ConfigDedicatedNR_r16__ext0O__Type i0 i1
  end.
Lemma SL_ConfigDedicatedNR_r16__ext0O__F1F2_cond (z : SL_ConfigDedicatedNR_r16__ext0O__Type)
  : SL_ConfigDedicatedNR_r16__ext0O__cond z ->
  (seq_cond SL_ConfigDedicatedNR_r16__ext0O__list (SL_ConfigDedicatedNR_r16__ext0O__F1 z)).
intro H. unfold SL_ConfigDedicatedNR_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SL_ConfigDedicatedNR_r16__ext0O__F1F2_cond2 (z : SL_ConfigDedicatedNR_r16__ext0O__Type)
 : SL_ConfigDedicatedNR_r16__ext0O__F2 (SL_ConfigDedicatedNR_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ConfigDedicatedNR_r16__ext0O__F2F1_cond (y : seq_type SL_ConfigDedicatedNR_r16__ext0O__list)
  : seq_cond SL_ConfigDedicatedNR_r16__ext0O__list y ->
 (SL_ConfigDedicatedNR_r16__ext0O__cond (SL_ConfigDedicatedNR_r16__ext0O__F2 y)) /\  SL_ConfigDedicatedNR_r16__ext0O__F1 (SL_ConfigDedicatedNR_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ConfigDedicatedNR_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SL_ConfigDedicatedNR_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ConfigDedicatedNR_r16__ext0O__Format : T_Format SL_ConfigDedicatedNR_r16__ext0O__Type SL_ConfigDedicatedNR_r16__ext0O__cond :=
        proj2_format  SL_ConfigDedicatedNR_r16__ext0O__cond SL_ConfigDedicatedNR_r16__ext0O__list__Format
    SL_ConfigDedicatedNR_r16__ext0O__F1 SL_ConfigDedicatedNR_r16__ext0O__F2 SL_ConfigDedicatedNR_r16__ext0O__F1F2_cond  SL_ConfigDedicatedNR_r16__ext0O__F1F2_cond2 SL_ConfigDedicatedNR_r16__ext0O__F2F1_cond.
Opaque SL_ConfigDedicatedNR_r16__ext0O__cond SL_ConfigDedicatedNR_r16__ext0O__Format.

Definition SL_ConfigDedicatedNR_r16__ext0__check_all_none (b : SL_ConfigDedicatedNR_r16__ext0O__Type) : bool :=
match b with 
  | make__SL_ConfigDedicatedNR_r16__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition SL_ConfigDedicatedNR_r16__ext0__Format : T_Format SL_ConfigDedicatedNR_r16__ext0__Type SL_ConfigDedicatedNR_r16__ext0__cond :=
  restrict_add_format SL_ConfigDedicatedNR_r16__ext0__check_all_none SL_ConfigDedicatedNR_r16__ext0O__Format.

Opaque SL_ConfigDedicatedNR_r16__ext0__cond SL_ConfigDedicatedNR_r16__ext0__Format.


Definition SL_ConfigDedicatedNR_r16__root_Format_Type := Eval cbn in seq_format_prod SL_ConfigDedicatedNR_r16__root_list.
Definition SL_ConfigDedicatedNR_r16__root_Format_list : SL_ConfigDedicatedNR_r16__root_Format_Type :=
  (SL_PHY_MAC_RLC_Config_r16__Format, (SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16__Format, (SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16__Format, (SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16__Format, (SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16__Format, (SL_ConfigDedicatedNR_r16__t400_r16__Format, unit_format)))))).

Definition SL_ConfigDedicatedNR_r16__ext_Format_Type := Eval cbn in get_formats SL_ConfigDedicatedNR_r16__ext_list.
Definition SL_ConfigDedicatedNR_r16__ext_Format_list : SL_ConfigDedicatedNR_r16__ext_Format_Type :=
  (SL_ConfigDedicatedNR_r16__ext0__Format, unit__Format).

Definition SL_ConfigDedicatedNR_r16__list_type : Set := (seq_type SL_ConfigDedicatedNR_r16__root_list) * (seq_ext_type SL_ConfigDedicatedNR_r16__ext_list).
Definition SL_ConfigDedicatedNR_r16__list_cond (z : SL_ConfigDedicatedNR_r16__list_type) : Prop :=
        (seq_cond SL_ConfigDedicatedNR_r16__root_list (fst z)) /\ (seq_ext_cond SL_ConfigDedicatedNR_r16__ext_list (snd z)).
Definition SL_ConfigDedicatedNR_r16__list_format : T_Format SL_ConfigDedicatedNR_r16__list_type SL_ConfigDedicatedNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_ConfigDedicatedNR_r16__root_list SL_ConfigDedicatedNR_r16__root_Format_list SL_ConfigDedicatedNR_r16__ext_list SL_ConfigDedicatedNR_r16__ext_Format_list.

Opaque SL_ConfigDedicatedNR_r16__list_format.
Definition SL_ConfigDedicatedNR_r16__F1 (z : SL_ConfigDedicatedNR_r16__Type) : SL_ConfigDedicatedNR_r16__list_type :=
  (((SL_ConfigDedicatedNR_r16__sl_PHY_MAC_RLC_Config_r16 z, (SL_ConfigDedicatedNR_r16__sl_RadioBearerToReleaseList_r16 z, (SL_ConfigDedicatedNR_r16__sl_RadioBearerToAddModList_r16 z, (SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToReleaseList_r16 z, (SL_ConfigDedicatedNR_r16__sl_MeasConfigInfoToAddModList_r16 z, (SL_ConfigDedicatedNR_r16__t400_r16 z, tt))))))), (
(SL_ConfigDedicatedNR_r16__ext0 z, tt))).
Definition SL_ConfigDedicatedNR_r16__F2 (y : SL_ConfigDedicatedNR_r16__list_type) : SL_ConfigDedicatedNR_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__SL_ConfigDedicatedNR_r16__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition SL_ConfigDedicatedNR_r16__helper1 : (forall a : SL_ConfigDedicatedNR_r16__Type, SL_ConfigDedicatedNR_r16__cond a -> SL_ConfigDedicatedNR_r16__list_cond (SL_ConfigDedicatedNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_ConfigDedicatedNR_r16__helper2 : (forall a : SL_ConfigDedicatedNR_r16__Type, SL_ConfigDedicatedNR_r16__F2 (SL_ConfigDedicatedNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_ConfigDedicatedNR_r16__helper3 : (forall b : SL_ConfigDedicatedNR_r16__list_type, SL_ConfigDedicatedNR_r16__list_cond b -> SL_ConfigDedicatedNR_r16__cond (SL_ConfigDedicatedNR_r16__F2 b) /\ SL_ConfigDedicatedNR_r16__F1 (SL_ConfigDedicatedNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_ConfigDedicatedNR_r16__cond, SL_ConfigDedicatedNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_ConfigDedicatedNR_r16__Format : T_Format SL_ConfigDedicatedNR_r16__Type SL_ConfigDedicatedNR_r16__cond :=
 proj2_format SL_ConfigDedicatedNR_r16__cond SL_ConfigDedicatedNR_r16__list_format  SL_ConfigDedicatedNR_r16__F1 SL_ConfigDedicatedNR_r16__F2 SL_ConfigDedicatedNR_r16__helper1 SL_ConfigDedicatedNR_r16__helper2 SL_ConfigDedicatedNR_r16__helper3.

Opaque SL_ConfigDedicatedNR_r16__cond SL_ConfigDedicatedNR_r16__Format.

