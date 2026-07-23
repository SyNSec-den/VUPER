Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EpochTime_r17.

Opaque EpochTime_r17__cond EpochTime_r17__Format.

Inductive NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Type : Set :=
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s5
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s10
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s15
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s20
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s25
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s30
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s35
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s40
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s45
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s50
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s55
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s60
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s120
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s180
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s240
 | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s900
.
Definition NTN_Config_r17__ntn_UlSyncValidityDuration_r17__cond := (fun (_ : NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Type) => True).
Lemma NTN_Config_r17__ntn_UlSyncValidityDuration_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Config_r17__ntn_UlSyncValidityDuration_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 NTN_Config_r17__ntn_UlSyncValidityDuration_r17__nat__helper.

Definition NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1 t :=
  match t with
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s5 => 0
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s10 => 1
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s15 => 2
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s20 => 3
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s25 => 4
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s30 => 5
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s35 => 6
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s40 => 7
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s45 => 8
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s50 => 9
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s55 => 10
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s60 => 11
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s120 => 12
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s180 => 13
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s240 => 14
  | NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s900 => 15
  end.
Definition NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F2 n :=
  match n with
  | 0 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s5
  | 1 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s10
  | 2 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s15
  | 3 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s20
  | 4 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s25
  | 5 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s30
  | 6 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s35
  | 7 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s40
  | 8 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s45
  | 9 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s50
  | 10 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s55
  | 11 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s60
  | 12 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s120
  | 13 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s180
  | 14 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s240
  | 15 => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s900
  | _ => NTN_Config_r17__ntn_UlSyncValidityDuration_r17__s5
  end.
Lemma NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1F2 : forall x : NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Type, (NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1 x <= 15) /\ NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F2 (NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F2F1 : forall (y : nat) (H : y <= 15), NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1 (NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F2 y) = y. enum_solve H y. Qed.

Lemma NTN_Config_r17__cellSpecificKoffset_r17__helper1 : (1 <= 1023)%Z.  lia. Qed.
Lemma NTN_Config_r17__cellSpecificKoffset_r17__helper2 : to_bit_sz (Z.to_nat (1023 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NTN_Config_r17__cellSpecificKoffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NTN_Config_r17__cellSpecificKoffset_r17__Type := Z.
Definition NTN_Config_r17__cellSpecificKoffset_r17__cond := (fun z => (1 <= z <= 1023)%Z).
Lemma NTN_Config_r17__kmac_r17__helper1 : (1 <= 512)%Z.  lia. Qed.
Lemma NTN_Config_r17__kmac_r17__helper2 : to_bit_sz (Z.to_nat (512 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (512 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NTN_Config_r17__kmac_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NTN_Config_r17__kmac_r17__Type := Z.
Definition NTN_Config_r17__kmac_r17__cond := (fun z => (1 <= z <= 512)%Z).
Require Import NR.TA_Info_r17.

Opaque TA_Info_r17__cond TA_Info_r17__Format.

Inductive NTN_Config_r17__ntn_PolarizationDL_r17__Type : Set :=
 | NTN_Config_r17__ntn_PolarizationDL_r17__rhcp
 | NTN_Config_r17__ntn_PolarizationDL_r17__lhcp
 | NTN_Config_r17__ntn_PolarizationDL_r17__linear
.
Definition NTN_Config_r17__ntn_PolarizationDL_r17__cond := (fun (_ : NTN_Config_r17__ntn_PolarizationDL_r17__Type) => True).
Lemma NTN_Config_r17__ntn_PolarizationDL_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Config_r17__ntn_PolarizationDL_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 NTN_Config_r17__ntn_PolarizationDL_r17__nat__helper.

Definition NTN_Config_r17__ntn_PolarizationDL_r17__F1 t :=
  match t with
  | NTN_Config_r17__ntn_PolarizationDL_r17__rhcp => 0
  | NTN_Config_r17__ntn_PolarizationDL_r17__lhcp => 1
  | NTN_Config_r17__ntn_PolarizationDL_r17__linear => 2
  end.
Definition NTN_Config_r17__ntn_PolarizationDL_r17__F2 n :=
  match n with
  | 0 => NTN_Config_r17__ntn_PolarizationDL_r17__rhcp
  | 1 => NTN_Config_r17__ntn_PolarizationDL_r17__lhcp
  | 2 => NTN_Config_r17__ntn_PolarizationDL_r17__linear
  | _ => NTN_Config_r17__ntn_PolarizationDL_r17__rhcp
  end.
Lemma NTN_Config_r17__ntn_PolarizationDL_r17__F1F2 : forall x : NTN_Config_r17__ntn_PolarizationDL_r17__Type, (NTN_Config_r17__ntn_PolarizationDL_r17__F1 x <= 2) /\ NTN_Config_r17__ntn_PolarizationDL_r17__F2 (NTN_Config_r17__ntn_PolarizationDL_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Config_r17__ntn_PolarizationDL_r17__F2F1 : forall (y : nat) (H : y <= 2), NTN_Config_r17__ntn_PolarizationDL_r17__F1 (NTN_Config_r17__ntn_PolarizationDL_r17__F2 y) = y. enum_solve H y. Qed.

Inductive NTN_Config_r17__ntn_PolarizationUL_r17__Type : Set :=
 | NTN_Config_r17__ntn_PolarizationUL_r17__rhcp
 | NTN_Config_r17__ntn_PolarizationUL_r17__lhcp
 | NTN_Config_r17__ntn_PolarizationUL_r17__linear
.
Definition NTN_Config_r17__ntn_PolarizationUL_r17__cond := (fun (_ : NTN_Config_r17__ntn_PolarizationUL_r17__Type) => True).
Lemma NTN_Config_r17__ntn_PolarizationUL_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Config_r17__ntn_PolarizationUL_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 NTN_Config_r17__ntn_PolarizationUL_r17__nat__helper.

Definition NTN_Config_r17__ntn_PolarizationUL_r17__F1 t :=
  match t with
  | NTN_Config_r17__ntn_PolarizationUL_r17__rhcp => 0
  | NTN_Config_r17__ntn_PolarizationUL_r17__lhcp => 1
  | NTN_Config_r17__ntn_PolarizationUL_r17__linear => 2
  end.
Definition NTN_Config_r17__ntn_PolarizationUL_r17__F2 n :=
  match n with
  | 0 => NTN_Config_r17__ntn_PolarizationUL_r17__rhcp
  | 1 => NTN_Config_r17__ntn_PolarizationUL_r17__lhcp
  | 2 => NTN_Config_r17__ntn_PolarizationUL_r17__linear
  | _ => NTN_Config_r17__ntn_PolarizationUL_r17__rhcp
  end.
Lemma NTN_Config_r17__ntn_PolarizationUL_r17__F1F2 : forall x : NTN_Config_r17__ntn_PolarizationUL_r17__Type, (NTN_Config_r17__ntn_PolarizationUL_r17__F1 x <= 2) /\ NTN_Config_r17__ntn_PolarizationUL_r17__F2 (NTN_Config_r17__ntn_PolarizationUL_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Config_r17__ntn_PolarizationUL_r17__F2F1 : forall (y : nat) (H : y <= 2), NTN_Config_r17__ntn_PolarizationUL_r17__F1 (NTN_Config_r17__ntn_PolarizationUL_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.EphemerisInfo_r17.

Opaque EphemerisInfo_r17__cond EphemerisInfo_r17__Format.

Inductive NTN_Config_r17__ta_Report_r17__Type : Set :=
 | NTN_Config_r17__ta_Report_r17__enabled
.
Definition NTN_Config_r17__ta_Report_r17__cond := (fun (_ : NTN_Config_r17__ta_Report_r17__Type) => True).
Lemma NTN_Config_r17__ta_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Config_r17__ta_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NTN_Config_r17__ta_Report_r17__nat__helper.

Definition NTN_Config_r17__ta_Report_r17__F1 t :=
  match t with
  | NTN_Config_r17__ta_Report_r17__enabled => 0
  end.
Definition NTN_Config_r17__ta_Report_r17__F2 n :=
  match n with
  | 0 => NTN_Config_r17__ta_Report_r17__enabled
  | _ => NTN_Config_r17__ta_Report_r17__enabled
  end.
Lemma NTN_Config_r17__ta_Report_r17__F1F2 : forall x : NTN_Config_r17__ta_Report_r17__Type, (NTN_Config_r17__ta_Report_r17__F1 x <= 0) /\ NTN_Config_r17__ta_Report_r17__F2 (NTN_Config_r17__ta_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Config_r17__ta_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), NTN_Config_r17__ta_Report_r17__F1 (NTN_Config_r17__ta_Report_r17__F2 y) = y. enum_solve H y. Qed.

Record NTN_Config_r17__Type : Set :=
  make__NTN_Config_r17__Type {
    NTN_Config_r17__epochTime_r17 : option EpochTime_r17__Type ;
    NTN_Config_r17__ntn_UlSyncValidityDuration_r17 : option NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Type ;
    NTN_Config_r17__cellSpecificKoffset_r17 : option Z ;
    NTN_Config_r17__kmac_r17 : option Z ;
    NTN_Config_r17__ta_Info_r17 : option TA_Info_r17__Type ;
    NTN_Config_r17__ntn_PolarizationDL_r17 : option NTN_Config_r17__ntn_PolarizationDL_r17__Type ;
    NTN_Config_r17__ntn_PolarizationUL_r17 : option NTN_Config_r17__ntn_PolarizationUL_r17__Type ;
    NTN_Config_r17__ephemerisInfo_r17 : option EphemerisInfo_r17__Type ;
    NTN_Config_r17__ta_Report_r17 : option NTN_Config_r17__ta_Report_r17__Type ;
}.
Definition NTN_Config_r17__root_list : list seq_elem := (
 Opt EpochTime_r17__Type EpochTime_r17__cond ::
 Opt NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Type NTN_Config_r17__ntn_UlSyncValidityDuration_r17__cond ::
 Opt Z NTN_Config_r17__cellSpecificKoffset_r17__cond ::
 Opt Z NTN_Config_r17__kmac_r17__cond ::
 Opt TA_Info_r17__Type TA_Info_r17__cond ::
 Opt NTN_Config_r17__ntn_PolarizationDL_r17__Type NTN_Config_r17__ntn_PolarizationDL_r17__cond ::
 Opt NTN_Config_r17__ntn_PolarizationUL_r17__Type NTN_Config_r17__ntn_PolarizationUL_r17__cond ::
 Opt EphemerisInfo_r17__Type EphemerisInfo_r17__cond ::
 Opt NTN_Config_r17__ta_Report_r17__Type NTN_Config_r17__ta_Report_r17__cond ::
 nil).
Definition NTN_Config_r17__ext_list : list typ := (
  nil).
Definition NTN_Config_r17__cond (z : NTN_Config_r17__Type) := 
(  opt_cond EpochTime_r17__cond (NTN_Config_r17__epochTime_r17 z) /\
  opt_cond NTN_Config_r17__ntn_UlSyncValidityDuration_r17__cond (NTN_Config_r17__ntn_UlSyncValidityDuration_r17 z) /\
  opt_cond NTN_Config_r17__cellSpecificKoffset_r17__cond (NTN_Config_r17__cellSpecificKoffset_r17 z) /\
  opt_cond NTN_Config_r17__kmac_r17__cond (NTN_Config_r17__kmac_r17 z) /\
  opt_cond TA_Info_r17__cond (NTN_Config_r17__ta_Info_r17 z) /\
  opt_cond NTN_Config_r17__ntn_PolarizationDL_r17__cond (NTN_Config_r17__ntn_PolarizationDL_r17 z) /\
  opt_cond NTN_Config_r17__ntn_PolarizationUL_r17__cond (NTN_Config_r17__ntn_PolarizationUL_r17 z) /\
  opt_cond EphemerisInfo_r17__cond (NTN_Config_r17__ephemerisInfo_r17 z) /\
  opt_cond NTN_Config_r17__ta_Report_r17__cond (NTN_Config_r17__ta_Report_r17 z) /\
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
Definition NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Format : T_Format NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Config_r17__ntn_UlSyncValidityDuration_r17__nat__Format NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1 NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F2 NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F1F2 NTN_Config_r17__ntn_UlSyncValidityDuration_r17__F2F1.

Opaque NTN_Config_r17__ntn_UlSyncValidityDuration_r17__cond NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Format.

Definition NTN_Config_r17__cellSpecificKoffset_r17__Format : T_Format Z NTN_Config_r17__cellSpecificKoffset_r17__cond :=
 ranged_int_format (1) (1023) NTN_Config_r17__cellSpecificKoffset_r17__helper1 NTN_Config_r17__cellSpecificKoffset_r17__helper2.

Opaque NTN_Config_r17__cellSpecificKoffset_r17__cond NTN_Config_r17__cellSpecificKoffset_r17__Format.

Definition NTN_Config_r17__kmac_r17__Format : T_Format Z NTN_Config_r17__kmac_r17__cond :=
 ranged_int_format (1) (512) NTN_Config_r17__kmac_r17__helper1 NTN_Config_r17__kmac_r17__helper2.

Opaque NTN_Config_r17__kmac_r17__cond NTN_Config_r17__kmac_r17__Format.

Definition NTN_Config_r17__ntn_PolarizationDL_r17__Format : T_Format NTN_Config_r17__ntn_PolarizationDL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Config_r17__ntn_PolarizationDL_r17__nat__Format NTN_Config_r17__ntn_PolarizationDL_r17__F1 NTN_Config_r17__ntn_PolarizationDL_r17__F2 NTN_Config_r17__ntn_PolarizationDL_r17__F1F2 NTN_Config_r17__ntn_PolarizationDL_r17__F2F1.

Opaque NTN_Config_r17__ntn_PolarizationDL_r17__cond NTN_Config_r17__ntn_PolarizationDL_r17__Format.

Definition NTN_Config_r17__ntn_PolarizationUL_r17__Format : T_Format NTN_Config_r17__ntn_PolarizationUL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Config_r17__ntn_PolarizationUL_r17__nat__Format NTN_Config_r17__ntn_PolarizationUL_r17__F1 NTN_Config_r17__ntn_PolarizationUL_r17__F2 NTN_Config_r17__ntn_PolarizationUL_r17__F1F2 NTN_Config_r17__ntn_PolarizationUL_r17__F2F1.

Opaque NTN_Config_r17__ntn_PolarizationUL_r17__cond NTN_Config_r17__ntn_PolarizationUL_r17__Format.

Definition NTN_Config_r17__ta_Report_r17__Format : T_Format NTN_Config_r17__ta_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Config_r17__ta_Report_r17__nat__Format NTN_Config_r17__ta_Report_r17__F1 NTN_Config_r17__ta_Report_r17__F2 NTN_Config_r17__ta_Report_r17__F1F2 NTN_Config_r17__ta_Report_r17__F2F1.

Opaque NTN_Config_r17__ta_Report_r17__cond NTN_Config_r17__ta_Report_r17__Format.


Definition NTN_Config_r17__root_Format_Type := Eval cbn in seq_format_prod NTN_Config_r17__root_list.
Definition NTN_Config_r17__root_Format_list : NTN_Config_r17__root_Format_Type :=
  (EpochTime_r17__Format, (NTN_Config_r17__ntn_UlSyncValidityDuration_r17__Format, (NTN_Config_r17__cellSpecificKoffset_r17__Format, (NTN_Config_r17__kmac_r17__Format, (TA_Info_r17__Format, (NTN_Config_r17__ntn_PolarizationDL_r17__Format, (NTN_Config_r17__ntn_PolarizationUL_r17__Format, (EphemerisInfo_r17__Format, (NTN_Config_r17__ta_Report_r17__Format, unit_format))))))))).

Definition NTN_Config_r17__ext_Format_Type := Eval cbn in get_formats NTN_Config_r17__ext_list.
Definition NTN_Config_r17__ext_Format_list : NTN_Config_r17__ext_Format_Type :=
  unit__Format.

Definition NTN_Config_r17__list_type : Set := (seq_type NTN_Config_r17__root_list) * (seq_ext_type NTN_Config_r17__ext_list).
Definition NTN_Config_r17__list_cond (z : NTN_Config_r17__list_type) : Prop :=
        (seq_cond NTN_Config_r17__root_list (fst z)) /\ (seq_ext_cond NTN_Config_r17__ext_list (snd z)).
Definition NTN_Config_r17__list_format : T_Format NTN_Config_r17__list_type NTN_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format NTN_Config_r17__root_list NTN_Config_r17__root_Format_list NTN_Config_r17__ext_list NTN_Config_r17__ext_Format_list.

Opaque NTN_Config_r17__list_format.
Definition NTN_Config_r17__F1 (z : NTN_Config_r17__Type) : NTN_Config_r17__list_type :=
  (((NTN_Config_r17__epochTime_r17 z, (NTN_Config_r17__ntn_UlSyncValidityDuration_r17 z, (NTN_Config_r17__cellSpecificKoffset_r17 z, (NTN_Config_r17__kmac_r17 z, (NTN_Config_r17__ta_Info_r17 z, (NTN_Config_r17__ntn_PolarizationDL_r17 z, (NTN_Config_r17__ntn_PolarizationUL_r17 z, (NTN_Config_r17__ephemerisInfo_r17 z, (NTN_Config_r17__ta_Report_r17 z, tt)))))))))), (
tt)).
Definition NTN_Config_r17__F2 (y : NTN_Config_r17__list_type) : NTN_Config_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__NTN_Config_r17__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition NTN_Config_r17__helper1 : (forall a : NTN_Config_r17__Type, NTN_Config_r17__cond a -> NTN_Config_r17__list_cond (NTN_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NTN_Config_r17__helper2 : (forall a : NTN_Config_r17__Type, NTN_Config_r17__F2 (NTN_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NTN_Config_r17__helper3 : (forall b : NTN_Config_r17__list_type, NTN_Config_r17__list_cond b -> NTN_Config_r17__cond (NTN_Config_r17__F2 b) /\ NTN_Config_r17__F1 (NTN_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NTN_Config_r17__cond, NTN_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NTN_Config_r17__Format : T_Format NTN_Config_r17__Type NTN_Config_r17__cond :=
 proj2_format NTN_Config_r17__cond NTN_Config_r17__list_format  NTN_Config_r17__F1 NTN_Config_r17__F2 NTN_Config_r17__helper1 NTN_Config_r17__helper2 NTN_Config_r17__helper3.

Opaque NTN_Config_r17__cond NTN_Config_r17__Format.

