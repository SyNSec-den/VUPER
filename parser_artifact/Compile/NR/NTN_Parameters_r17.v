Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive NTN_Parameters_r17__inactiveStateNTN_r17__Type : Set :=
 | NTN_Parameters_r17__inactiveStateNTN_r17__supported
.
Definition NTN_Parameters_r17__inactiveStateNTN_r17__cond := (fun (_ : NTN_Parameters_r17__inactiveStateNTN_r17__Type) => True).
Lemma NTN_Parameters_r17__inactiveStateNTN_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Parameters_r17__inactiveStateNTN_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NTN_Parameters_r17__inactiveStateNTN_r17__nat__helper.

Definition NTN_Parameters_r17__inactiveStateNTN_r17__F1 t :=
  match t with
  | NTN_Parameters_r17__inactiveStateNTN_r17__supported => 0
  end.
Definition NTN_Parameters_r17__inactiveStateNTN_r17__F2 n :=
  match n with
  | 0 => NTN_Parameters_r17__inactiveStateNTN_r17__supported
  | _ => NTN_Parameters_r17__inactiveStateNTN_r17__supported
  end.
Lemma NTN_Parameters_r17__inactiveStateNTN_r17__F1F2 : forall x : NTN_Parameters_r17__inactiveStateNTN_r17__Type, (NTN_Parameters_r17__inactiveStateNTN_r17__F1 x <= 0) /\ NTN_Parameters_r17__inactiveStateNTN_r17__F2 (NTN_Parameters_r17__inactiveStateNTN_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Parameters_r17__inactiveStateNTN_r17__F2F1 : forall (y : nat) (H : y <= 0), NTN_Parameters_r17__inactiveStateNTN_r17__F1 (NTN_Parameters_r17__inactiveStateNTN_r17__F2 y) = y. enum_solve H y. Qed.

Inductive NTN_Parameters_r17__ra_SDT_NTN_r17__Type : Set :=
 | NTN_Parameters_r17__ra_SDT_NTN_r17__supported
.
Definition NTN_Parameters_r17__ra_SDT_NTN_r17__cond := (fun (_ : NTN_Parameters_r17__ra_SDT_NTN_r17__Type) => True).
Lemma NTN_Parameters_r17__ra_SDT_NTN_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Parameters_r17__ra_SDT_NTN_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NTN_Parameters_r17__ra_SDT_NTN_r17__nat__helper.

Definition NTN_Parameters_r17__ra_SDT_NTN_r17__F1 t :=
  match t with
  | NTN_Parameters_r17__ra_SDT_NTN_r17__supported => 0
  end.
Definition NTN_Parameters_r17__ra_SDT_NTN_r17__F2 n :=
  match n with
  | 0 => NTN_Parameters_r17__ra_SDT_NTN_r17__supported
  | _ => NTN_Parameters_r17__ra_SDT_NTN_r17__supported
  end.
Lemma NTN_Parameters_r17__ra_SDT_NTN_r17__F1F2 : forall x : NTN_Parameters_r17__ra_SDT_NTN_r17__Type, (NTN_Parameters_r17__ra_SDT_NTN_r17__F1 x <= 0) /\ NTN_Parameters_r17__ra_SDT_NTN_r17__F2 (NTN_Parameters_r17__ra_SDT_NTN_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Parameters_r17__ra_SDT_NTN_r17__F2F1 : forall (y : nat) (H : y <= 0), NTN_Parameters_r17__ra_SDT_NTN_r17__F1 (NTN_Parameters_r17__ra_SDT_NTN_r17__F2 y) = y. enum_solve H y. Qed.

Inductive NTN_Parameters_r17__srb_SDT_NTN_r17__Type : Set :=
 | NTN_Parameters_r17__srb_SDT_NTN_r17__supported
.
Definition NTN_Parameters_r17__srb_SDT_NTN_r17__cond := (fun (_ : NTN_Parameters_r17__srb_SDT_NTN_r17__Type) => True).
Lemma NTN_Parameters_r17__srb_SDT_NTN_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NTN_Parameters_r17__srb_SDT_NTN_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NTN_Parameters_r17__srb_SDT_NTN_r17__nat__helper.

Definition NTN_Parameters_r17__srb_SDT_NTN_r17__F1 t :=
  match t with
  | NTN_Parameters_r17__srb_SDT_NTN_r17__supported => 0
  end.
Definition NTN_Parameters_r17__srb_SDT_NTN_r17__F2 n :=
  match n with
  | 0 => NTN_Parameters_r17__srb_SDT_NTN_r17__supported
  | _ => NTN_Parameters_r17__srb_SDT_NTN_r17__supported
  end.
Lemma NTN_Parameters_r17__srb_SDT_NTN_r17__F1F2 : forall x : NTN_Parameters_r17__srb_SDT_NTN_r17__Type, (NTN_Parameters_r17__srb_SDT_NTN_r17__F1 x <= 0) /\ NTN_Parameters_r17__srb_SDT_NTN_r17__F2 (NTN_Parameters_r17__srb_SDT_NTN_r17__F1 x) = x. imp_solve. Qed.
Lemma NTN_Parameters_r17__srb_SDT_NTN_r17__F2F1 : forall (y : nat) (H : y <= 0), NTN_Parameters_r17__srb_SDT_NTN_r17__F1 (NTN_Parameters_r17__srb_SDT_NTN_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasAndMobParameters.

Opaque MeasAndMobParameters__cond MeasAndMobParameters__Format.

Require Import NR.MAC_Parameters.

Opaque MAC_Parameters__cond MAC_Parameters__Format.

Require Import NR.Phy_Parameters.

Opaque Phy_Parameters__cond Phy_Parameters__Format.

Require Import NR.UE_NR_CapabilityAddXDD_Mode.

Opaque UE_NR_CapabilityAddXDD_Mode__cond UE_NR_CapabilityAddXDD_Mode__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode.

Opaque UE_NR_CapabilityAddFRX_Mode__cond UE_NR_CapabilityAddFRX_Mode__Format.

Require Import NR.UE_BasedPerfMeas_Parameters_r16.

Opaque UE_BasedPerfMeas_Parameters_r16__cond UE_BasedPerfMeas_Parameters_r16__Format.

Require Import NR.SON_Parameters_r16.

Opaque SON_Parameters_r16__cond SON_Parameters_r16__Format.

Record NTN_Parameters_r17__Type : Set :=
  make__NTN_Parameters_r17__Type {
    NTN_Parameters_r17__inactiveStateNTN_r17 : option NTN_Parameters_r17__inactiveStateNTN_r17__Type ;
    NTN_Parameters_r17__ra_SDT_NTN_r17 : option NTN_Parameters_r17__ra_SDT_NTN_r17__Type ;
    NTN_Parameters_r17__srb_SDT_NTN_r17 : option NTN_Parameters_r17__srb_SDT_NTN_r17__Type ;
    NTN_Parameters_r17__measAndMobParametersNTN_r17 : option MeasAndMobParameters__Type ;
    NTN_Parameters_r17__mac_ParametersNTN_r17 : option MAC_Parameters__Type ;
    NTN_Parameters_r17__phy_ParametersNTN_r17 : option Phy_Parameters__Type ;
    NTN_Parameters_r17__fdd_Add_UE_NR_CapabilitiesNTN_r17 : option UE_NR_CapabilityAddXDD_Mode__Type ;
    NTN_Parameters_r17__fr1_Add_UE_NR_CapabilitiesNTN_r17 : option UE_NR_CapabilityAddFRX_Mode__Type ;
    NTN_Parameters_r17__ue_BasedPerfMeas_ParametersNTN_r17 : option UE_BasedPerfMeas_Parameters_r16__Type ;
    NTN_Parameters_r17__son_ParametersNTN_r17 : option SON_Parameters_r16__Type ;
}.
Definition NTN_Parameters_r17__list := (
 Opt NTN_Parameters_r17__inactiveStateNTN_r17__Type NTN_Parameters_r17__inactiveStateNTN_r17__cond ::
 Opt NTN_Parameters_r17__ra_SDT_NTN_r17__Type NTN_Parameters_r17__ra_SDT_NTN_r17__cond ::
 Opt NTN_Parameters_r17__srb_SDT_NTN_r17__Type NTN_Parameters_r17__srb_SDT_NTN_r17__cond ::
 Opt MeasAndMobParameters__Type MeasAndMobParameters__cond ::
 Opt MAC_Parameters__Type MAC_Parameters__cond ::
 Opt Phy_Parameters__Type Phy_Parameters__cond ::
 Opt UE_NR_CapabilityAddXDD_Mode__Type UE_NR_CapabilityAddXDD_Mode__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode__Type UE_NR_CapabilityAddFRX_Mode__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__Type UE_BasedPerfMeas_Parameters_r16__cond ::
 Opt SON_Parameters_r16__Type SON_Parameters_r16__cond ::
 nil).
Definition NTN_Parameters_r17__cond z := 
  opt_cond NTN_Parameters_r17__inactiveStateNTN_r17__cond (NTN_Parameters_r17__inactiveStateNTN_r17 z) /\
  opt_cond NTN_Parameters_r17__ra_SDT_NTN_r17__cond (NTN_Parameters_r17__ra_SDT_NTN_r17 z) /\
  opt_cond NTN_Parameters_r17__srb_SDT_NTN_r17__cond (NTN_Parameters_r17__srb_SDT_NTN_r17 z) /\
  opt_cond MeasAndMobParameters__cond (NTN_Parameters_r17__measAndMobParametersNTN_r17 z) /\
  opt_cond MAC_Parameters__cond (NTN_Parameters_r17__mac_ParametersNTN_r17 z) /\
  opt_cond Phy_Parameters__cond (NTN_Parameters_r17__phy_ParametersNTN_r17 z) /\
  opt_cond UE_NR_CapabilityAddXDD_Mode__cond (NTN_Parameters_r17__fdd_Add_UE_NR_CapabilitiesNTN_r17 z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode__cond (NTN_Parameters_r17__fr1_Add_UE_NR_CapabilitiesNTN_r17 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__cond (NTN_Parameters_r17__ue_BasedPerfMeas_ParametersNTN_r17 z) /\
  opt_cond SON_Parameters_r16__cond (NTN_Parameters_r17__son_ParametersNTN_r17 z) /\
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
Definition NTN_Parameters_r17__inactiveStateNTN_r17__Format : T_Format NTN_Parameters_r17__inactiveStateNTN_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Parameters_r17__inactiveStateNTN_r17__nat__Format NTN_Parameters_r17__inactiveStateNTN_r17__F1 NTN_Parameters_r17__inactiveStateNTN_r17__F2 NTN_Parameters_r17__inactiveStateNTN_r17__F1F2 NTN_Parameters_r17__inactiveStateNTN_r17__F2F1.

Opaque NTN_Parameters_r17__inactiveStateNTN_r17__cond NTN_Parameters_r17__inactiveStateNTN_r17__Format.

Definition NTN_Parameters_r17__ra_SDT_NTN_r17__Format : T_Format NTN_Parameters_r17__ra_SDT_NTN_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Parameters_r17__ra_SDT_NTN_r17__nat__Format NTN_Parameters_r17__ra_SDT_NTN_r17__F1 NTN_Parameters_r17__ra_SDT_NTN_r17__F2 NTN_Parameters_r17__ra_SDT_NTN_r17__F1F2 NTN_Parameters_r17__ra_SDT_NTN_r17__F2F1.

Opaque NTN_Parameters_r17__ra_SDT_NTN_r17__cond NTN_Parameters_r17__ra_SDT_NTN_r17__Format.

Definition NTN_Parameters_r17__srb_SDT_NTN_r17__Format : T_Format NTN_Parameters_r17__srb_SDT_NTN_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NTN_Parameters_r17__srb_SDT_NTN_r17__nat__Format NTN_Parameters_r17__srb_SDT_NTN_r17__F1 NTN_Parameters_r17__srb_SDT_NTN_r17__F2 NTN_Parameters_r17__srb_SDT_NTN_r17__F1F2 NTN_Parameters_r17__srb_SDT_NTN_r17__F2F1.

Opaque NTN_Parameters_r17__srb_SDT_NTN_r17__cond NTN_Parameters_r17__srb_SDT_NTN_r17__Format.


Definition NTN_Parameters_r17__Format_Type := Eval cbn in seq_format_prod NTN_Parameters_r17__list.
Definition NTN_Parameters_r17__Format_list : NTN_Parameters_r17__Format_Type :=
  (NTN_Parameters_r17__inactiveStateNTN_r17__Format, (NTN_Parameters_r17__ra_SDT_NTN_r17__Format, (NTN_Parameters_r17__srb_SDT_NTN_r17__Format, (MeasAndMobParameters__Format, (MAC_Parameters__Format, (Phy_Parameters__Format, (UE_NR_CapabilityAddXDD_Mode__Format, (UE_NR_CapabilityAddFRX_Mode__Format, (UE_BasedPerfMeas_Parameters_r16__Format, (SON_Parameters_r16__Format, unit_format)))))))))).
Definition NTN_Parameters_r17__list__Format := (*Eval compute in *) seq_format NTN_Parameters_r17__list NTN_Parameters_r17__Format_list.
Definition NTN_Parameters_r17__F1 z :=
  (NTN_Parameters_r17__inactiveStateNTN_r17 z, (NTN_Parameters_r17__ra_SDT_NTN_r17 z, (NTN_Parameters_r17__srb_SDT_NTN_r17 z, (NTN_Parameters_r17__measAndMobParametersNTN_r17 z, (NTN_Parameters_r17__mac_ParametersNTN_r17 z, (NTN_Parameters_r17__phy_ParametersNTN_r17 z, (NTN_Parameters_r17__fdd_Add_UE_NR_CapabilitiesNTN_r17 z, (NTN_Parameters_r17__fr1_Add_UE_NR_CapabilitiesNTN_r17 z, (NTN_Parameters_r17__ue_BasedPerfMeas_ParametersNTN_r17 z, (NTN_Parameters_r17__son_ParametersNTN_r17 z, tt)))))))))).
Definition NTN_Parameters_r17__F2 (y : seq_type NTN_Parameters_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__NTN_Parameters_r17__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma NTN_Parameters_r17__F1F2_cond (z : NTN_Parameters_r17__Type)
  : NTN_Parameters_r17__cond z ->
  (seq_cond NTN_Parameters_r17__list (NTN_Parameters_r17__F1 z)).
intro H. unfold NTN_Parameters_r17__cond in H. simpl. auto. Qed.
Lemma NTN_Parameters_r17__F1F2_cond2 (z : NTN_Parameters_r17__Type)
 : NTN_Parameters_r17__F2 (NTN_Parameters_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NTN_Parameters_r17__F2F1_cond (y : seq_type NTN_Parameters_r17__list)
  : seq_cond NTN_Parameters_r17__list y ->
 (NTN_Parameters_r17__cond (NTN_Parameters_r17__F2 y)) /\  NTN_Parameters_r17__F1 (NTN_Parameters_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NTN_Parameters_r17__cond. simpl in *. auto.
 - simpl. unfold NTN_Parameters_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NTN_Parameters_r17__Format : T_Format NTN_Parameters_r17__Type NTN_Parameters_r17__cond :=
        proj2_format  NTN_Parameters_r17__cond NTN_Parameters_r17__list__Format
    NTN_Parameters_r17__F1 NTN_Parameters_r17__F2 NTN_Parameters_r17__F1F2_cond  NTN_Parameters_r17__F1F2_cond2 NTN_Parameters_r17__F2F1_cond.
Opaque NTN_Parameters_r17__cond NTN_Parameters_r17__Format.

