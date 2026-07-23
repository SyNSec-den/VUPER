Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.BandCombinationInfoSN.

Opaque BandCombinationInfoSN__cond BandCombinationInfoSN__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Lemma ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__Type := Z.
Definition ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__cond := (fun z => (1 <= z <= 15)%Z).
Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Record ConfigRestrictModReqSCG__ext0O__Type : Set :=
  make__ConfigRestrictModReqSCG__ext0O__Type {
    ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG : option Z ;
    ConfigRestrictModReqSCG__ext0O__requestedP_MaxEUTRA : option P_Max__Type ;
}.
Definition ConfigRestrictModReqSCG__ext0O__list := (
 Opt Z ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__cond ::
 Opt P_Max__Type P_Max__cond ::
 nil).
Definition ConfigRestrictModReqSCG__ext0O__cond z := 
  opt_cond ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__cond (ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG z) /\
  opt_cond P_Max__cond (ConfigRestrictModReqSCG__ext0O__requestedP_MaxEUTRA z) /\
  True.

Definition ConfigRestrictModReqSCG__ext0__Type := ConfigRestrictModReqSCG__ext0O__Type.
Definition ConfigRestrictModReqSCG__ext0__cond := ConfigRestrictModReqSCG__ext0O__cond.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Lemma ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__helper1 : (1 <= maxMeasIdentitiesMN)%Z. unfold maxMeasIdentitiesMN.
 lia. Qed.
Lemma ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__helper2 : to_bit_sz (Z.to_nat (maxMeasIdentitiesMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasIdentitiesMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__Type := Z.
Definition ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__cond := (fun z => (1 <= z <= maxMeasIdentitiesMN)%Z).
Lemma ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__helper1 : (1 <= maxMeasIdentitiesMN)%Z. unfold maxMeasIdentitiesMN.
 lia. Qed.
Lemma ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__helper2 : to_bit_sz (Z.to_nat (maxMeasIdentitiesMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasIdentitiesMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__Type := Z.
Definition ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__cond := (fun z => (1 <= z <= maxMeasIdentitiesMN)%Z).
Require Import NR.T_Offset_r16.

Opaque T_Offset_r16__cond T_Offset_r16__Format.

Record ConfigRestrictModReqSCG__ext1O__Type : Set :=
  make__ConfigRestrictModReqSCG__ext1O__Type {
    ConfigRestrictModReqSCG__ext1O__requestedP_MaxFR2_r16 : option P_Max__Type ;
    ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16 : option Z ;
    ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16 : option Z ;
    ConfigRestrictModReqSCG__ext1O__requestedToffset_r16 : option T_Offset_r16__Type ;
}.
Definition ConfigRestrictModReqSCG__ext1O__list := (
 Opt P_Max__Type P_Max__cond ::
 Opt Z ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__cond ::
 Opt Z ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__cond ::
 Opt T_Offset_r16__Type T_Offset_r16__cond ::
 nil).
Definition ConfigRestrictModReqSCG__ext1O__cond z := 
  opt_cond P_Max__cond (ConfigRestrictModReqSCG__ext1O__requestedP_MaxFR2_r16 z) /\
  opt_cond ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__cond (ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16 z) /\
  opt_cond ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__cond (ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16 z) /\
  opt_cond T_Offset_r16__cond (ConfigRestrictModReqSCG__ext1O__requestedToffset_r16 z) /\
  True.

Definition ConfigRestrictModReqSCG__ext1__Type := ConfigRestrictModReqSCG__ext1O__Type.
Definition ConfigRestrictModReqSCG__ext1__cond := ConfigRestrictModReqSCG__ext1O__cond.

Record ConfigRestrictModReqSCG__Type : Set :=
  make__ConfigRestrictModReqSCG__Type {
    ConfigRestrictModReqSCG__requestedBC_MRDC : option BandCombinationInfoSN__Type ;
    ConfigRestrictModReqSCG__requestedP_MaxFR1 : option P_Max__Type ;
    ConfigRestrictModReqSCG__ext0 : option ConfigRestrictModReqSCG__ext0__Type ;
    ConfigRestrictModReqSCG__ext1 : option ConfigRestrictModReqSCG__ext1__Type ;
}.
Definition ConfigRestrictModReqSCG__root_list : list seq_elem := (
 Opt BandCombinationInfoSN__Type BandCombinationInfoSN__cond ::
 Opt P_Max__Type P_Max__cond ::
 nil).
Definition ConfigRestrictModReqSCG__ext_list : list typ := (
  typ_cons ConfigRestrictModReqSCG__ext0__Type ConfigRestrictModReqSCG__ext0__cond ::
  typ_cons ConfigRestrictModReqSCG__ext1__Type ConfigRestrictModReqSCG__ext1__cond ::
  nil).
Definition ConfigRestrictModReqSCG__cond (z : ConfigRestrictModReqSCG__Type) := 
(  opt_cond BandCombinationInfoSN__cond (ConfigRestrictModReqSCG__requestedBC_MRDC z) /\
  opt_cond P_Max__cond (ConfigRestrictModReqSCG__requestedP_MaxFR1 z) /\
  True) /\ 
(  opt_cond ConfigRestrictModReqSCG__ext0__cond (ConfigRestrictModReqSCG__ext0 z) /\
  opt_cond ConfigRestrictModReqSCG__ext1__cond (ConfigRestrictModReqSCG__ext1 z) /\
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
Definition ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__Format : T_Format Z ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__cond :=
 ranged_int_format (1) (15) ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__helper1 ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__helper2.

Opaque ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__cond ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__Format.


Definition ConfigRestrictModReqSCG__ext0O__Format_Type := Eval cbn in seq_format_prod ConfigRestrictModReqSCG__ext0O__list.
Definition ConfigRestrictModReqSCG__ext0O__Format_list : ConfigRestrictModReqSCG__ext0O__Format_Type :=
  (ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG__Format, (P_Max__Format, unit_format)).
Definition ConfigRestrictModReqSCG__ext0O__list__Format := (*Eval compute in *) seq_format ConfigRestrictModReqSCG__ext0O__list ConfigRestrictModReqSCG__ext0O__Format_list.
Definition ConfigRestrictModReqSCG__ext0O__F1 z :=
  (ConfigRestrictModReqSCG__ext0O__requestedPDCCH_BlindDetectionSCG z, (ConfigRestrictModReqSCG__ext0O__requestedP_MaxEUTRA z, tt)).
Definition ConfigRestrictModReqSCG__ext0O__F2 (y : seq_type ConfigRestrictModReqSCG__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ConfigRestrictModReqSCG__ext0O__Type i0 i1
  end.
Lemma ConfigRestrictModReqSCG__ext0O__F1F2_cond (z : ConfigRestrictModReqSCG__ext0O__Type)
  : ConfigRestrictModReqSCG__ext0O__cond z ->
  (seq_cond ConfigRestrictModReqSCG__ext0O__list (ConfigRestrictModReqSCG__ext0O__F1 z)).
intro H. unfold ConfigRestrictModReqSCG__ext0O__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictModReqSCG__ext0O__F1F2_cond2 (z : ConfigRestrictModReqSCG__ext0O__Type)
 : ConfigRestrictModReqSCG__ext0O__F2 (ConfigRestrictModReqSCG__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictModReqSCG__ext0O__F2F1_cond (y : seq_type ConfigRestrictModReqSCG__ext0O__list)
  : seq_cond ConfigRestrictModReqSCG__ext0O__list y ->
 (ConfigRestrictModReqSCG__ext0O__cond (ConfigRestrictModReqSCG__ext0O__F2 y)) /\  ConfigRestrictModReqSCG__ext0O__F1 (ConfigRestrictModReqSCG__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictModReqSCG__ext0O__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictModReqSCG__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictModReqSCG__ext0O__Format : T_Format ConfigRestrictModReqSCG__ext0O__Type ConfigRestrictModReqSCG__ext0O__cond :=
        proj2_format  ConfigRestrictModReqSCG__ext0O__cond ConfigRestrictModReqSCG__ext0O__list__Format
    ConfigRestrictModReqSCG__ext0O__F1 ConfigRestrictModReqSCG__ext0O__F2 ConfigRestrictModReqSCG__ext0O__F1F2_cond  ConfigRestrictModReqSCG__ext0O__F1F2_cond2 ConfigRestrictModReqSCG__ext0O__F2F1_cond.
Opaque ConfigRestrictModReqSCG__ext0O__cond ConfigRestrictModReqSCG__ext0O__Format.

Definition ConfigRestrictModReqSCG__ext0__check_all_none (b : ConfigRestrictModReqSCG__ext0O__Type) : bool :=
match b with 
  | make__ConfigRestrictModReqSCG__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition ConfigRestrictModReqSCG__ext0__Format : T_Format ConfigRestrictModReqSCG__ext0__Type ConfigRestrictModReqSCG__ext0__cond :=
  restrict_add_format ConfigRestrictModReqSCG__ext0__check_all_none ConfigRestrictModReqSCG__ext0O__Format.

Opaque ConfigRestrictModReqSCG__ext0__cond ConfigRestrictModReqSCG__ext0__Format.

Definition ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__Format : T_Format Z ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__cond :=
 ranged_int_format (1) (maxMeasIdentitiesMN) ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__helper1 ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__helper2.

Opaque ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__cond ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__Format.

Definition ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__Format : T_Format Z ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__cond :=
 ranged_int_format (1) (maxMeasIdentitiesMN) ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__helper1 ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__helper2.

Opaque ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__cond ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__Format.


Definition ConfigRestrictModReqSCG__ext1O__Format_Type := Eval cbn in seq_format_prod ConfigRestrictModReqSCG__ext1O__list.
Definition ConfigRestrictModReqSCG__ext1O__Format_list : ConfigRestrictModReqSCG__ext1O__Format_Type :=
  (P_Max__Format, (ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16__Format, (ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16__Format, (T_Offset_r16__Format, unit_format)))).
Definition ConfigRestrictModReqSCG__ext1O__list__Format := (*Eval compute in *) seq_format ConfigRestrictModReqSCG__ext1O__list ConfigRestrictModReqSCG__ext1O__Format_list.
Definition ConfigRestrictModReqSCG__ext1O__F1 z :=
  (ConfigRestrictModReqSCG__ext1O__requestedP_MaxFR2_r16 z, (ConfigRestrictModReqSCG__ext1O__requestedMaxInterFreqMeasIdSCG_r16 z, (ConfigRestrictModReqSCG__ext1O__requestedMaxIntraFreqMeasIdSCG_r16 z, (ConfigRestrictModReqSCG__ext1O__requestedToffset_r16 z, tt)))).
Definition ConfigRestrictModReqSCG__ext1O__F2 (y : seq_type ConfigRestrictModReqSCG__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ConfigRestrictModReqSCG__ext1O__Type i0 i1 i2 i3
  end.
Lemma ConfigRestrictModReqSCG__ext1O__F1F2_cond (z : ConfigRestrictModReqSCG__ext1O__Type)
  : ConfigRestrictModReqSCG__ext1O__cond z ->
  (seq_cond ConfigRestrictModReqSCG__ext1O__list (ConfigRestrictModReqSCG__ext1O__F1 z)).
intro H. unfold ConfigRestrictModReqSCG__ext1O__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictModReqSCG__ext1O__F1F2_cond2 (z : ConfigRestrictModReqSCG__ext1O__Type)
 : ConfigRestrictModReqSCG__ext1O__F2 (ConfigRestrictModReqSCG__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictModReqSCG__ext1O__F2F1_cond (y : seq_type ConfigRestrictModReqSCG__ext1O__list)
  : seq_cond ConfigRestrictModReqSCG__ext1O__list y ->
 (ConfigRestrictModReqSCG__ext1O__cond (ConfigRestrictModReqSCG__ext1O__F2 y)) /\  ConfigRestrictModReqSCG__ext1O__F1 (ConfigRestrictModReqSCG__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictModReqSCG__ext1O__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictModReqSCG__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictModReqSCG__ext1O__Format : T_Format ConfigRestrictModReqSCG__ext1O__Type ConfigRestrictModReqSCG__ext1O__cond :=
        proj2_format  ConfigRestrictModReqSCG__ext1O__cond ConfigRestrictModReqSCG__ext1O__list__Format
    ConfigRestrictModReqSCG__ext1O__F1 ConfigRestrictModReqSCG__ext1O__F2 ConfigRestrictModReqSCG__ext1O__F1F2_cond  ConfigRestrictModReqSCG__ext1O__F1F2_cond2 ConfigRestrictModReqSCG__ext1O__F2F1_cond.
Opaque ConfigRestrictModReqSCG__ext1O__cond ConfigRestrictModReqSCG__ext1O__Format.

Definition ConfigRestrictModReqSCG__ext1__check_all_none (b : ConfigRestrictModReqSCG__ext1O__Type) : bool :=
match b with 
  | make__ConfigRestrictModReqSCG__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition ConfigRestrictModReqSCG__ext1__Format : T_Format ConfigRestrictModReqSCG__ext1__Type ConfigRestrictModReqSCG__ext1__cond :=
  restrict_add_format ConfigRestrictModReqSCG__ext1__check_all_none ConfigRestrictModReqSCG__ext1O__Format.

Opaque ConfigRestrictModReqSCG__ext1__cond ConfigRestrictModReqSCG__ext1__Format.


Definition ConfigRestrictModReqSCG__root_Format_Type := Eval cbn in seq_format_prod ConfigRestrictModReqSCG__root_list.
Definition ConfigRestrictModReqSCG__root_Format_list : ConfigRestrictModReqSCG__root_Format_Type :=
  (BandCombinationInfoSN__Format, (P_Max__Format, unit_format)).

Definition ConfigRestrictModReqSCG__ext_Format_Type := Eval cbn in get_formats ConfigRestrictModReqSCG__ext_list.
Definition ConfigRestrictModReqSCG__ext_Format_list : ConfigRestrictModReqSCG__ext_Format_Type :=
  (ConfigRestrictModReqSCG__ext0__Format, (ConfigRestrictModReqSCG__ext1__Format, unit__Format)).

Definition ConfigRestrictModReqSCG__list_type : Set := (seq_type ConfigRestrictModReqSCG__root_list) * (seq_ext_type ConfigRestrictModReqSCG__ext_list).
Definition ConfigRestrictModReqSCG__list_cond (z : ConfigRestrictModReqSCG__list_type) : Prop :=
        (seq_cond ConfigRestrictModReqSCG__root_list (fst z)) /\ (seq_ext_cond ConfigRestrictModReqSCG__ext_list (snd z)).
Definition ConfigRestrictModReqSCG__list_format : T_Format ConfigRestrictModReqSCG__list_type ConfigRestrictModReqSCG__list_cond :=
 (* Eval compute in *) seq_ext_format ConfigRestrictModReqSCG__root_list ConfigRestrictModReqSCG__root_Format_list ConfigRestrictModReqSCG__ext_list ConfigRestrictModReqSCG__ext_Format_list.

Opaque ConfigRestrictModReqSCG__list_format.
Definition ConfigRestrictModReqSCG__F1 (z : ConfigRestrictModReqSCG__Type) : ConfigRestrictModReqSCG__list_type :=
  (((ConfigRestrictModReqSCG__requestedBC_MRDC z, (ConfigRestrictModReqSCG__requestedP_MaxFR1 z, tt))), (
(ConfigRestrictModReqSCG__ext0 z, (ConfigRestrictModReqSCG__ext1 z, tt)))).
Definition ConfigRestrictModReqSCG__F2 (y : ConfigRestrictModReqSCG__list_type) : ConfigRestrictModReqSCG__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, _)))=>
    make__ConfigRestrictModReqSCG__Type j0 j1 i0 i1
  end.
Definition ConfigRestrictModReqSCG__helper1 : (forall a : ConfigRestrictModReqSCG__Type, ConfigRestrictModReqSCG__cond a -> ConfigRestrictModReqSCG__list_cond (ConfigRestrictModReqSCG__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ConfigRestrictModReqSCG__helper2 : (forall a : ConfigRestrictModReqSCG__Type, ConfigRestrictModReqSCG__F2 (ConfigRestrictModReqSCG__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ConfigRestrictModReqSCG__helper3 : (forall b : ConfigRestrictModReqSCG__list_type, ConfigRestrictModReqSCG__list_cond b -> ConfigRestrictModReqSCG__cond (ConfigRestrictModReqSCG__F2 b) /\ ConfigRestrictModReqSCG__F1 (ConfigRestrictModReqSCG__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ConfigRestrictModReqSCG__cond, ConfigRestrictModReqSCG__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ConfigRestrictModReqSCG__Format : T_Format ConfigRestrictModReqSCG__Type ConfigRestrictModReqSCG__cond :=
 proj2_format ConfigRestrictModReqSCG__cond ConfigRestrictModReqSCG__list_format  ConfigRestrictModReqSCG__F1 ConfigRestrictModReqSCG__F2 ConfigRestrictModReqSCG__helper1 ConfigRestrictModReqSCG__helper2 ConfigRestrictModReqSCG__helper3.

Opaque ConfigRestrictModReqSCG__cond ConfigRestrictModReqSCG__Format.

