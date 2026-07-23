Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ReestablishmentInfo.

Opaque ReestablishmentInfo__cond ReestablishmentInfo__Format.

Require Import NR.ConfigRestrictInfoSCG.

Opaque ConfigRestrictInfoSCG__cond ConfigRestrictInfoSCG__Format.

Require Import NR.RAN_NotificationAreaInfo.

Opaque RAN_NotificationAreaInfo__cond RAN_NotificationAreaInfo__Format.

Record AS_Context__ext0O__Type : Set :=
  make__AS_Context__ext0O__Type {
    AS_Context__ext0O__ran_NotificationAreaInfo : option RAN_NotificationAreaInfo__Type ;
}.
Definition AS_Context__ext0O__list := (
 Opt RAN_NotificationAreaInfo__Type RAN_NotificationAreaInfo__cond ::
 nil).
Definition AS_Context__ext0O__cond z := 
  opt_cond RAN_NotificationAreaInfo__cond (AS_Context__ext0O__ran_NotificationAreaInfo z) /\
  True.

Definition AS_Context__ext0__Type := AS_Context__ext0O__Type.
Definition AS_Context__ext0__cond := AS_Context__ext0O__cond.

Record AS_Context__ext1O__Type : Set :=
  make__AS_Context__ext1O__Type {
    AS_Context__ext1O__ueAssistanceInformation : option octet_string ;
}.
Definition AS_Context__ext1O__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition AS_Context__ext1O__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Context__ext1O__ueAssistanceInformation z) /\
  True.

Definition AS_Context__ext1__Type := AS_Context__ext1O__Type.
Definition AS_Context__ext1__cond := AS_Context__ext1O__cond.

Require Import NR.BandCombinationInfoSN.

Opaque BandCombinationInfoSN__cond BandCombinationInfoSN__Format.

Record AS_Context__ext2O__Type : Set :=
  make__AS_Context__ext2O__Type {
    AS_Context__ext2O__selectedBandCombinationSN : option BandCombinationInfoSN__Type ;
}.
Definition AS_Context__ext2O__list := (
 Opt BandCombinationInfoSN__Type BandCombinationInfoSN__cond ::
 nil).
Definition AS_Context__ext2O__cond z := 
  opt_cond BandCombinationInfoSN__cond (AS_Context__ext2O__selectedBandCombinationSN z) /\
  True.

Definition AS_Context__ext2__Type := AS_Context__ext2O__Type.
Definition AS_Context__ext2__cond := AS_Context__ext2O__cond.

Require Import NR.ConfigRestrictInfoDAPS_r16.

Opaque ConfigRestrictInfoDAPS_r16__cond ConfigRestrictInfoDAPS_r16__Format.

Require Import NR.NeedForGapsInfoNR_r16.

Opaque NeedForGapsInfoNR_r16__cond NeedForGapsInfoNR_r16__Format.

Record AS_Context__ext3O__Type : Set :=
  make__AS_Context__ext3O__Type {
    AS_Context__ext3O__configRestrictInfoDAPS_r16 : option ConfigRestrictInfoDAPS_r16__Type ;
    AS_Context__ext3O__sidelinkUEInformationNR_r16 : option octet_string ;
    AS_Context__ext3O__sidelinkUEInformationEUTRA_r16 : option octet_string ;
    AS_Context__ext3O__ueAssistanceInformationEUTRA_r16 : option octet_string ;
    AS_Context__ext3O__ueAssistanceInformationSCG_r16 : option octet_string ;
    AS_Context__ext3O__needForGapsInfoNR_r16 : option NeedForGapsInfoNR_r16__Type ;
}.
Definition AS_Context__ext3O__list := (
 Opt ConfigRestrictInfoDAPS_r16__Type ConfigRestrictInfoDAPS_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt NeedForGapsInfoNR_r16__Type NeedForGapsInfoNR_r16__cond ::
 nil).
Definition AS_Context__ext3O__cond z := 
  opt_cond ConfigRestrictInfoDAPS_r16__cond (AS_Context__ext3O__configRestrictInfoDAPS_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Context__ext3O__sidelinkUEInformationNR_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Context__ext3O__sidelinkUEInformationEUTRA_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Context__ext3O__ueAssistanceInformationEUTRA_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Context__ext3O__ueAssistanceInformationSCG_r16 z) /\
  opt_cond NeedForGapsInfoNR_r16__cond (AS_Context__ext3O__needForGapsInfoNR_r16 z) /\
  True.

Definition AS_Context__ext3__Type := AS_Context__ext3O__Type.
Definition AS_Context__ext3__cond := AS_Context__ext3O__cond.

Require Import NR.ConfigRestrictInfoDAPS_v1640.

Opaque ConfigRestrictInfoDAPS_v1640__cond ConfigRestrictInfoDAPS_v1640__Format.

Record AS_Context__ext4O__Type : Set :=
  make__AS_Context__ext4O__Type {
    AS_Context__ext4O__configRestrictInfoDAPS_v1640 : option ConfigRestrictInfoDAPS_v1640__Type ;
}.
Definition AS_Context__ext4O__list := (
 Opt ConfigRestrictInfoDAPS_v1640__Type ConfigRestrictInfoDAPS_v1640__cond ::
 nil).
Definition AS_Context__ext4O__cond z := 
  opt_cond ConfigRestrictInfoDAPS_v1640__cond (AS_Context__ext4O__configRestrictInfoDAPS_v1640 z) /\
  True.

Definition AS_Context__ext4__Type := AS_Context__ext4O__Type.
Definition AS_Context__ext4__cond := AS_Context__ext4O__cond.

Require Import NR.NeedForGapNCSG_InfoNR_r17.

Opaque NeedForGapNCSG_InfoNR_r17__cond NeedForGapNCSG_InfoNR_r17__Format.

Require Import NR.NeedForGapNCSG_InfoEUTRA_r17.

Opaque NeedForGapNCSG_InfoEUTRA_r17__cond NeedForGapNCSG_InfoEUTRA_r17__Format.

Record AS_Context__ext5O__Type : Set :=
  make__AS_Context__ext5O__Type {
    AS_Context__ext5O__needForGapNCSG_InfoNR_r17 : option NeedForGapNCSG_InfoNR_r17__Type ;
    AS_Context__ext5O__needForGapNCSG_InfoEUTRA_r17 : option NeedForGapNCSG_InfoEUTRA_r17__Type ;
    AS_Context__ext5O__mbsInterestIndication_r17 : option octet_string ;
}.
Definition AS_Context__ext5O__list := (
 Opt NeedForGapNCSG_InfoNR_r17__Type NeedForGapNCSG_InfoNR_r17__cond ::
 Opt NeedForGapNCSG_InfoEUTRA_r17__Type NeedForGapNCSG_InfoEUTRA_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition AS_Context__ext5O__cond z := 
  opt_cond NeedForGapNCSG_InfoNR_r17__cond (AS_Context__ext5O__needForGapNCSG_InfoNR_r17 z) /\
  opt_cond NeedForGapNCSG_InfoEUTRA_r17__cond (AS_Context__ext5O__needForGapNCSG_InfoEUTRA_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Context__ext5O__mbsInterestIndication_r17 z) /\
  True.

Definition AS_Context__ext5__Type := AS_Context__ext5O__Type.
Definition AS_Context__ext5__cond := AS_Context__ext5O__cond.

Record AS_Context__Type : Set :=
  make__AS_Context__Type {
    AS_Context__reestablishmentInfo : option ReestablishmentInfo__Type ;
    AS_Context__configRestrictInfo : option ConfigRestrictInfoSCG__Type ;
    AS_Context__ext0 : option AS_Context__ext0__Type ;
    AS_Context__ext1 : option AS_Context__ext1__Type ;
    AS_Context__ext2 : option AS_Context__ext2__Type ;
    AS_Context__ext3 : option AS_Context__ext3__Type ;
    AS_Context__ext4 : option AS_Context__ext4__Type ;
    AS_Context__ext5 : option AS_Context__ext5__Type ;
}.
Definition AS_Context__root_list : list seq_elem := (
 Opt ReestablishmentInfo__Type ReestablishmentInfo__cond ::
 Opt ConfigRestrictInfoSCG__Type ConfigRestrictInfoSCG__cond ::
 nil).
Definition AS_Context__ext_list : list typ := (
  typ_cons AS_Context__ext0__Type AS_Context__ext0__cond ::
  typ_cons AS_Context__ext1__Type AS_Context__ext1__cond ::
  typ_cons AS_Context__ext2__Type AS_Context__ext2__cond ::
  typ_cons AS_Context__ext3__Type AS_Context__ext3__cond ::
  typ_cons AS_Context__ext4__Type AS_Context__ext4__cond ::
  typ_cons AS_Context__ext5__Type AS_Context__ext5__cond ::
  nil).
Definition AS_Context__cond (z : AS_Context__Type) := 
(  opt_cond ReestablishmentInfo__cond (AS_Context__reestablishmentInfo z) /\
  opt_cond ConfigRestrictInfoSCG__cond (AS_Context__configRestrictInfo z) /\
  True) /\ 
(  opt_cond AS_Context__ext0__cond (AS_Context__ext0 z) /\
  opt_cond AS_Context__ext1__cond (AS_Context__ext1 z) /\
  opt_cond AS_Context__ext2__cond (AS_Context__ext2 z) /\
  opt_cond AS_Context__ext3__cond (AS_Context__ext3 z) /\
  opt_cond AS_Context__ext4__cond (AS_Context__ext4 z) /\
  opt_cond AS_Context__ext5__cond (AS_Context__ext5 z) /\
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

Definition AS_Context__ext0O__Format_Type := Eval cbn in seq_format_prod AS_Context__ext0O__list.
Definition AS_Context__ext0O__Format_list : AS_Context__ext0O__Format_Type :=
  (RAN_NotificationAreaInfo__Format, unit_format).
Definition AS_Context__ext0O__list__Format := (*Eval compute in *) seq_format AS_Context__ext0O__list AS_Context__ext0O__Format_list.
Definition AS_Context__ext0O__F1 z :=
  (AS_Context__ext0O__ran_NotificationAreaInfo z, tt).
Definition AS_Context__ext0O__F2 (y : seq_type AS_Context__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__AS_Context__ext0O__Type i0
  end.
Lemma AS_Context__ext0O__F1F2_cond (z : AS_Context__ext0O__Type)
  : AS_Context__ext0O__cond z ->
  (seq_cond AS_Context__ext0O__list (AS_Context__ext0O__F1 z)).
intro H. unfold AS_Context__ext0O__cond in H. simpl. auto. Qed.
Lemma AS_Context__ext0O__F1F2_cond2 (z : AS_Context__ext0O__Type)
 : AS_Context__ext0O__F2 (AS_Context__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Context__ext0O__F2F1_cond (y : seq_type AS_Context__ext0O__list)
  : seq_cond AS_Context__ext0O__list y ->
 (AS_Context__ext0O__cond (AS_Context__ext0O__F2 y)) /\  AS_Context__ext0O__F1 (AS_Context__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Context__ext0O__cond. simpl in *. auto.
 - simpl. unfold AS_Context__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Context__ext0O__Format : T_Format AS_Context__ext0O__Type AS_Context__ext0O__cond :=
        proj2_format  AS_Context__ext0O__cond AS_Context__ext0O__list__Format
    AS_Context__ext0O__F1 AS_Context__ext0O__F2 AS_Context__ext0O__F1F2_cond  AS_Context__ext0O__F1F2_cond2 AS_Context__ext0O__F2F1_cond.
Opaque AS_Context__ext0O__cond AS_Context__ext0O__Format.

Definition AS_Context__ext0__check_all_none (b : AS_Context__ext0O__Type) : bool :=
match b with 
  | make__AS_Context__ext0O__Type None  => false 
  | _ => true 
 end.
Definition AS_Context__ext0__Format : T_Format AS_Context__ext0__Type AS_Context__ext0__cond :=
  restrict_add_format AS_Context__ext0__check_all_none AS_Context__ext0O__Format.

Opaque AS_Context__ext0__cond AS_Context__ext0__Format.


Definition AS_Context__ext1O__Format_Type := Eval cbn in seq_format_prod AS_Context__ext1O__list.
Definition AS_Context__ext1O__Format_list : AS_Context__ext1O__Format_Type :=
  (octet_string_nc__Format, unit_format).
Definition AS_Context__ext1O__list__Format := (*Eval compute in *) seq_format AS_Context__ext1O__list AS_Context__ext1O__Format_list.
Definition AS_Context__ext1O__F1 z :=
  (AS_Context__ext1O__ueAssistanceInformation z, tt).
Definition AS_Context__ext1O__F2 (y : seq_type AS_Context__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__AS_Context__ext1O__Type i0
  end.
Lemma AS_Context__ext1O__F1F2_cond (z : AS_Context__ext1O__Type)
  : AS_Context__ext1O__cond z ->
  (seq_cond AS_Context__ext1O__list (AS_Context__ext1O__F1 z)).
intro H. unfold AS_Context__ext1O__cond in H. simpl. auto. Qed.
Lemma AS_Context__ext1O__F1F2_cond2 (z : AS_Context__ext1O__Type)
 : AS_Context__ext1O__F2 (AS_Context__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Context__ext1O__F2F1_cond (y : seq_type AS_Context__ext1O__list)
  : seq_cond AS_Context__ext1O__list y ->
 (AS_Context__ext1O__cond (AS_Context__ext1O__F2 y)) /\  AS_Context__ext1O__F1 (AS_Context__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Context__ext1O__cond. simpl in *. auto.
 - simpl. unfold AS_Context__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Context__ext1O__Format : T_Format AS_Context__ext1O__Type AS_Context__ext1O__cond :=
        proj2_format  AS_Context__ext1O__cond AS_Context__ext1O__list__Format
    AS_Context__ext1O__F1 AS_Context__ext1O__F2 AS_Context__ext1O__F1F2_cond  AS_Context__ext1O__F1F2_cond2 AS_Context__ext1O__F2F1_cond.
Opaque AS_Context__ext1O__cond AS_Context__ext1O__Format.

Definition AS_Context__ext1__check_all_none (b : AS_Context__ext1O__Type) : bool :=
match b with 
  | make__AS_Context__ext1O__Type None  => false 
  | _ => true 
 end.
Definition AS_Context__ext1__Format : T_Format AS_Context__ext1__Type AS_Context__ext1__cond :=
  restrict_add_format AS_Context__ext1__check_all_none AS_Context__ext1O__Format.

Opaque AS_Context__ext1__cond AS_Context__ext1__Format.


Definition AS_Context__ext2O__Format_Type := Eval cbn in seq_format_prod AS_Context__ext2O__list.
Definition AS_Context__ext2O__Format_list : AS_Context__ext2O__Format_Type :=
  (BandCombinationInfoSN__Format, unit_format).
Definition AS_Context__ext2O__list__Format := (*Eval compute in *) seq_format AS_Context__ext2O__list AS_Context__ext2O__Format_list.
Definition AS_Context__ext2O__F1 z :=
  (AS_Context__ext2O__selectedBandCombinationSN z, tt).
Definition AS_Context__ext2O__F2 (y : seq_type AS_Context__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__AS_Context__ext2O__Type i0
  end.
Lemma AS_Context__ext2O__F1F2_cond (z : AS_Context__ext2O__Type)
  : AS_Context__ext2O__cond z ->
  (seq_cond AS_Context__ext2O__list (AS_Context__ext2O__F1 z)).
intro H. unfold AS_Context__ext2O__cond in H. simpl. auto. Qed.
Lemma AS_Context__ext2O__F1F2_cond2 (z : AS_Context__ext2O__Type)
 : AS_Context__ext2O__F2 (AS_Context__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Context__ext2O__F2F1_cond (y : seq_type AS_Context__ext2O__list)
  : seq_cond AS_Context__ext2O__list y ->
 (AS_Context__ext2O__cond (AS_Context__ext2O__F2 y)) /\  AS_Context__ext2O__F1 (AS_Context__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Context__ext2O__cond. simpl in *. auto.
 - simpl. unfold AS_Context__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Context__ext2O__Format : T_Format AS_Context__ext2O__Type AS_Context__ext2O__cond :=
        proj2_format  AS_Context__ext2O__cond AS_Context__ext2O__list__Format
    AS_Context__ext2O__F1 AS_Context__ext2O__F2 AS_Context__ext2O__F1F2_cond  AS_Context__ext2O__F1F2_cond2 AS_Context__ext2O__F2F1_cond.
Opaque AS_Context__ext2O__cond AS_Context__ext2O__Format.

Definition AS_Context__ext2__check_all_none (b : AS_Context__ext2O__Type) : bool :=
match b with 
  | make__AS_Context__ext2O__Type None  => false 
  | _ => true 
 end.
Definition AS_Context__ext2__Format : T_Format AS_Context__ext2__Type AS_Context__ext2__cond :=
  restrict_add_format AS_Context__ext2__check_all_none AS_Context__ext2O__Format.

Opaque AS_Context__ext2__cond AS_Context__ext2__Format.


Definition AS_Context__ext3O__Format_Type := Eval cbn in seq_format_prod AS_Context__ext3O__list.
Definition AS_Context__ext3O__Format_list : AS_Context__ext3O__Format_Type :=
  (ConfigRestrictInfoDAPS_r16__Format, (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, (NeedForGapsInfoNR_r16__Format, unit_format)))))).
Definition AS_Context__ext3O__list__Format := (*Eval compute in *) seq_format AS_Context__ext3O__list AS_Context__ext3O__Format_list.
Definition AS_Context__ext3O__F1 z :=
  (AS_Context__ext3O__configRestrictInfoDAPS_r16 z, (AS_Context__ext3O__sidelinkUEInformationNR_r16 z, (AS_Context__ext3O__sidelinkUEInformationEUTRA_r16 z, (AS_Context__ext3O__ueAssistanceInformationEUTRA_r16 z, (AS_Context__ext3O__ueAssistanceInformationSCG_r16 z, (AS_Context__ext3O__needForGapsInfoNR_r16 z, tt)))))).
Definition AS_Context__ext3O__F2 (y : seq_type AS_Context__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__AS_Context__ext3O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma AS_Context__ext3O__F1F2_cond (z : AS_Context__ext3O__Type)
  : AS_Context__ext3O__cond z ->
  (seq_cond AS_Context__ext3O__list (AS_Context__ext3O__F1 z)).
intro H. unfold AS_Context__ext3O__cond in H. simpl. auto. Qed.
Lemma AS_Context__ext3O__F1F2_cond2 (z : AS_Context__ext3O__Type)
 : AS_Context__ext3O__F2 (AS_Context__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Context__ext3O__F2F1_cond (y : seq_type AS_Context__ext3O__list)
  : seq_cond AS_Context__ext3O__list y ->
 (AS_Context__ext3O__cond (AS_Context__ext3O__F2 y)) /\  AS_Context__ext3O__F1 (AS_Context__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Context__ext3O__cond. simpl in *. auto.
 - simpl. unfold AS_Context__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Context__ext3O__Format : T_Format AS_Context__ext3O__Type AS_Context__ext3O__cond :=
        proj2_format  AS_Context__ext3O__cond AS_Context__ext3O__list__Format
    AS_Context__ext3O__F1 AS_Context__ext3O__F2 AS_Context__ext3O__F1F2_cond  AS_Context__ext3O__F1F2_cond2 AS_Context__ext3O__F2F1_cond.
Opaque AS_Context__ext3O__cond AS_Context__ext3O__Format.

Definition AS_Context__ext3__check_all_none (b : AS_Context__ext3O__Type) : bool :=
match b with 
  | make__AS_Context__ext3O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition AS_Context__ext3__Format : T_Format AS_Context__ext3__Type AS_Context__ext3__cond :=
  restrict_add_format AS_Context__ext3__check_all_none AS_Context__ext3O__Format.

Opaque AS_Context__ext3__cond AS_Context__ext3__Format.


Definition AS_Context__ext4O__Format_Type := Eval cbn in seq_format_prod AS_Context__ext4O__list.
Definition AS_Context__ext4O__Format_list : AS_Context__ext4O__Format_Type :=
  (ConfigRestrictInfoDAPS_v1640__Format, unit_format).
Definition AS_Context__ext4O__list__Format := (*Eval compute in *) seq_format AS_Context__ext4O__list AS_Context__ext4O__Format_list.
Definition AS_Context__ext4O__F1 z :=
  (AS_Context__ext4O__configRestrictInfoDAPS_v1640 z, tt).
Definition AS_Context__ext4O__F2 (y : seq_type AS_Context__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__AS_Context__ext4O__Type i0
  end.
Lemma AS_Context__ext4O__F1F2_cond (z : AS_Context__ext4O__Type)
  : AS_Context__ext4O__cond z ->
  (seq_cond AS_Context__ext4O__list (AS_Context__ext4O__F1 z)).
intro H. unfold AS_Context__ext4O__cond in H. simpl. auto. Qed.
Lemma AS_Context__ext4O__F1F2_cond2 (z : AS_Context__ext4O__Type)
 : AS_Context__ext4O__F2 (AS_Context__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Context__ext4O__F2F1_cond (y : seq_type AS_Context__ext4O__list)
  : seq_cond AS_Context__ext4O__list y ->
 (AS_Context__ext4O__cond (AS_Context__ext4O__F2 y)) /\  AS_Context__ext4O__F1 (AS_Context__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Context__ext4O__cond. simpl in *. auto.
 - simpl. unfold AS_Context__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Context__ext4O__Format : T_Format AS_Context__ext4O__Type AS_Context__ext4O__cond :=
        proj2_format  AS_Context__ext4O__cond AS_Context__ext4O__list__Format
    AS_Context__ext4O__F1 AS_Context__ext4O__F2 AS_Context__ext4O__F1F2_cond  AS_Context__ext4O__F1F2_cond2 AS_Context__ext4O__F2F1_cond.
Opaque AS_Context__ext4O__cond AS_Context__ext4O__Format.

Definition AS_Context__ext4__check_all_none (b : AS_Context__ext4O__Type) : bool :=
match b with 
  | make__AS_Context__ext4O__Type None  => false 
  | _ => true 
 end.
Definition AS_Context__ext4__Format : T_Format AS_Context__ext4__Type AS_Context__ext4__cond :=
  restrict_add_format AS_Context__ext4__check_all_none AS_Context__ext4O__Format.

Opaque AS_Context__ext4__cond AS_Context__ext4__Format.


Definition AS_Context__ext5O__Format_Type := Eval cbn in seq_format_prod AS_Context__ext5O__list.
Definition AS_Context__ext5O__Format_list : AS_Context__ext5O__Format_Type :=
  (NeedForGapNCSG_InfoNR_r17__Format, (NeedForGapNCSG_InfoEUTRA_r17__Format, (octet_string_nc__Format, unit_format))).
Definition AS_Context__ext5O__list__Format := (*Eval compute in *) seq_format AS_Context__ext5O__list AS_Context__ext5O__Format_list.
Definition AS_Context__ext5O__F1 z :=
  (AS_Context__ext5O__needForGapNCSG_InfoNR_r17 z, (AS_Context__ext5O__needForGapNCSG_InfoEUTRA_r17 z, (AS_Context__ext5O__mbsInterestIndication_r17 z, tt))).
Definition AS_Context__ext5O__F2 (y : seq_type AS_Context__ext5O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__AS_Context__ext5O__Type i0 i1 i2
  end.
Lemma AS_Context__ext5O__F1F2_cond (z : AS_Context__ext5O__Type)
  : AS_Context__ext5O__cond z ->
  (seq_cond AS_Context__ext5O__list (AS_Context__ext5O__F1 z)).
intro H. unfold AS_Context__ext5O__cond in H. simpl. auto. Qed.
Lemma AS_Context__ext5O__F1F2_cond2 (z : AS_Context__ext5O__Type)
 : AS_Context__ext5O__F2 (AS_Context__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Context__ext5O__F2F1_cond (y : seq_type AS_Context__ext5O__list)
  : seq_cond AS_Context__ext5O__list y ->
 (AS_Context__ext5O__cond (AS_Context__ext5O__F2 y)) /\  AS_Context__ext5O__F1 (AS_Context__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Context__ext5O__cond. simpl in *. auto.
 - simpl. unfold AS_Context__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Context__ext5O__Format : T_Format AS_Context__ext5O__Type AS_Context__ext5O__cond :=
        proj2_format  AS_Context__ext5O__cond AS_Context__ext5O__list__Format
    AS_Context__ext5O__F1 AS_Context__ext5O__F2 AS_Context__ext5O__F1F2_cond  AS_Context__ext5O__F1F2_cond2 AS_Context__ext5O__F2F1_cond.
Opaque AS_Context__ext5O__cond AS_Context__ext5O__Format.

Definition AS_Context__ext5__check_all_none (b : AS_Context__ext5O__Type) : bool :=
match b with 
  | make__AS_Context__ext5O__Type None None None  => false 
  | _ => true 
 end.
Definition AS_Context__ext5__Format : T_Format AS_Context__ext5__Type AS_Context__ext5__cond :=
  restrict_add_format AS_Context__ext5__check_all_none AS_Context__ext5O__Format.

Opaque AS_Context__ext5__cond AS_Context__ext5__Format.


Definition AS_Context__root_Format_Type := Eval cbn in seq_format_prod AS_Context__root_list.
Definition AS_Context__root_Format_list : AS_Context__root_Format_Type :=
  (ReestablishmentInfo__Format, (ConfigRestrictInfoSCG__Format, unit_format)).

Definition AS_Context__ext_Format_Type := Eval cbn in get_formats AS_Context__ext_list.
Definition AS_Context__ext_Format_list : AS_Context__ext_Format_Type :=
  (AS_Context__ext0__Format, (AS_Context__ext1__Format, (AS_Context__ext2__Format, (AS_Context__ext3__Format, (AS_Context__ext4__Format, (AS_Context__ext5__Format, unit__Format)))))).

Definition AS_Context__list_type : Set := (seq_type AS_Context__root_list) * (seq_ext_type AS_Context__ext_list).
Definition AS_Context__list_cond (z : AS_Context__list_type) : Prop :=
        (seq_cond AS_Context__root_list (fst z)) /\ (seq_ext_cond AS_Context__ext_list (snd z)).
Definition AS_Context__list_format : T_Format AS_Context__list_type AS_Context__list_cond :=
 (* Eval compute in *) seq_ext_format AS_Context__root_list AS_Context__root_Format_list AS_Context__ext_list AS_Context__ext_Format_list.

Opaque AS_Context__list_format.
Definition AS_Context__F1 (z : AS_Context__Type) : AS_Context__list_type :=
  (((AS_Context__reestablishmentInfo z, (AS_Context__configRestrictInfo z, tt))), (
(AS_Context__ext0 z, (AS_Context__ext1 z, (AS_Context__ext2 z, (AS_Context__ext3 z, (AS_Context__ext4 z, (AS_Context__ext5 z, tt)))))))).
Definition AS_Context__F2 (y : AS_Context__list_type) : AS_Context__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, (i2, (i3, (i4, (i5, _)))))))=>
    make__AS_Context__Type j0 j1 i0 i1 i2 i3 i4 i5
  end.
Definition AS_Context__helper1 : (forall a : AS_Context__Type, AS_Context__cond a -> AS_Context__list_cond (AS_Context__F1 a)).
                     intros. destruct a. auto. Qed.
Definition AS_Context__helper2 : (forall a : AS_Context__Type, AS_Context__F2 (AS_Context__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition AS_Context__helper3 : (forall b : AS_Context__list_type, AS_Context__list_cond b -> AS_Context__cond (AS_Context__F2 b) /\ AS_Context__F1 (AS_Context__F2 b) = b).
                     intros. destruct b as [y y1]. unfold AS_Context__cond, AS_Context__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition AS_Context__Format : T_Format AS_Context__Type AS_Context__cond :=
 proj2_format AS_Context__cond AS_Context__list_format  AS_Context__F1 AS_Context__F2 AS_Context__helper1 AS_Context__helper2 AS_Context__helper3.

Opaque AS_Context__cond AS_Context__Format.

