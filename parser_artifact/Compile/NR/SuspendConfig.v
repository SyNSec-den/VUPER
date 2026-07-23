Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.I_RNTI_Value.

Opaque I_RNTI_Value__cond I_RNTI_Value__Format.

Require Import NR.ShortI_RNTI_Value.

Opaque ShortI_RNTI_Value__cond ShortI_RNTI_Value__Format.

Require Import NR.PagingCycle.

Opaque PagingCycle__cond PagingCycle__Format.

Require Import NR.RAN_NotificationAreaInfo.

Opaque RAN_NotificationAreaInfo__cond RAN_NotificationAreaInfo__Format.

Require Import NR.PeriodicRNAU_TimerValue.

Opaque PeriodicRNAU_TimerValue__cond PeriodicRNAU_TimerValue__Format.

Require Import NR.NextHopChainingCount.

Opaque NextHopChainingCount__cond NextHopChainingCount__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.SetupRelease.
Require Import NR.SDT_Config_r17.
Definition SuspendConfig__ext0O__sdt_Config_r17__Type := SetupRelease__Type SDT_Config_r17__Type.
Definition SuspendConfig__ext0O__sdt_Config_r17__cond := SetupRelease__cond _ SDT_Config_r17__cond.
Definition SuspendConfig__ext0O__sdt_Config_r17__Format : T_Format SuspendConfig__ext0O__sdt_Config_r17__Type SuspendConfig__ext0O__sdt_Config_r17__cond := SetupRelease__Format _ _ SDT_Config_r17__Format.
Opaque SuspendConfig__ext0O__sdt_Config_r17__cond SuspendConfig__ext0O__sdt_Config_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SRS_PosRRC_Inactive_r17.
Definition SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Type := SetupRelease__Type SRS_PosRRC_Inactive_r17__Type.
Definition SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__cond := SetupRelease__cond _ SRS_PosRRC_Inactive_r17__cond.
Definition SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Format : T_Format SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Type SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__cond := SetupRelease__Format _ _ SRS_PosRRC_Inactive_r17__Format.
Opaque SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__cond SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Format.

Require Import NR.ExtendedPagingCycle_r17.

Opaque ExtendedPagingCycle_r17__cond ExtendedPagingCycle_r17__Format.

Record SuspendConfig__ext0O__Type : Set :=
  make__SuspendConfig__ext0O__Type {
    SuspendConfig__ext0O__sl_UEIdentityRemote_r17 : option RNTI_Value__Type ;
    SuspendConfig__ext0O__sdt_Config_r17 : option SuspendConfig__ext0O__sdt_Config_r17__Type ;
    SuspendConfig__ext0O__srs_PosRRC_Inactive_r17 : option SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Type ;
    SuspendConfig__ext0O__ran_ExtendedPagingCycle_r17 : option ExtendedPagingCycle_r17__Type ;
}.
Definition SuspendConfig__ext0O__list := (
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt SuspendConfig__ext0O__sdt_Config_r17__Type SuspendConfig__ext0O__sdt_Config_r17__cond ::
 Opt SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Type SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__cond ::
 Opt ExtendedPagingCycle_r17__Type ExtendedPagingCycle_r17__cond ::
 nil).
Definition SuspendConfig__ext0O__cond z := 
  opt_cond RNTI_Value__cond (SuspendConfig__ext0O__sl_UEIdentityRemote_r17 z) /\
  opt_cond SuspendConfig__ext0O__sdt_Config_r17__cond (SuspendConfig__ext0O__sdt_Config_r17 z) /\
  opt_cond SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__cond (SuspendConfig__ext0O__srs_PosRRC_Inactive_r17 z) /\
  opt_cond ExtendedPagingCycle_r17__cond (SuspendConfig__ext0O__ran_ExtendedPagingCycle_r17 z) /\
  True.

Definition SuspendConfig__ext0__Type := SuspendConfig__ext0O__Type.
Definition SuspendConfig__ext0__cond := SuspendConfig__ext0O__cond.

Record SuspendConfig__Type : Set :=
  make__SuspendConfig__Type {
    SuspendConfig__fullI_RNTI : I_RNTI_Value__Type ;
    SuspendConfig__shortI_RNTI : ShortI_RNTI_Value__Type ;
    SuspendConfig__ran_PagingCycle : PagingCycle__Type ;
    SuspendConfig__ran_NotificationAreaInfo : option RAN_NotificationAreaInfo__Type ;
    SuspendConfig__t380 : option PeriodicRNAU_TimerValue__Type ;
    SuspendConfig__nextHopChainingCount : NextHopChainingCount__Type ;
    SuspendConfig__ext0 : option SuspendConfig__ext0__Type ;
}.
Definition SuspendConfig__root_list : list seq_elem := (
 Nor I_RNTI_Value__Type I_RNTI_Value__cond ::
 Nor ShortI_RNTI_Value__Type ShortI_RNTI_Value__cond ::
 Nor PagingCycle__Type PagingCycle__cond ::
 Opt RAN_NotificationAreaInfo__Type RAN_NotificationAreaInfo__cond ::
 Opt PeriodicRNAU_TimerValue__Type PeriodicRNAU_TimerValue__cond ::
 Nor NextHopChainingCount__Type NextHopChainingCount__cond ::
 nil).
Definition SuspendConfig__ext_list : list typ := (
  typ_cons SuspendConfig__ext0__Type SuspendConfig__ext0__cond ::
  nil).
Definition SuspendConfig__cond (z : SuspendConfig__Type) := 
(  I_RNTI_Value__cond (SuspendConfig__fullI_RNTI z) /\
  ShortI_RNTI_Value__cond (SuspendConfig__shortI_RNTI z) /\
  PagingCycle__cond (SuspendConfig__ran_PagingCycle z) /\
  opt_cond RAN_NotificationAreaInfo__cond (SuspendConfig__ran_NotificationAreaInfo z) /\
  opt_cond PeriodicRNAU_TimerValue__cond (SuspendConfig__t380 z) /\
  NextHopChainingCount__cond (SuspendConfig__nextHopChainingCount z) /\
  True) /\ 
(  opt_cond SuspendConfig__ext0__cond (SuspendConfig__ext0 z) /\
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
Opaque SuspendConfig__ext0O__sdt_Config_r17__cond SuspendConfig__ext0O__sdt_Config_r17__Format.

Opaque SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__cond SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Format.


Definition SuspendConfig__ext0O__Format_Type := Eval cbn in seq_format_prod SuspendConfig__ext0O__list.
Definition SuspendConfig__ext0O__Format_list : SuspendConfig__ext0O__Format_Type :=
  (RNTI_Value__Format, (SuspendConfig__ext0O__sdt_Config_r17__Format, (SuspendConfig__ext0O__srs_PosRRC_Inactive_r17__Format, (ExtendedPagingCycle_r17__Format, unit_format)))).
Definition SuspendConfig__ext0O__list__Format := (*Eval compute in *) seq_format SuspendConfig__ext0O__list SuspendConfig__ext0O__Format_list.
Definition SuspendConfig__ext0O__F1 z :=
  (SuspendConfig__ext0O__sl_UEIdentityRemote_r17 z, (SuspendConfig__ext0O__sdt_Config_r17 z, (SuspendConfig__ext0O__srs_PosRRC_Inactive_r17 z, (SuspendConfig__ext0O__ran_ExtendedPagingCycle_r17 z, tt)))).
Definition SuspendConfig__ext0O__F2 (y : seq_type SuspendConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SuspendConfig__ext0O__Type i0 i1 i2 i3
  end.
Lemma SuspendConfig__ext0O__F1F2_cond (z : SuspendConfig__ext0O__Type)
  : SuspendConfig__ext0O__cond z ->
  (seq_cond SuspendConfig__ext0O__list (SuspendConfig__ext0O__F1 z)).
intro H. unfold SuspendConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma SuspendConfig__ext0O__F1F2_cond2 (z : SuspendConfig__ext0O__Type)
 : SuspendConfig__ext0O__F2 (SuspendConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SuspendConfig__ext0O__F2F1_cond (y : seq_type SuspendConfig__ext0O__list)
  : seq_cond SuspendConfig__ext0O__list y ->
 (SuspendConfig__ext0O__cond (SuspendConfig__ext0O__F2 y)) /\  SuspendConfig__ext0O__F1 (SuspendConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SuspendConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold SuspendConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SuspendConfig__ext0O__Format : T_Format SuspendConfig__ext0O__Type SuspendConfig__ext0O__cond :=
        proj2_format  SuspendConfig__ext0O__cond SuspendConfig__ext0O__list__Format
    SuspendConfig__ext0O__F1 SuspendConfig__ext0O__F2 SuspendConfig__ext0O__F1F2_cond  SuspendConfig__ext0O__F1F2_cond2 SuspendConfig__ext0O__F2F1_cond.
Opaque SuspendConfig__ext0O__cond SuspendConfig__ext0O__Format.

Definition SuspendConfig__ext0__check_all_none (b : SuspendConfig__ext0O__Type) : bool :=
match b with 
  | make__SuspendConfig__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition SuspendConfig__ext0__Format : T_Format SuspendConfig__ext0__Type SuspendConfig__ext0__cond :=
  restrict_add_format SuspendConfig__ext0__check_all_none SuspendConfig__ext0O__Format.

Opaque SuspendConfig__ext0__cond SuspendConfig__ext0__Format.


Definition SuspendConfig__root_Format_Type := Eval cbn in seq_format_prod SuspendConfig__root_list.
Definition SuspendConfig__root_Format_list : SuspendConfig__root_Format_Type :=
  (I_RNTI_Value__Format, (ShortI_RNTI_Value__Format, (PagingCycle__Format, (RAN_NotificationAreaInfo__Format, (PeriodicRNAU_TimerValue__Format, (NextHopChainingCount__Format, unit_format)))))).

Definition SuspendConfig__ext_Format_Type := Eval cbn in get_formats SuspendConfig__ext_list.
Definition SuspendConfig__ext_Format_list : SuspendConfig__ext_Format_Type :=
  (SuspendConfig__ext0__Format, unit__Format).

Definition SuspendConfig__list_type : Set := (seq_type SuspendConfig__root_list) * (seq_ext_type SuspendConfig__ext_list).
Definition SuspendConfig__list_cond (z : SuspendConfig__list_type) : Prop :=
        (seq_cond SuspendConfig__root_list (fst z)) /\ (seq_ext_cond SuspendConfig__ext_list (snd z)).
Definition SuspendConfig__list_format : T_Format SuspendConfig__list_type SuspendConfig__list_cond :=
 (* Eval compute in *) seq_ext_format SuspendConfig__root_list SuspendConfig__root_Format_list SuspendConfig__ext_list SuspendConfig__ext_Format_list.

Opaque SuspendConfig__list_format.
Definition SuspendConfig__F1 (z : SuspendConfig__Type) : SuspendConfig__list_type :=
  (((SuspendConfig__fullI_RNTI z, (SuspendConfig__shortI_RNTI z, (SuspendConfig__ran_PagingCycle z, (SuspendConfig__ran_NotificationAreaInfo z, (SuspendConfig__t380 z, (SuspendConfig__nextHopChainingCount z, tt))))))), (
(SuspendConfig__ext0 z, tt))).
Definition SuspendConfig__F2 (y : SuspendConfig__list_type) : SuspendConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__SuspendConfig__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition SuspendConfig__helper1 : (forall a : SuspendConfig__Type, SuspendConfig__cond a -> SuspendConfig__list_cond (SuspendConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SuspendConfig__helper2 : (forall a : SuspendConfig__Type, SuspendConfig__F2 (SuspendConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SuspendConfig__helper3 : (forall b : SuspendConfig__list_type, SuspendConfig__list_cond b -> SuspendConfig__cond (SuspendConfig__F2 b) /\ SuspendConfig__F1 (SuspendConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SuspendConfig__cond, SuspendConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SuspendConfig__Format : T_Format SuspendConfig__Type SuspendConfig__cond :=
 proj2_format SuspendConfig__cond SuspendConfig__list_format  SuspendConfig__F1 SuspendConfig__F2 SuspendConfig__helper1 SuspendConfig__helper2 SuspendConfig__helper3.

Opaque SuspendConfig__cond SuspendConfig__Format.

