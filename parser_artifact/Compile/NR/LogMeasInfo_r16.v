Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Lemma LogMeasInfo_r16__relativeTimeStamp_r16__helper1 : (0 <= 7200)%Z.  lia. Qed.
Lemma LogMeasInfo_r16__relativeTimeStamp_r16__helper2 : to_bit_sz (Z.to_nat (7200 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7200 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply LogMeasInfo_r16__relativeTimeStamp_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogMeasInfo_r16__relativeTimeStamp_r16__Type := Z.
Definition LogMeasInfo_r16__relativeTimeStamp_r16__cond := (fun z => (0 <= z <= 7200)%Z).
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.MeasResultServingCell_r16.

Opaque MeasResultServingCell_r16__cond MeasResultServingCell_r16__Format.

Require Import NR.MeasResultListLogging2NR_r16.

Opaque MeasResultListLogging2NR_r16__cond MeasResultListLogging2NR_r16__Format.

Require Import NR.MeasResultList2EUTRA_r16.

Opaque MeasResultList2EUTRA_r16__cond MeasResultList2EUTRA_r16__Format.

Record LogMeasInfo_r16__measResultNeighCells_r16__Type : Set :=
  make__LogMeasInfo_r16__measResultNeighCells_r16__Type {
    LogMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListNR : option MeasResultListLogging2NR_r16__Type ;
    LogMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA : option MeasResultList2EUTRA_r16__Type ;
}.
Definition LogMeasInfo_r16__measResultNeighCells_r16__list := (
 Opt MeasResultListLogging2NR_r16__Type MeasResultListLogging2NR_r16__cond ::
 Opt MeasResultList2EUTRA_r16__Type MeasResultList2EUTRA_r16__cond ::
 nil).
Definition LogMeasInfo_r16__measResultNeighCells_r16__cond z := 
  opt_cond MeasResultListLogging2NR_r16__cond (LogMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListNR z) /\
  opt_cond MeasResultList2EUTRA_r16__cond (LogMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA z) /\
  True.

Inductive LogMeasInfo_r16__anyCellSelectionDetected_r16__Type : Set :=
 | LogMeasInfo_r16__anyCellSelectionDetected_r16__true
.
Definition LogMeasInfo_r16__anyCellSelectionDetected_r16__cond := (fun (_ : LogMeasInfo_r16__anyCellSelectionDetected_r16__Type) => True).
Lemma LogMeasInfo_r16__anyCellSelectionDetected_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogMeasInfo_r16__anyCellSelectionDetected_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LogMeasInfo_r16__anyCellSelectionDetected_r16__nat__helper.

Definition LogMeasInfo_r16__anyCellSelectionDetected_r16__F1 t :=
  match t with
  | LogMeasInfo_r16__anyCellSelectionDetected_r16__true => 0
  end.
Definition LogMeasInfo_r16__anyCellSelectionDetected_r16__F2 n :=
  match n with
  | 0 => LogMeasInfo_r16__anyCellSelectionDetected_r16__true
  | _ => LogMeasInfo_r16__anyCellSelectionDetected_r16__true
  end.
Lemma LogMeasInfo_r16__anyCellSelectionDetected_r16__F1F2 : forall x : LogMeasInfo_r16__anyCellSelectionDetected_r16__Type, (LogMeasInfo_r16__anyCellSelectionDetected_r16__F1 x <= 0) /\ LogMeasInfo_r16__anyCellSelectionDetected_r16__F2 (LogMeasInfo_r16__anyCellSelectionDetected_r16__F1 x) = x. imp_solve. Qed.
Lemma LogMeasInfo_r16__anyCellSelectionDetected_r16__F2F1 : forall (y : nat) (H : y <= 0), LogMeasInfo_r16__anyCellSelectionDetected_r16__F1 (LogMeasInfo_r16__anyCellSelectionDetected_r16__F2 y) = y. enum_solve H y. Qed.

Inductive LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type : Set :=
 | LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__true
.
Definition LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__cond := (fun (_ : LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type) => True).
Lemma LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__nat__helper.

Definition LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1 t :=
  match t with
  | LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__true => 0
  end.
Definition LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2 n :=
  match n with
  | 0 => LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__true
  | _ => LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__true
  end.
Lemma LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1F2 : forall x : LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type, (LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1 x <= 0) /\ LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2 (LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1 x) = x. imp_solve. Qed.
Lemma LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2F1 : forall (y : nat) (H : y <= 0), LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1 (LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2 y) = y. enum_solve H y. Qed.

Record LogMeasInfo_r16__ext0O__Type : Set :=
  make__LogMeasInfo_r16__ext0O__Type {
    LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17 : option LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type ;
}.
Definition LogMeasInfo_r16__ext0O__list := (
 Opt LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__cond ::
 nil).
Definition LogMeasInfo_r16__ext0O__cond z := 
  opt_cond LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__cond (LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17 z) /\
  True.

Definition LogMeasInfo_r16__ext0__Type := LogMeasInfo_r16__ext0O__Type.
Definition LogMeasInfo_r16__ext0__cond := LogMeasInfo_r16__ext0O__cond.

Record LogMeasInfo_r16__Type : Set :=
  make__LogMeasInfo_r16__Type {
    LogMeasInfo_r16__locationInfo_r16 : option LocationInfo_r16__Type ;
    LogMeasInfo_r16__relativeTimeStamp_r16 : Z ;
    LogMeasInfo_r16__servCellIdentity_r16 : option CGI_Info_Logging_r16__Type ;
    LogMeasInfo_r16__measResultServingCell_r16 : option MeasResultServingCell_r16__Type ;
    LogMeasInfo_r16__measResultNeighCells_r16 : LogMeasInfo_r16__measResultNeighCells_r16__Type ;
    LogMeasInfo_r16__anyCellSelectionDetected_r16 : option LogMeasInfo_r16__anyCellSelectionDetected_r16__Type ;
    LogMeasInfo_r16__ext0 : option LogMeasInfo_r16__ext0__Type ;
}.
Definition LogMeasInfo_r16__root_list : list seq_elem := (
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 Nor Z LogMeasInfo_r16__relativeTimeStamp_r16__cond ::
 Opt CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
 Opt MeasResultServingCell_r16__Type MeasResultServingCell_r16__cond ::
 Nor LogMeasInfo_r16__measResultNeighCells_r16__Type LogMeasInfo_r16__measResultNeighCells_r16__cond ::
 Opt LogMeasInfo_r16__anyCellSelectionDetected_r16__Type LogMeasInfo_r16__anyCellSelectionDetected_r16__cond ::
 nil).
Definition LogMeasInfo_r16__ext_list : list typ := (
  typ_cons LogMeasInfo_r16__ext0__Type LogMeasInfo_r16__ext0__cond ::
  nil).
Definition LogMeasInfo_r16__cond (z : LogMeasInfo_r16__Type) := 
(  opt_cond LocationInfo_r16__cond (LogMeasInfo_r16__locationInfo_r16 z) /\
  LogMeasInfo_r16__relativeTimeStamp_r16__cond (LogMeasInfo_r16__relativeTimeStamp_r16 z) /\
  opt_cond CGI_Info_Logging_r16__cond (LogMeasInfo_r16__servCellIdentity_r16 z) /\
  opt_cond MeasResultServingCell_r16__cond (LogMeasInfo_r16__measResultServingCell_r16 z) /\
  LogMeasInfo_r16__measResultNeighCells_r16__cond (LogMeasInfo_r16__measResultNeighCells_r16 z) /\
  opt_cond LogMeasInfo_r16__anyCellSelectionDetected_r16__cond (LogMeasInfo_r16__anyCellSelectionDetected_r16 z) /\
  True) /\ 
(  opt_cond LogMeasInfo_r16__ext0__cond (LogMeasInfo_r16__ext0 z) /\
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
Definition LogMeasInfo_r16__relativeTimeStamp_r16__Format : T_Format Z LogMeasInfo_r16__relativeTimeStamp_r16__cond :=
 ranged_int_format (0) (7200) LogMeasInfo_r16__relativeTimeStamp_r16__helper1 LogMeasInfo_r16__relativeTimeStamp_r16__helper2.

Opaque LogMeasInfo_r16__relativeTimeStamp_r16__cond LogMeasInfo_r16__relativeTimeStamp_r16__Format.


Definition LogMeasInfo_r16__measResultNeighCells_r16__Format_Type := Eval cbn in seq_format_prod LogMeasInfo_r16__measResultNeighCells_r16__list.
Definition LogMeasInfo_r16__measResultNeighCells_r16__Format_list : LogMeasInfo_r16__measResultNeighCells_r16__Format_Type :=
  (MeasResultListLogging2NR_r16__Format, (MeasResultList2EUTRA_r16__Format, unit_format)).
Definition LogMeasInfo_r16__measResultNeighCells_r16__list__Format := (*Eval compute in *) seq_format LogMeasInfo_r16__measResultNeighCells_r16__list LogMeasInfo_r16__measResultNeighCells_r16__Format_list.
Definition LogMeasInfo_r16__measResultNeighCells_r16__F1 z :=
  (LogMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListNR z, (LogMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA z, tt)).
Definition LogMeasInfo_r16__measResultNeighCells_r16__F2 (y : seq_type LogMeasInfo_r16__measResultNeighCells_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__LogMeasInfo_r16__measResultNeighCells_r16__Type i0 i1
  end.
Lemma LogMeasInfo_r16__measResultNeighCells_r16__F1F2_cond (z : LogMeasInfo_r16__measResultNeighCells_r16__Type)
  : LogMeasInfo_r16__measResultNeighCells_r16__cond z ->
  (seq_cond LogMeasInfo_r16__measResultNeighCells_r16__list (LogMeasInfo_r16__measResultNeighCells_r16__F1 z)).
intro H. unfold LogMeasInfo_r16__measResultNeighCells_r16__cond in H. simpl. auto. Qed.
Lemma LogMeasInfo_r16__measResultNeighCells_r16__F1F2_cond2 (z : LogMeasInfo_r16__measResultNeighCells_r16__Type)
 : LogMeasInfo_r16__measResultNeighCells_r16__F2 (LogMeasInfo_r16__measResultNeighCells_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LogMeasInfo_r16__measResultNeighCells_r16__F2F1_cond (y : seq_type LogMeasInfo_r16__measResultNeighCells_r16__list)
  : seq_cond LogMeasInfo_r16__measResultNeighCells_r16__list y ->
 (LogMeasInfo_r16__measResultNeighCells_r16__cond (LogMeasInfo_r16__measResultNeighCells_r16__F2 y)) /\  LogMeasInfo_r16__measResultNeighCells_r16__F1 (LogMeasInfo_r16__measResultNeighCells_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LogMeasInfo_r16__measResultNeighCells_r16__cond. simpl in *. auto.
 - simpl. unfold LogMeasInfo_r16__measResultNeighCells_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LogMeasInfo_r16__measResultNeighCells_r16__Format : T_Format LogMeasInfo_r16__measResultNeighCells_r16__Type LogMeasInfo_r16__measResultNeighCells_r16__cond :=
        proj2_format  LogMeasInfo_r16__measResultNeighCells_r16__cond LogMeasInfo_r16__measResultNeighCells_r16__list__Format
    LogMeasInfo_r16__measResultNeighCells_r16__F1 LogMeasInfo_r16__measResultNeighCells_r16__F2 LogMeasInfo_r16__measResultNeighCells_r16__F1F2_cond  LogMeasInfo_r16__measResultNeighCells_r16__F1F2_cond2 LogMeasInfo_r16__measResultNeighCells_r16__F2F1_cond.
Opaque LogMeasInfo_r16__measResultNeighCells_r16__cond LogMeasInfo_r16__measResultNeighCells_r16__Format.

Definition LogMeasInfo_r16__anyCellSelectionDetected_r16__Format : T_Format LogMeasInfo_r16__anyCellSelectionDetected_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogMeasInfo_r16__anyCellSelectionDetected_r16__nat__Format LogMeasInfo_r16__anyCellSelectionDetected_r16__F1 LogMeasInfo_r16__anyCellSelectionDetected_r16__F2 LogMeasInfo_r16__anyCellSelectionDetected_r16__F1F2 LogMeasInfo_r16__anyCellSelectionDetected_r16__F2F1.

Opaque LogMeasInfo_r16__anyCellSelectionDetected_r16__cond LogMeasInfo_r16__anyCellSelectionDetected_r16__Format.

Definition LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Format : T_Format LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__nat__Format LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1 LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2 LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1F2 LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2F1.

Opaque LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__cond LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Format.


Definition LogMeasInfo_r16__ext0O__Format_Type := Eval cbn in seq_format_prod LogMeasInfo_r16__ext0O__list.
Definition LogMeasInfo_r16__ext0O__Format_list : LogMeasInfo_r16__ext0O__Format_Type :=
  (LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Format, unit_format).
Definition LogMeasInfo_r16__ext0O__list__Format := (*Eval compute in *) seq_format LogMeasInfo_r16__ext0O__list LogMeasInfo_r16__ext0O__Format_list.
Definition LogMeasInfo_r16__ext0O__F1 z :=
  (LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17 z, tt).
Definition LogMeasInfo_r16__ext0O__F2 (y : seq_type LogMeasInfo_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__LogMeasInfo_r16__ext0O__Type i0
  end.
Lemma LogMeasInfo_r16__ext0O__F1F2_cond (z : LogMeasInfo_r16__ext0O__Type)
  : LogMeasInfo_r16__ext0O__cond z ->
  (seq_cond LogMeasInfo_r16__ext0O__list (LogMeasInfo_r16__ext0O__F1 z)).
intro H. unfold LogMeasInfo_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma LogMeasInfo_r16__ext0O__F1F2_cond2 (z : LogMeasInfo_r16__ext0O__Type)
 : LogMeasInfo_r16__ext0O__F2 (LogMeasInfo_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LogMeasInfo_r16__ext0O__F2F1_cond (y : seq_type LogMeasInfo_r16__ext0O__list)
  : seq_cond LogMeasInfo_r16__ext0O__list y ->
 (LogMeasInfo_r16__ext0O__cond (LogMeasInfo_r16__ext0O__F2 y)) /\  LogMeasInfo_r16__ext0O__F1 (LogMeasInfo_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LogMeasInfo_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold LogMeasInfo_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LogMeasInfo_r16__ext0O__Format : T_Format LogMeasInfo_r16__ext0O__Type LogMeasInfo_r16__ext0O__cond :=
        proj2_format  LogMeasInfo_r16__ext0O__cond LogMeasInfo_r16__ext0O__list__Format
    LogMeasInfo_r16__ext0O__F1 LogMeasInfo_r16__ext0O__F2 LogMeasInfo_r16__ext0O__F1F2_cond  LogMeasInfo_r16__ext0O__F1F2_cond2 LogMeasInfo_r16__ext0O__F2F1_cond.
Opaque LogMeasInfo_r16__ext0O__cond LogMeasInfo_r16__ext0O__Format.

Definition LogMeasInfo_r16__ext0__check_all_none (b : LogMeasInfo_r16__ext0O__Type) : bool :=
match b with 
  | make__LogMeasInfo_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition LogMeasInfo_r16__ext0__Format : T_Format LogMeasInfo_r16__ext0__Type LogMeasInfo_r16__ext0__cond :=
  restrict_add_format LogMeasInfo_r16__ext0__check_all_none LogMeasInfo_r16__ext0O__Format.

Opaque LogMeasInfo_r16__ext0__cond LogMeasInfo_r16__ext0__Format.


Definition LogMeasInfo_r16__root_Format_Type := Eval cbn in seq_format_prod LogMeasInfo_r16__root_list.
Definition LogMeasInfo_r16__root_Format_list : LogMeasInfo_r16__root_Format_Type :=
  (LocationInfo_r16__Format, (LogMeasInfo_r16__relativeTimeStamp_r16__Format, (CGI_Info_Logging_r16__Format, (MeasResultServingCell_r16__Format, (LogMeasInfo_r16__measResultNeighCells_r16__Format, (LogMeasInfo_r16__anyCellSelectionDetected_r16__Format, unit_format)))))).

Definition LogMeasInfo_r16__ext_Format_Type := Eval cbn in get_formats LogMeasInfo_r16__ext_list.
Definition LogMeasInfo_r16__ext_Format_list : LogMeasInfo_r16__ext_Format_Type :=
  (LogMeasInfo_r16__ext0__Format, unit__Format).

Definition LogMeasInfo_r16__list_type : Set := (seq_type LogMeasInfo_r16__root_list) * (seq_ext_type LogMeasInfo_r16__ext_list).
Definition LogMeasInfo_r16__list_cond (z : LogMeasInfo_r16__list_type) : Prop :=
        (seq_cond LogMeasInfo_r16__root_list (fst z)) /\ (seq_ext_cond LogMeasInfo_r16__ext_list (snd z)).
Definition LogMeasInfo_r16__list_format : T_Format LogMeasInfo_r16__list_type LogMeasInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format LogMeasInfo_r16__root_list LogMeasInfo_r16__root_Format_list LogMeasInfo_r16__ext_list LogMeasInfo_r16__ext_Format_list.

Opaque LogMeasInfo_r16__list_format.
Definition LogMeasInfo_r16__F1 (z : LogMeasInfo_r16__Type) : LogMeasInfo_r16__list_type :=
  (((LogMeasInfo_r16__locationInfo_r16 z, (LogMeasInfo_r16__relativeTimeStamp_r16 z, (LogMeasInfo_r16__servCellIdentity_r16 z, (LogMeasInfo_r16__measResultServingCell_r16 z, (LogMeasInfo_r16__measResultNeighCells_r16 z, (LogMeasInfo_r16__anyCellSelectionDetected_r16 z, tt))))))), (
(LogMeasInfo_r16__ext0 z, tt))).
Definition LogMeasInfo_r16__F2 (y : LogMeasInfo_r16__list_type) : LogMeasInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__LogMeasInfo_r16__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition LogMeasInfo_r16__helper1 : (forall a : LogMeasInfo_r16__Type, LogMeasInfo_r16__cond a -> LogMeasInfo_r16__list_cond (LogMeasInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LogMeasInfo_r16__helper2 : (forall a : LogMeasInfo_r16__Type, LogMeasInfo_r16__F2 (LogMeasInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LogMeasInfo_r16__helper3 : (forall b : LogMeasInfo_r16__list_type, LogMeasInfo_r16__list_cond b -> LogMeasInfo_r16__cond (LogMeasInfo_r16__F2 b) /\ LogMeasInfo_r16__F1 (LogMeasInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LogMeasInfo_r16__cond, LogMeasInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LogMeasInfo_r16__Format : T_Format LogMeasInfo_r16__Type LogMeasInfo_r16__cond :=
 proj2_format LogMeasInfo_r16__cond LogMeasInfo_r16__list_format  LogMeasInfo_r16__F1 LogMeasInfo_r16__F2 LogMeasInfo_r16__helper1 LogMeasInfo_r16__helper2 LogMeasInfo_r16__helper3.

Opaque LogMeasInfo_r16__cond LogMeasInfo_r16__Format.

