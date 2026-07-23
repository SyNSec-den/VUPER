Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PeriodicalReportConfig.

Opaque PeriodicalReportConfig__cond PeriodicalReportConfig__Format.

Require Import NR.EventTriggerConfig.

Opaque EventTriggerConfig__cond EventTriggerConfig__Format.


Inductive ReportConfigNR__reportType__root__Type : Set :=
  | ReportConfigNR__reportType__root__periodical : PeriodicalReportConfig__Type -> ReportConfigNR__reportType__root__Type
  | ReportConfigNR__reportType__root__eventTriggered : EventTriggerConfig__Type -> ReportConfigNR__reportType__root__Type
.
Definition ReportConfigNR__reportType__root__list : list typ := (
typ_cons PeriodicalReportConfig__Type PeriodicalReportConfig__cond ::
typ_cons EventTriggerConfig__Type EventTriggerConfig__cond ::
 nil).
Definition ReportConfigNR__reportType__root__cond (c : ReportConfigNR__reportType__root__Type) := 
  match c with
  | ReportConfigNR__reportType__root__periodical t => PeriodicalReportConfig__cond t 
  | ReportConfigNR__reportType__root__eventTriggered t => EventTriggerConfig__cond t 
  end.

Lemma ReportConfigNR__reportType__root__len_helper1 : to_bit_sz (length ReportConfigNR__reportType__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ReportConfigNR__reportType__root__len_helper2 : 2 <= length2 ReportConfigNR__reportType__root__list.
 simpl. lia. Qed.
Require Import NR.ReportCGI.

Opaque ReportCGI__cond ReportCGI__Format.

Require Import NR.ReportSFTD_NR.

Opaque ReportSFTD_NR__cond ReportSFTD_NR__Format.

Require Import NR.CondTriggerConfig_r16.

Opaque CondTriggerConfig_r16__cond CondTriggerConfig_r16__Format.

Require Import NR.CLI_PeriodicalReportConfig_r16.

Opaque CLI_PeriodicalReportConfig_r16__cond CLI_PeriodicalReportConfig_r16__Format.

Require Import NR.CLI_EventTriggerConfig_r16.

Opaque CLI_EventTriggerConfig_r16__cond CLI_EventTriggerConfig_r16__Format.

Require Import NR.RxTxPeriodical_r17.

Opaque RxTxPeriodical_r17__cond RxTxPeriodical_r17__Format.


Inductive ReportConfigNR__reportType__ext__Type : Set :=
  | ReportConfigNR__reportType__ext__reportCGI : ReportCGI__Type -> ReportConfigNR__reportType__ext__Type
  | ReportConfigNR__reportType__ext__reportSFTD : ReportSFTD_NR__Type -> ReportConfigNR__reportType__ext__Type
  | ReportConfigNR__reportType__ext__condTriggerConfig_r16 : CondTriggerConfig_r16__Type -> ReportConfigNR__reportType__ext__Type
  | ReportConfigNR__reportType__ext__cli_Periodical_r16 : CLI_PeriodicalReportConfig_r16__Type -> ReportConfigNR__reportType__ext__Type
  | ReportConfigNR__reportType__ext__cli_EventTriggered_r16 : CLI_EventTriggerConfig_r16__Type -> ReportConfigNR__reportType__ext__Type
  | ReportConfigNR__reportType__ext__rxTxPeriodical_r17 : RxTxPeriodical_r17__Type -> ReportConfigNR__reportType__ext__Type
.
Definition ReportConfigNR__reportType__ext__list : list typ := (
typ_cons ReportCGI__Type ReportCGI__cond ::
typ_cons ReportSFTD_NR__Type ReportSFTD_NR__cond ::
typ_cons CondTriggerConfig_r16__Type CondTriggerConfig_r16__cond ::
typ_cons CLI_PeriodicalReportConfig_r16__Type CLI_PeriodicalReportConfig_r16__cond ::
typ_cons CLI_EventTriggerConfig_r16__Type CLI_EventTriggerConfig_r16__cond ::
typ_cons RxTxPeriodical_r17__Type RxTxPeriodical_r17__cond ::
 nil).
Definition ReportConfigNR__reportType__ext__cond (c : ReportConfigNR__reportType__ext__Type) := 
  match c with
  | ReportConfigNR__reportType__ext__reportCGI t => ReportCGI__cond t 
  | ReportConfigNR__reportType__ext__reportSFTD t => ReportSFTD_NR__cond t 
  | ReportConfigNR__reportType__ext__condTriggerConfig_r16 t => CondTriggerConfig_r16__cond t 
  | ReportConfigNR__reportType__ext__cli_Periodical_r16 t => CLI_PeriodicalReportConfig_r16__cond t 
  | ReportConfigNR__reportType__ext__cli_EventTriggered_r16 t => CLI_EventTriggerConfig_r16__cond t 
  | ReportConfigNR__reportType__ext__rxTxPeriodical_r17 t => RxTxPeriodical_r17__cond t 
  end.

Lemma ReportConfigNR__reportType__ext__len_helper1 : to_bit_sz (length ReportConfigNR__reportType__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition ReportConfigNR__reportType__Type : Set := ReportConfigNR__reportType__root__Type + ReportConfigNR__reportType__ext__Type.
Definition ReportConfigNR__reportType__cond :=
  sum_cond ReportConfigNR__reportType__root__cond ReportConfigNR__reportType__ext__cond.
Record ReportConfigNR__Type : Set :=
  make__ReportConfigNR__Type {
    ReportConfigNR__reportType : ReportConfigNR__reportType__Type ;
}.
Definition ReportConfigNR__list := (
 Nor ReportConfigNR__reportType__Type ReportConfigNR__reportType__cond ::
 nil).
Definition ReportConfigNR__cond z := 
  ReportConfigNR__reportType__cond (ReportConfigNR__reportType z) /\
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

Definition ReportConfigNR__reportType__root__Format_Type := Eval cbn in get_formats ReportConfigNR__reportType__root__list.
Definition ReportConfigNR__reportType__root__Format_list : ReportConfigNR__reportType__root__Format_Type :=
  (PeriodicalReportConfig__Format, (EventTriggerConfig__Format, unit__Format)).
Definition ReportConfigNR__reportType__root__list__Format := Eval compute in choice_format ReportConfigNR__reportType__root__list ReportConfigNR__reportType__root__len_helper1 ReportConfigNR__reportType__root__len_helper2  ReportConfigNR__reportType__root__Format_list.
Definition ReportConfigNR__reportType__root__F1 (z : ReportConfigNR__reportType__root__Type) : (choice ReportConfigNR__reportType__root__list) :=
  match z with
   | ReportConfigNR__reportType__root__periodical t => existT _ 0 t
  | ReportConfigNR__reportType__root__eventTriggered t => existT _ 1 t
  end.
Definition ReportConfigNR__reportType__root__g := (fun n => typ_set (get_nth_typ ReportConfigNR__reportType__root__list n)).
Definition ReportConfigNR__reportType__root__F2 (y : choice ReportConfigNR__reportType__root__list) : ReportConfigNR__reportType__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReportConfigNR__reportType__root__g n -> ReportConfigNR__reportType__root__Type) with
    | 0 => fun (t : PeriodicalReportConfig__Type) => ReportConfigNR__reportType__root__periodical t 
    | 1 => fun (t : EventTriggerConfig__Type) => ReportConfigNR__reportType__root__eventTriggered t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ReportConfigNR__reportType__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ReportConfigNR__reportType__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ReportConfigNR__reportType__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ReportConfigNR__reportType__root__Type with end) n0
           end t0).

Lemma ReportConfigNR__reportType__root__helper2 :  forall (y : ReportConfigNR__reportType__root__Type), ReportConfigNR__reportType__root__cond y -> choice_cond ReportConfigNR__reportType__root__list (ReportConfigNR__reportType__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReportConfigNR__reportType__root__helper3 :  forall (y : ReportConfigNR__reportType__root__Type), ReportConfigNR__reportType__root__F2 (ReportConfigNR__reportType__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReportConfigNR__reportType__root__helper4 : (forall b : choice ReportConfigNR__reportType__root__list, choice_cond ReportConfigNR__reportType__root__list b -> ReportConfigNR__reportType__root__cond (ReportConfigNR__reportType__root__F2 b) /\ ReportConfigNR__reportType__root__F1 (ReportConfigNR__reportType__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReportConfigNR__reportType__root__F1 ReportConfigNR__reportType__root__F2.
Definition ReportConfigNR__reportType__root__Format : T_Format ReportConfigNR__reportType__root__Type ReportConfigNR__reportType__root__cond :=
  (* Eval compute in *) proj2_format ReportConfigNR__reportType__root__cond ReportConfigNR__reportType__root__list__Format ReportConfigNR__reportType__root__F1 ReportConfigNR__reportType__root__F2 ReportConfigNR__reportType__root__helper2 ReportConfigNR__reportType__root__helper3 ReportConfigNR__reportType__root__helper4.
Opaque ReportConfigNR__reportType__root__cond ReportConfigNR__reportType__root__Format.


Definition ReportConfigNR__reportType__ext__Format_Type := Eval cbn in get_formats ReportConfigNR__reportType__ext__list.
Definition ReportConfigNR__reportType__ext__Format_list : ReportConfigNR__reportType__ext__Format_Type :=
  (ReportCGI__Format, (ReportSFTD_NR__Format, (CondTriggerConfig_r16__Format, (CLI_PeriodicalReportConfig_r16__Format, (CLI_EventTriggerConfig_r16__Format, (RxTxPeriodical_r17__Format, unit__Format)))))).
Definition ReportConfigNR__reportType__ext__list__Format := Eval compute in choice_ext_format ReportConfigNR__reportType__ext__list ReportConfigNR__reportType__ext__Format_list.
Definition ReportConfigNR__reportType__ext__F1 (z : ReportConfigNR__reportType__ext__Type) : (choice ReportConfigNR__reportType__ext__list) :=
  match z with
   | ReportConfigNR__reportType__ext__reportCGI t => existT _ 0 t
  | ReportConfigNR__reportType__ext__reportSFTD t => existT _ 1 t
  | ReportConfigNR__reportType__ext__condTriggerConfig_r16 t => existT _ 2 t
  | ReportConfigNR__reportType__ext__cli_Periodical_r16 t => existT _ 3 t
  | ReportConfigNR__reportType__ext__cli_EventTriggered_r16 t => existT _ 4 t
  | ReportConfigNR__reportType__ext__rxTxPeriodical_r17 t => existT _ 5 t
  end.
Definition ReportConfigNR__reportType__ext__g := (fun n => typ_set (get_nth_typ ReportConfigNR__reportType__ext__list n)).
Definition ReportConfigNR__reportType__ext__F2 (y : choice ReportConfigNR__reportType__ext__list) : ReportConfigNR__reportType__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReportConfigNR__reportType__ext__g n -> ReportConfigNR__reportType__ext__Type) with
    | 0 => fun (t : ReportCGI__Type) => ReportConfigNR__reportType__ext__reportCGI t 
    | 1 => fun (t : ReportSFTD_NR__Type) => ReportConfigNR__reportType__ext__reportSFTD t 
    | 2 => fun (t : CondTriggerConfig_r16__Type) => ReportConfigNR__reportType__ext__condTriggerConfig_r16 t 
    | 3 => fun (t : CLI_PeriodicalReportConfig_r16__Type) => ReportConfigNR__reportType__ext__cli_Periodical_r16 t 
    | 4 => fun (t : CLI_EventTriggerConfig_r16__Type) => ReportConfigNR__reportType__ext__cli_EventTriggered_r16 t 
    | 5 => fun (t : RxTxPeriodical_r17__Type) => ReportConfigNR__reportType__ext__rxTxPeriodical_r17 t 
 | (S (S (S (S (S (S n0)))))) => (fun (x' : nat) (t'' : ReportConfigNR__reportType__ext__g (S (S (S (S (S (S x'))))))) =>let t' :=
                       eq_rect (get_nth_typ ReportConfigNR__reportType__ext__list (S (S (S (S (S (S x')))))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len ReportConfigNR__reportType__ext__list (S (S (S (S (S (S x'))))))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))) in match t' return ReportConfigNR__reportType__ext__Type with end) n0
                       end t0).

Lemma ReportConfigNR__reportType__ext__helper2 :  forall (y : ReportConfigNR__reportType__ext__Type), ReportConfigNR__reportType__ext__cond y -> choice_cond ReportConfigNR__reportType__ext__list (ReportConfigNR__reportType__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReportConfigNR__reportType__ext__helper3 :  forall (y : ReportConfigNR__reportType__ext__Type), ReportConfigNR__reportType__ext__F2 (ReportConfigNR__reportType__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReportConfigNR__reportType__ext__helper4 : (forall b : choice ReportConfigNR__reportType__ext__list, choice_cond ReportConfigNR__reportType__ext__list b -> ReportConfigNR__reportType__ext__cond (ReportConfigNR__reportType__ext__F2 b) /\ ReportConfigNR__reportType__ext__F1 (ReportConfigNR__reportType__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReportConfigNR__reportType__ext__F1 ReportConfigNR__reportType__ext__F2.
Definition ReportConfigNR__reportType__ext__Format : T_Format ReportConfigNR__reportType__ext__Type ReportConfigNR__reportType__ext__cond :=
          proj2_format ReportConfigNR__reportType__ext__cond ReportConfigNR__reportType__ext__list__Format ReportConfigNR__reportType__ext__F1 ReportConfigNR__reportType__ext__F2 ReportConfigNR__reportType__ext__helper2 ReportConfigNR__reportType__ext__helper3 ReportConfigNR__reportType__ext__helper4.
Opaque ReportConfigNR__reportType__ext__cond ReportConfigNR__reportType__ext__Format.

Definition ReportConfigNR__reportType__Format : T_Format ReportConfigNR__reportType__Type ReportConfigNR__reportType__cond := sum_format ReportConfigNR__reportType__root__Format ReportConfigNR__reportType__ext__Format.
Opaque ReportConfigNR__reportType__cond ReportConfigNR__reportType__Format.


Definition ReportConfigNR__Format_Type := Eval cbn in seq_format_prod ReportConfigNR__list.
Definition ReportConfigNR__Format_list : ReportConfigNR__Format_Type :=
  (ReportConfigNR__reportType__Format, unit_format).
Definition ReportConfigNR__list__Format := (*Eval compute in *) seq_format ReportConfigNR__list ReportConfigNR__Format_list.
Definition ReportConfigNR__F1 z :=
  (ReportConfigNR__reportType z, tt).
Definition ReportConfigNR__F2 (y : seq_type ReportConfigNR__list) :=
  match y with
  | (i0, _)=>
    make__ReportConfigNR__Type i0
  end.
Lemma ReportConfigNR__F1F2_cond (z : ReportConfigNR__Type)
  : ReportConfigNR__cond z ->
  (seq_cond ReportConfigNR__list (ReportConfigNR__F1 z)).
intro H. unfold ReportConfigNR__cond in H. simpl. auto. Qed.
Lemma ReportConfigNR__F1F2_cond2 (z : ReportConfigNR__Type)
 : ReportConfigNR__F2 (ReportConfigNR__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReportConfigNR__F2F1_cond (y : seq_type ReportConfigNR__list)
  : seq_cond ReportConfigNR__list y ->
 (ReportConfigNR__cond (ReportConfigNR__F2 y)) /\  ReportConfigNR__F1 (ReportConfigNR__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReportConfigNR__cond. simpl in *. auto.
 - simpl. unfold ReportConfigNR__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReportConfigNR__Format : T_Format ReportConfigNR__Type ReportConfigNR__cond :=
        proj2_format  ReportConfigNR__cond ReportConfigNR__list__Format
    ReportConfigNR__F1 ReportConfigNR__F2 ReportConfigNR__F1F2_cond  ReportConfigNR__F1F2_cond2 ReportConfigNR__F2F1_cond.
Opaque ReportConfigNR__cond ReportConfigNR__Format.

