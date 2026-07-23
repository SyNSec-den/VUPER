Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PeriodicalReportConfigInterRAT.

Opaque PeriodicalReportConfigInterRAT__cond PeriodicalReportConfigInterRAT__Format.

Require Import NR.EventTriggerConfigInterRAT.

Opaque EventTriggerConfigInterRAT__cond EventTriggerConfigInterRAT__Format.

Require Import NR.ReportCGI_EUTRA.

Opaque ReportCGI_EUTRA__cond ReportCGI_EUTRA__Format.


Inductive ReportConfigInterRAT__reportType__root__Type : Set :=
  | ReportConfigInterRAT__reportType__root__periodical : PeriodicalReportConfigInterRAT__Type -> ReportConfigInterRAT__reportType__root__Type
  | ReportConfigInterRAT__reportType__root__eventTriggered : EventTriggerConfigInterRAT__Type -> ReportConfigInterRAT__reportType__root__Type
  | ReportConfigInterRAT__reportType__root__reportCGI : ReportCGI_EUTRA__Type -> ReportConfigInterRAT__reportType__root__Type
.
Definition ReportConfigInterRAT__reportType__root__list : list typ := (
typ_cons PeriodicalReportConfigInterRAT__Type PeriodicalReportConfigInterRAT__cond ::
typ_cons EventTriggerConfigInterRAT__Type EventTriggerConfigInterRAT__cond ::
typ_cons ReportCGI_EUTRA__Type ReportCGI_EUTRA__cond ::
 nil).
Definition ReportConfigInterRAT__reportType__root__cond (c : ReportConfigInterRAT__reportType__root__Type) := 
  match c with
  | ReportConfigInterRAT__reportType__root__periodical t => PeriodicalReportConfigInterRAT__cond t 
  | ReportConfigInterRAT__reportType__root__eventTriggered t => EventTriggerConfigInterRAT__cond t 
  | ReportConfigInterRAT__reportType__root__reportCGI t => ReportCGI_EUTRA__cond t 
  end.

Lemma ReportConfigInterRAT__reportType__root__len_helper1 : to_bit_sz (length ReportConfigInterRAT__reportType__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ReportConfigInterRAT__reportType__root__len_helper2 : 2 <= length2 ReportConfigInterRAT__reportType__root__list.
 simpl. lia. Qed.
Require Import NR.ReportSFTD_EUTRA.

Opaque ReportSFTD_EUTRA__cond ReportSFTD_EUTRA__Format.


Inductive ReportConfigInterRAT__reportType__ext__Type : Set :=
  | ReportConfigInterRAT__reportType__ext__reportSFTD : ReportSFTD_EUTRA__Type -> ReportConfigInterRAT__reportType__ext__Type
.
Definition ReportConfigInterRAT__reportType__ext__list : list typ := (
typ_cons ReportSFTD_EUTRA__Type ReportSFTD_EUTRA__cond ::
 nil).
Definition ReportConfigInterRAT__reportType__ext__cond (c : ReportConfigInterRAT__reportType__ext__Type) := 
  match c with
  | ReportConfigInterRAT__reportType__ext__reportSFTD t => ReportSFTD_EUTRA__cond t 
  end.

Lemma ReportConfigInterRAT__reportType__ext__len_helper1 : to_bit_sz (length ReportConfigInterRAT__reportType__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition ReportConfigInterRAT__reportType__Type : Set := ReportConfigInterRAT__reportType__root__Type + ReportConfigInterRAT__reportType__ext__Type.
Definition ReportConfigInterRAT__reportType__cond :=
  sum_cond ReportConfigInterRAT__reportType__root__cond ReportConfigInterRAT__reportType__ext__cond.
Record ReportConfigInterRAT__Type : Set :=
  make__ReportConfigInterRAT__Type {
    ReportConfigInterRAT__reportType : ReportConfigInterRAT__reportType__Type ;
}.
Definition ReportConfigInterRAT__list := (
 Nor ReportConfigInterRAT__reportType__Type ReportConfigInterRAT__reportType__cond ::
 nil).
Definition ReportConfigInterRAT__cond z := 
  ReportConfigInterRAT__reportType__cond (ReportConfigInterRAT__reportType z) /\
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

Definition ReportConfigInterRAT__reportType__root__Format_Type := Eval cbn in get_formats ReportConfigInterRAT__reportType__root__list.
Definition ReportConfigInterRAT__reportType__root__Format_list : ReportConfigInterRAT__reportType__root__Format_Type :=
  (PeriodicalReportConfigInterRAT__Format, (EventTriggerConfigInterRAT__Format, (ReportCGI_EUTRA__Format, unit__Format))).
Definition ReportConfigInterRAT__reportType__root__list__Format := Eval compute in choice_format ReportConfigInterRAT__reportType__root__list ReportConfigInterRAT__reportType__root__len_helper1 ReportConfigInterRAT__reportType__root__len_helper2  ReportConfigInterRAT__reportType__root__Format_list.
Definition ReportConfigInterRAT__reportType__root__F1 (z : ReportConfigInterRAT__reportType__root__Type) : (choice ReportConfigInterRAT__reportType__root__list) :=
  match z with
   | ReportConfigInterRAT__reportType__root__periodical t => existT _ 0 t
  | ReportConfigInterRAT__reportType__root__eventTriggered t => existT _ 1 t
  | ReportConfigInterRAT__reportType__root__reportCGI t => existT _ 2 t
  end.
Definition ReportConfigInterRAT__reportType__root__g := (fun n => typ_set (get_nth_typ ReportConfigInterRAT__reportType__root__list n)).
Definition ReportConfigInterRAT__reportType__root__F2 (y : choice ReportConfigInterRAT__reportType__root__list) : ReportConfigInterRAT__reportType__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReportConfigInterRAT__reportType__root__g n -> ReportConfigInterRAT__reportType__root__Type) with
    | 0 => fun (t : PeriodicalReportConfigInterRAT__Type) => ReportConfigInterRAT__reportType__root__periodical t 
    | 1 => fun (t : EventTriggerConfigInterRAT__Type) => ReportConfigInterRAT__reportType__root__eventTriggered t 
    | 2 => fun (t : ReportCGI_EUTRA__Type) => ReportConfigInterRAT__reportType__root__reportCGI t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : ReportConfigInterRAT__reportType__root__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ ReportConfigInterRAT__reportType__root__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ReportConfigInterRAT__reportType__root__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return ReportConfigInterRAT__reportType__root__Type with end) n0
           end t0).

Lemma ReportConfigInterRAT__reportType__root__helper2 :  forall (y : ReportConfigInterRAT__reportType__root__Type), ReportConfigInterRAT__reportType__root__cond y -> choice_cond ReportConfigInterRAT__reportType__root__list (ReportConfigInterRAT__reportType__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReportConfigInterRAT__reportType__root__helper3 :  forall (y : ReportConfigInterRAT__reportType__root__Type), ReportConfigInterRAT__reportType__root__F2 (ReportConfigInterRAT__reportType__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReportConfigInterRAT__reportType__root__helper4 : (forall b : choice ReportConfigInterRAT__reportType__root__list, choice_cond ReportConfigInterRAT__reportType__root__list b -> ReportConfigInterRAT__reportType__root__cond (ReportConfigInterRAT__reportType__root__F2 b) /\ ReportConfigInterRAT__reportType__root__F1 (ReportConfigInterRAT__reportType__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReportConfigInterRAT__reportType__root__F1 ReportConfigInterRAT__reportType__root__F2.
Definition ReportConfigInterRAT__reportType__root__Format : T_Format ReportConfigInterRAT__reportType__root__Type ReportConfigInterRAT__reportType__root__cond :=
  (* Eval compute in *) proj2_format ReportConfigInterRAT__reportType__root__cond ReportConfigInterRAT__reportType__root__list__Format ReportConfigInterRAT__reportType__root__F1 ReportConfigInterRAT__reportType__root__F2 ReportConfigInterRAT__reportType__root__helper2 ReportConfigInterRAT__reportType__root__helper3 ReportConfigInterRAT__reportType__root__helper4.
Opaque ReportConfigInterRAT__reportType__root__cond ReportConfigInterRAT__reportType__root__Format.


Definition ReportConfigInterRAT__reportType__ext__Format_Type := Eval cbn in get_formats ReportConfigInterRAT__reportType__ext__list.
Definition ReportConfigInterRAT__reportType__ext__Format_list : ReportConfigInterRAT__reportType__ext__Format_Type :=
  (ReportSFTD_EUTRA__Format, unit__Format).
Definition ReportConfigInterRAT__reportType__ext__list__Format := Eval compute in choice_ext_format ReportConfigInterRAT__reportType__ext__list ReportConfigInterRAT__reportType__ext__Format_list.
Definition ReportConfigInterRAT__reportType__ext__F1 (z : ReportConfigInterRAT__reportType__ext__Type) : (choice ReportConfigInterRAT__reportType__ext__list) :=
  match z with
   | ReportConfigInterRAT__reportType__ext__reportSFTD t => existT _ 0 t
  end.
Definition ReportConfigInterRAT__reportType__ext__g := (fun n => typ_set (get_nth_typ ReportConfigInterRAT__reportType__ext__list n)).
Definition ReportConfigInterRAT__reportType__ext__F2 (y : choice ReportConfigInterRAT__reportType__ext__list) : ReportConfigInterRAT__reportType__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReportConfigInterRAT__reportType__ext__g n -> ReportConfigInterRAT__reportType__ext__Type) with
    | 0 => fun (t : ReportSFTD_EUTRA__Type) => ReportConfigInterRAT__reportType__ext__reportSFTD t 
 | (S n0) => (fun (x' : nat) (t'' : ReportConfigInterRAT__reportType__ext__g (S x')) =>let t' :=
                       eq_rect (get_nth_typ ReportConfigInterRAT__reportType__ext__list (S x'))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len ReportConfigInterRAT__reportType__ext__list (S x')
                       (le_n_S _ _ (le_0_n x'))) in match t' return ReportConfigInterRAT__reportType__ext__Type with end) n0
                       end t0).

Lemma ReportConfigInterRAT__reportType__ext__helper2 :  forall (y : ReportConfigInterRAT__reportType__ext__Type), ReportConfigInterRAT__reportType__ext__cond y -> choice_cond ReportConfigInterRAT__reportType__ext__list (ReportConfigInterRAT__reportType__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReportConfigInterRAT__reportType__ext__helper3 :  forall (y : ReportConfigInterRAT__reportType__ext__Type), ReportConfigInterRAT__reportType__ext__F2 (ReportConfigInterRAT__reportType__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReportConfigInterRAT__reportType__ext__helper4 : (forall b : choice ReportConfigInterRAT__reportType__ext__list, choice_cond ReportConfigInterRAT__reportType__ext__list b -> ReportConfigInterRAT__reportType__ext__cond (ReportConfigInterRAT__reportType__ext__F2 b) /\ ReportConfigInterRAT__reportType__ext__F1 (ReportConfigInterRAT__reportType__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReportConfigInterRAT__reportType__ext__F1 ReportConfigInterRAT__reportType__ext__F2.
Definition ReportConfigInterRAT__reportType__ext__Format : T_Format ReportConfigInterRAT__reportType__ext__Type ReportConfigInterRAT__reportType__ext__cond :=
          proj2_format ReportConfigInterRAT__reportType__ext__cond ReportConfigInterRAT__reportType__ext__list__Format ReportConfigInterRAT__reportType__ext__F1 ReportConfigInterRAT__reportType__ext__F2 ReportConfigInterRAT__reportType__ext__helper2 ReportConfigInterRAT__reportType__ext__helper3 ReportConfigInterRAT__reportType__ext__helper4.
Opaque ReportConfigInterRAT__reportType__ext__cond ReportConfigInterRAT__reportType__ext__Format.

Definition ReportConfigInterRAT__reportType__Format : T_Format ReportConfigInterRAT__reportType__Type ReportConfigInterRAT__reportType__cond := sum_format ReportConfigInterRAT__reportType__root__Format ReportConfigInterRAT__reportType__ext__Format.
Opaque ReportConfigInterRAT__reportType__cond ReportConfigInterRAT__reportType__Format.


Definition ReportConfigInterRAT__Format_Type := Eval cbn in seq_format_prod ReportConfigInterRAT__list.
Definition ReportConfigInterRAT__Format_list : ReportConfigInterRAT__Format_Type :=
  (ReportConfigInterRAT__reportType__Format, unit_format).
Definition ReportConfigInterRAT__list__Format := (*Eval compute in *) seq_format ReportConfigInterRAT__list ReportConfigInterRAT__Format_list.
Definition ReportConfigInterRAT__F1 z :=
  (ReportConfigInterRAT__reportType z, tt).
Definition ReportConfigInterRAT__F2 (y : seq_type ReportConfigInterRAT__list) :=
  match y with
  | (i0, _)=>
    make__ReportConfigInterRAT__Type i0
  end.
Lemma ReportConfigInterRAT__F1F2_cond (z : ReportConfigInterRAT__Type)
  : ReportConfigInterRAT__cond z ->
  (seq_cond ReportConfigInterRAT__list (ReportConfigInterRAT__F1 z)).
intro H. unfold ReportConfigInterRAT__cond in H. simpl. auto. Qed.
Lemma ReportConfigInterRAT__F1F2_cond2 (z : ReportConfigInterRAT__Type)
 : ReportConfigInterRAT__F2 (ReportConfigInterRAT__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReportConfigInterRAT__F2F1_cond (y : seq_type ReportConfigInterRAT__list)
  : seq_cond ReportConfigInterRAT__list y ->
 (ReportConfigInterRAT__cond (ReportConfigInterRAT__F2 y)) /\  ReportConfigInterRAT__F1 (ReportConfigInterRAT__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReportConfigInterRAT__cond. simpl in *. auto.
 - simpl. unfold ReportConfigInterRAT__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReportConfigInterRAT__Format : T_Format ReportConfigInterRAT__Type ReportConfigInterRAT__cond :=
        proj2_format  ReportConfigInterRAT__cond ReportConfigInterRAT__list__Format
    ReportConfigInterRAT__F1 ReportConfigInterRAT__F2 ReportConfigInterRAT__F1F2_cond  ReportConfigInterRAT__F1F2_cond2 ReportConfigInterRAT__F2F1_cond.
Opaque ReportConfigInterRAT__cond ReportConfigInterRAT__Format.

