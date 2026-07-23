Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PeriodicalReportConfigNR_SL_r16.

Opaque PeriodicalReportConfigNR_SL_r16__cond PeriodicalReportConfigNR_SL_r16__Format.

Require Import NR.EventTriggerConfigNR_SL_r16.

Opaque EventTriggerConfigNR_SL_r16__cond EventTriggerConfigNR_SL_r16__Format.


Inductive ReportConfigNR_SL_r16__reportType_r16__Type : Set :=
  | ReportConfigNR_SL_r16__reportType_r16__periodical_r16 : PeriodicalReportConfigNR_SL_r16__Type -> ReportConfigNR_SL_r16__reportType_r16__Type
  | ReportConfigNR_SL_r16__reportType_r16__eventTriggered_r16 : EventTriggerConfigNR_SL_r16__Type -> ReportConfigNR_SL_r16__reportType_r16__Type
.
Definition ReportConfigNR_SL_r16__reportType_r16__list : list typ := (
typ_cons PeriodicalReportConfigNR_SL_r16__Type PeriodicalReportConfigNR_SL_r16__cond ::
typ_cons EventTriggerConfigNR_SL_r16__Type EventTriggerConfigNR_SL_r16__cond ::
 nil).
Definition ReportConfigNR_SL_r16__reportType_r16__cond (c : ReportConfigNR_SL_r16__reportType_r16__Type) := 
  match c with
  | ReportConfigNR_SL_r16__reportType_r16__periodical_r16 t => PeriodicalReportConfigNR_SL_r16__cond t 
  | ReportConfigNR_SL_r16__reportType_r16__eventTriggered_r16 t => EventTriggerConfigNR_SL_r16__cond t 
  end.

Lemma ReportConfigNR_SL_r16__reportType_r16__len_helper1 : to_bit_sz (length ReportConfigNR_SL_r16__reportType_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ReportConfigNR_SL_r16__reportType_r16__len_helper2 : 2 <= length2 ReportConfigNR_SL_r16__reportType_r16__list.
 simpl. lia. Qed.
Record ReportConfigNR_SL_r16__Type : Set :=
  make__ReportConfigNR_SL_r16__Type {
    ReportConfigNR_SL_r16__reportType_r16 : ReportConfigNR_SL_r16__reportType_r16__Type ;
}.
Definition ReportConfigNR_SL_r16__list := (
 Nor ReportConfigNR_SL_r16__reportType_r16__Type ReportConfigNR_SL_r16__reportType_r16__cond ::
 nil).
Definition ReportConfigNR_SL_r16__cond z := 
  ReportConfigNR_SL_r16__reportType_r16__cond (ReportConfigNR_SL_r16__reportType_r16 z) /\
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

Definition ReportConfigNR_SL_r16__reportType_r16__Format_Type := Eval cbn in get_formats ReportConfigNR_SL_r16__reportType_r16__list.
Definition ReportConfigNR_SL_r16__reportType_r16__Format_list : ReportConfigNR_SL_r16__reportType_r16__Format_Type :=
  (PeriodicalReportConfigNR_SL_r16__Format, (EventTriggerConfigNR_SL_r16__Format, unit__Format)).
Definition ReportConfigNR_SL_r16__reportType_r16__list__Format := Eval compute in choice_format ReportConfigNR_SL_r16__reportType_r16__list ReportConfigNR_SL_r16__reportType_r16__len_helper1 ReportConfigNR_SL_r16__reportType_r16__len_helper2  ReportConfigNR_SL_r16__reportType_r16__Format_list.
Definition ReportConfigNR_SL_r16__reportType_r16__F1 (z : ReportConfigNR_SL_r16__reportType_r16__Type) : (choice ReportConfigNR_SL_r16__reportType_r16__list) :=
  match z with
   | ReportConfigNR_SL_r16__reportType_r16__periodical_r16 t => existT _ 0 t
  | ReportConfigNR_SL_r16__reportType_r16__eventTriggered_r16 t => existT _ 1 t
  end.
Definition ReportConfigNR_SL_r16__reportType_r16__g := (fun n => typ_set (get_nth_typ ReportConfigNR_SL_r16__reportType_r16__list n)).
Definition ReportConfigNR_SL_r16__reportType_r16__F2 (y : choice ReportConfigNR_SL_r16__reportType_r16__list) : ReportConfigNR_SL_r16__reportType_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReportConfigNR_SL_r16__reportType_r16__g n -> ReportConfigNR_SL_r16__reportType_r16__Type) with
    | 0 => fun (t : PeriodicalReportConfigNR_SL_r16__Type) => ReportConfigNR_SL_r16__reportType_r16__periodical_r16 t 
    | 1 => fun (t : EventTriggerConfigNR_SL_r16__Type) => ReportConfigNR_SL_r16__reportType_r16__eventTriggered_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ReportConfigNR_SL_r16__reportType_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ReportConfigNR_SL_r16__reportType_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ReportConfigNR_SL_r16__reportType_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ReportConfigNR_SL_r16__reportType_r16__Type with end) n0
           end t0).

Lemma ReportConfigNR_SL_r16__reportType_r16__helper2 :  forall (y : ReportConfigNR_SL_r16__reportType_r16__Type), ReportConfigNR_SL_r16__reportType_r16__cond y -> choice_cond ReportConfigNR_SL_r16__reportType_r16__list (ReportConfigNR_SL_r16__reportType_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReportConfigNR_SL_r16__reportType_r16__helper3 :  forall (y : ReportConfigNR_SL_r16__reportType_r16__Type), ReportConfigNR_SL_r16__reportType_r16__F2 (ReportConfigNR_SL_r16__reportType_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReportConfigNR_SL_r16__reportType_r16__helper4 : (forall b : choice ReportConfigNR_SL_r16__reportType_r16__list, choice_cond ReportConfigNR_SL_r16__reportType_r16__list b -> ReportConfigNR_SL_r16__reportType_r16__cond (ReportConfigNR_SL_r16__reportType_r16__F2 b) /\ ReportConfigNR_SL_r16__reportType_r16__F1 (ReportConfigNR_SL_r16__reportType_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReportConfigNR_SL_r16__reportType_r16__F1 ReportConfigNR_SL_r16__reportType_r16__F2.
Definition ReportConfigNR_SL_r16__reportType_r16__Format : T_Format ReportConfigNR_SL_r16__reportType_r16__Type ReportConfigNR_SL_r16__reportType_r16__cond :=
  (* Eval compute in *) proj2_format ReportConfigNR_SL_r16__reportType_r16__cond ReportConfigNR_SL_r16__reportType_r16__list__Format ReportConfigNR_SL_r16__reportType_r16__F1 ReportConfigNR_SL_r16__reportType_r16__F2 ReportConfigNR_SL_r16__reportType_r16__helper2 ReportConfigNR_SL_r16__reportType_r16__helper3 ReportConfigNR_SL_r16__reportType_r16__helper4.
Opaque ReportConfigNR_SL_r16__reportType_r16__cond ReportConfigNR_SL_r16__reportType_r16__Format.


Definition ReportConfigNR_SL_r16__Format_Type := Eval cbn in seq_format_prod ReportConfigNR_SL_r16__list.
Definition ReportConfigNR_SL_r16__Format_list : ReportConfigNR_SL_r16__Format_Type :=
  (ReportConfigNR_SL_r16__reportType_r16__Format, unit_format).
Definition ReportConfigNR_SL_r16__list__Format := (*Eval compute in *) seq_format ReportConfigNR_SL_r16__list ReportConfigNR_SL_r16__Format_list.
Definition ReportConfigNR_SL_r16__F1 z :=
  (ReportConfigNR_SL_r16__reportType_r16 z, tt).
Definition ReportConfigNR_SL_r16__F2 (y : seq_type ReportConfigNR_SL_r16__list) :=
  match y with
  | (i0, _)=>
    make__ReportConfigNR_SL_r16__Type i0
  end.
Lemma ReportConfigNR_SL_r16__F1F2_cond (z : ReportConfigNR_SL_r16__Type)
  : ReportConfigNR_SL_r16__cond z ->
  (seq_cond ReportConfigNR_SL_r16__list (ReportConfigNR_SL_r16__F1 z)).
intro H. unfold ReportConfigNR_SL_r16__cond in H. simpl. auto. Qed.
Lemma ReportConfigNR_SL_r16__F1F2_cond2 (z : ReportConfigNR_SL_r16__Type)
 : ReportConfigNR_SL_r16__F2 (ReportConfigNR_SL_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReportConfigNR_SL_r16__F2F1_cond (y : seq_type ReportConfigNR_SL_r16__list)
  : seq_cond ReportConfigNR_SL_r16__list y ->
 (ReportConfigNR_SL_r16__cond (ReportConfigNR_SL_r16__F2 y)) /\  ReportConfigNR_SL_r16__F1 (ReportConfigNR_SL_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReportConfigNR_SL_r16__cond. simpl in *. auto.
 - simpl. unfold ReportConfigNR_SL_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReportConfigNR_SL_r16__Format : T_Format ReportConfigNR_SL_r16__Type ReportConfigNR_SL_r16__cond :=
        proj2_format  ReportConfigNR_SL_r16__cond ReportConfigNR_SL_r16__list__Format
    ReportConfigNR_SL_r16__F1 ReportConfigNR_SL_r16__F2 ReportConfigNR_SL_r16__F1F2_cond  ReportConfigNR_SL_r16__F1F2_cond2 ReportConfigNR_SL_r16__F2F1_cond.
Opaque ReportConfigNR_SL_r16__cond ReportConfigNR_SL_r16__Format.

