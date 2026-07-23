Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_PeriodicalReportConfig_r16.

Opaque SL_PeriodicalReportConfig_r16__cond SL_PeriodicalReportConfig_r16__Format.

Require Import NR.SL_EventTriggerConfig_r16.

Opaque SL_EventTriggerConfig_r16__cond SL_EventTriggerConfig_r16__Format.


Inductive SL_ReportConfig_r16__sl_ReportType_r16__root__Type : Set :=
  | SL_ReportConfig_r16__sl_ReportType_r16__root__sl_Periodical_r16 : SL_PeriodicalReportConfig_r16__Type -> SL_ReportConfig_r16__sl_ReportType_r16__root__Type
  | SL_ReportConfig_r16__sl_ReportType_r16__root__sl_EventTriggered_r16 : SL_EventTriggerConfig_r16__Type -> SL_ReportConfig_r16__sl_ReportType_r16__root__Type
.
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__list : list typ := (
typ_cons SL_PeriodicalReportConfig_r16__Type SL_PeriodicalReportConfig_r16__cond ::
typ_cons SL_EventTriggerConfig_r16__Type SL_EventTriggerConfig_r16__cond ::
 nil).
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__cond (c : SL_ReportConfig_r16__sl_ReportType_r16__root__Type) := 
  match c with
  | SL_ReportConfig_r16__sl_ReportType_r16__root__sl_Periodical_r16 t => SL_PeriodicalReportConfig_r16__cond t 
  | SL_ReportConfig_r16__sl_ReportType_r16__root__sl_EventTriggered_r16 t => SL_EventTriggerConfig_r16__cond t 
  end.

Lemma SL_ReportConfig_r16__sl_ReportType_r16__root__len_helper1 : to_bit_sz (length SL_ReportConfig_r16__sl_ReportType_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_ReportConfig_r16__sl_ReportType_r16__root__len_helper2 : 2 <= length2 SL_ReportConfig_r16__sl_ReportType_r16__root__list.
 simpl. lia. Qed.

Definition SL_ReportConfig_r16__sl_ReportType_r16__ext__Type : Set := Empty_set.
Definition SL_ReportConfig_r16__sl_ReportType_r16__ext__cond (c : SL_ReportConfig_r16__sl_ReportType_r16__ext__Type) := True.
Definition SL_ReportConfig_r16__sl_ReportType_r16__Type : Set := SL_ReportConfig_r16__sl_ReportType_r16__root__Type + SL_ReportConfig_r16__sl_ReportType_r16__ext__Type.
Definition SL_ReportConfig_r16__sl_ReportType_r16__cond :=
  sum_cond SL_ReportConfig_r16__sl_ReportType_r16__root__cond SL_ReportConfig_r16__sl_ReportType_r16__ext__cond.
Record SL_ReportConfig_r16__Type : Set :=
  make__SL_ReportConfig_r16__Type {
    SL_ReportConfig_r16__sl_ReportType_r16 : SL_ReportConfig_r16__sl_ReportType_r16__Type ;
}.
Definition SL_ReportConfig_r16__root_list : list seq_elem := (
 Nor SL_ReportConfig_r16__sl_ReportType_r16__Type SL_ReportConfig_r16__sl_ReportType_r16__cond ::
 nil).
Definition SL_ReportConfig_r16__ext_list : list typ := (
  nil).
Definition SL_ReportConfig_r16__cond (z : SL_ReportConfig_r16__Type) := 
(  SL_ReportConfig_r16__sl_ReportType_r16__cond (SL_ReportConfig_r16__sl_ReportType_r16 z) /\
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

Definition SL_ReportConfig_r16__sl_ReportType_r16__root__Format_Type := Eval cbn in get_formats SL_ReportConfig_r16__sl_ReportType_r16__root__list.
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__Format_list : SL_ReportConfig_r16__sl_ReportType_r16__root__Format_Type :=
  (SL_PeriodicalReportConfig_r16__Format, (SL_EventTriggerConfig_r16__Format, unit__Format)).
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__list__Format := Eval compute in choice_format SL_ReportConfig_r16__sl_ReportType_r16__root__list SL_ReportConfig_r16__sl_ReportType_r16__root__len_helper1 SL_ReportConfig_r16__sl_ReportType_r16__root__len_helper2  SL_ReportConfig_r16__sl_ReportType_r16__root__Format_list.
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__F1 (z : SL_ReportConfig_r16__sl_ReportType_r16__root__Type) : (choice SL_ReportConfig_r16__sl_ReportType_r16__root__list) :=
  match z with
   | SL_ReportConfig_r16__sl_ReportType_r16__root__sl_Periodical_r16 t => existT _ 0 t
  | SL_ReportConfig_r16__sl_ReportType_r16__root__sl_EventTriggered_r16 t => existT _ 1 t
  end.
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__g := (fun n => typ_set (get_nth_typ SL_ReportConfig_r16__sl_ReportType_r16__root__list n)).
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__F2 (y : choice SL_ReportConfig_r16__sl_ReportType_r16__root__list) : SL_ReportConfig_r16__sl_ReportType_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_ReportConfig_r16__sl_ReportType_r16__root__g n -> SL_ReportConfig_r16__sl_ReportType_r16__root__Type) with
    | 0 => fun (t : SL_PeriodicalReportConfig_r16__Type) => SL_ReportConfig_r16__sl_ReportType_r16__root__sl_Periodical_r16 t 
    | 1 => fun (t : SL_EventTriggerConfig_r16__Type) => SL_ReportConfig_r16__sl_ReportType_r16__root__sl_EventTriggered_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_ReportConfig_r16__sl_ReportType_r16__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_ReportConfig_r16__sl_ReportType_r16__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_ReportConfig_r16__sl_ReportType_r16__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_ReportConfig_r16__sl_ReportType_r16__root__Type with end) n0
           end t0).

Lemma SL_ReportConfig_r16__sl_ReportType_r16__root__helper2 :  forall (y : SL_ReportConfig_r16__sl_ReportType_r16__root__Type), SL_ReportConfig_r16__sl_ReportType_r16__root__cond y -> choice_cond SL_ReportConfig_r16__sl_ReportType_r16__root__list (SL_ReportConfig_r16__sl_ReportType_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_ReportConfig_r16__sl_ReportType_r16__root__helper3 :  forall (y : SL_ReportConfig_r16__sl_ReportType_r16__root__Type), SL_ReportConfig_r16__sl_ReportType_r16__root__F2 (SL_ReportConfig_r16__sl_ReportType_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_ReportConfig_r16__sl_ReportType_r16__root__helper4 : (forall b : choice SL_ReportConfig_r16__sl_ReportType_r16__root__list, choice_cond SL_ReportConfig_r16__sl_ReportType_r16__root__list b -> SL_ReportConfig_r16__sl_ReportType_r16__root__cond (SL_ReportConfig_r16__sl_ReportType_r16__root__F2 b) /\ SL_ReportConfig_r16__sl_ReportType_r16__root__F1 (SL_ReportConfig_r16__sl_ReportType_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_ReportConfig_r16__sl_ReportType_r16__root__F1 SL_ReportConfig_r16__sl_ReportType_r16__root__F2.
Definition SL_ReportConfig_r16__sl_ReportType_r16__root__Format : T_Format SL_ReportConfig_r16__sl_ReportType_r16__root__Type SL_ReportConfig_r16__sl_ReportType_r16__root__cond :=
  (* Eval compute in *) proj2_format SL_ReportConfig_r16__sl_ReportType_r16__root__cond SL_ReportConfig_r16__sl_ReportType_r16__root__list__Format SL_ReportConfig_r16__sl_ReportType_r16__root__F1 SL_ReportConfig_r16__sl_ReportType_r16__root__F2 SL_ReportConfig_r16__sl_ReportType_r16__root__helper2 SL_ReportConfig_r16__sl_ReportType_r16__root__helper3 SL_ReportConfig_r16__sl_ReportType_r16__root__helper4.
Opaque SL_ReportConfig_r16__sl_ReportType_r16__root__cond SL_ReportConfig_r16__sl_ReportType_r16__root__Format.

Definition SL_ReportConfig_r16__sl_ReportType_r16__ext__Format : T_Format SL_ReportConfig_r16__sl_ReportType_r16__ext__Type SL_ReportConfig_r16__sl_ReportType_r16__ext__cond := empty_format.
Opaque SL_ReportConfig_r16__sl_ReportType_r16__ext__cond SL_ReportConfig_r16__sl_ReportType_r16__ext__Format.

Definition SL_ReportConfig_r16__sl_ReportType_r16__Format : T_Format SL_ReportConfig_r16__sl_ReportType_r16__Type SL_ReportConfig_r16__sl_ReportType_r16__cond := sum_format SL_ReportConfig_r16__sl_ReportType_r16__root__Format SL_ReportConfig_r16__sl_ReportType_r16__ext__Format.
Opaque SL_ReportConfig_r16__sl_ReportType_r16__cond SL_ReportConfig_r16__sl_ReportType_r16__Format.


Definition SL_ReportConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_ReportConfig_r16__root_list.
Definition SL_ReportConfig_r16__root_Format_list : SL_ReportConfig_r16__root_Format_Type :=
  (SL_ReportConfig_r16__sl_ReportType_r16__Format, unit_format).

Definition SL_ReportConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_ReportConfig_r16__ext_list.
Definition SL_ReportConfig_r16__ext_Format_list : SL_ReportConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_ReportConfig_r16__list_type : Set := (seq_type SL_ReportConfig_r16__root_list) * (seq_ext_type SL_ReportConfig_r16__ext_list).
Definition SL_ReportConfig_r16__list_cond (z : SL_ReportConfig_r16__list_type) : Prop :=
        (seq_cond SL_ReportConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_ReportConfig_r16__ext_list (snd z)).
Definition SL_ReportConfig_r16__list_format : T_Format SL_ReportConfig_r16__list_type SL_ReportConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_ReportConfig_r16__root_list SL_ReportConfig_r16__root_Format_list SL_ReportConfig_r16__ext_list SL_ReportConfig_r16__ext_Format_list.

Opaque SL_ReportConfig_r16__list_format.
Definition SL_ReportConfig_r16__F1 (z : SL_ReportConfig_r16__Type) : SL_ReportConfig_r16__list_type :=
  (((SL_ReportConfig_r16__sl_ReportType_r16 z, tt)), (
tt)).
Definition SL_ReportConfig_r16__F2 (y : SL_ReportConfig_r16__list_type) : SL_ReportConfig_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__SL_ReportConfig_r16__Type j0
  end.
Definition SL_ReportConfig_r16__helper1 : (forall a : SL_ReportConfig_r16__Type, SL_ReportConfig_r16__cond a -> SL_ReportConfig_r16__list_cond (SL_ReportConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_ReportConfig_r16__helper2 : (forall a : SL_ReportConfig_r16__Type, SL_ReportConfig_r16__F2 (SL_ReportConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_ReportConfig_r16__helper3 : (forall b : SL_ReportConfig_r16__list_type, SL_ReportConfig_r16__list_cond b -> SL_ReportConfig_r16__cond (SL_ReportConfig_r16__F2 b) /\ SL_ReportConfig_r16__F1 (SL_ReportConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_ReportConfig_r16__cond, SL_ReportConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_ReportConfig_r16__Format : T_Format SL_ReportConfig_r16__Type SL_ReportConfig_r16__cond :=
 proj2_format SL_ReportConfig_r16__cond SL_ReportConfig_r16__list_format  SL_ReportConfig_r16__F1 SL_ReportConfig_r16__F2 SL_ReportConfig_r16__helper1 SL_ReportConfig_r16__helper2 SL_ReportConfig_r16__helper3.

Opaque SL_ReportConfig_r16__cond SL_ReportConfig_r16__Format.

