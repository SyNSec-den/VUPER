Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReportConfigId.

Opaque ReportConfigId__cond ReportConfigId__Format.

Require Import NR.ReportConfigNR.

Opaque ReportConfigNR__cond ReportConfigNR__Format.


Inductive ReportConfigToAddMod__reportConfig__root__Type : Set := | ReportConfigToAddMod__reportConfig__root__reportConfigNR : ReportConfigNR__Type -> ReportConfigToAddMod__reportConfig__root__Type.
Definition ReportConfigToAddMod__reportConfig__root__cond (c : ReportConfigToAddMod__reportConfig__root__Type) := 
  match c with
  | ReportConfigToAddMod__reportConfig__root__reportConfigNR t => ReportConfigNR__cond t 
  end.

Require Import NR.ReportConfigInterRAT.

Opaque ReportConfigInterRAT__cond ReportConfigInterRAT__Format.

Require Import NR.ReportConfigNR_SL_r16.

Opaque ReportConfigNR_SL_r16__cond ReportConfigNR_SL_r16__Format.


Inductive ReportConfigToAddMod__reportConfig__ext__Type : Set :=
  | ReportConfigToAddMod__reportConfig__ext__reportConfigInterRAT : ReportConfigInterRAT__Type -> ReportConfigToAddMod__reportConfig__ext__Type
  | ReportConfigToAddMod__reportConfig__ext__reportConfigNR_SL_r16 : ReportConfigNR_SL_r16__Type -> ReportConfigToAddMod__reportConfig__ext__Type
.
Definition ReportConfigToAddMod__reportConfig__ext__list : list typ := (
typ_cons ReportConfigInterRAT__Type ReportConfigInterRAT__cond ::
typ_cons ReportConfigNR_SL_r16__Type ReportConfigNR_SL_r16__cond ::
 nil).
Definition ReportConfigToAddMod__reportConfig__ext__cond (c : ReportConfigToAddMod__reportConfig__ext__Type) := 
  match c with
  | ReportConfigToAddMod__reportConfig__ext__reportConfigInterRAT t => ReportConfigInterRAT__cond t 
  | ReportConfigToAddMod__reportConfig__ext__reportConfigNR_SL_r16 t => ReportConfigNR_SL_r16__cond t 
  end.

Lemma ReportConfigToAddMod__reportConfig__ext__len_helper1 : to_bit_sz (length ReportConfigToAddMod__reportConfig__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition ReportConfigToAddMod__reportConfig__Type : Set := ReportConfigToAddMod__reportConfig__root__Type + ReportConfigToAddMod__reportConfig__ext__Type.
Definition ReportConfigToAddMod__reportConfig__cond :=
  sum_cond ReportConfigToAddMod__reportConfig__root__cond ReportConfigToAddMod__reportConfig__ext__cond.
Record ReportConfigToAddMod__Type : Set :=
  make__ReportConfigToAddMod__Type {
    ReportConfigToAddMod__reportConfigId : ReportConfigId__Type ;
    ReportConfigToAddMod__reportConfig : ReportConfigToAddMod__reportConfig__Type ;
}.
Definition ReportConfigToAddMod__list := (
 Nor ReportConfigId__Type ReportConfigId__cond ::
 Nor ReportConfigToAddMod__reportConfig__Type ReportConfigToAddMod__reportConfig__cond ::
 nil).
Definition ReportConfigToAddMod__cond z := 
  ReportConfigId__cond (ReportConfigToAddMod__reportConfigId z) /\
  ReportConfigToAddMod__reportConfig__cond (ReportConfigToAddMod__reportConfig z) /\
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
Definition ReportConfigToAddMod__reportConfig__root__F1 (z : ReportConfigToAddMod__reportConfig__root__Type) : ReportConfigNR__Type := 
  match z with
  | ReportConfigToAddMod__reportConfig__root__reportConfigNR t => t
  end.
Definition ReportConfigToAddMod__reportConfig__root__F2 (y : ReportConfigNR__Type) : ReportConfigToAddMod__reportConfig__root__Type := ReportConfigToAddMod__reportConfig__root__reportConfigNR y.

Definition ReportConfigToAddMod__reportConfig__root__helper2 : (forall z : ReportConfigToAddMod__reportConfig__root__Type, ReportConfigToAddMod__reportConfig__root__cond z -> ReportConfigNR__cond (ReportConfigToAddMod__reportConfig__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition ReportConfigToAddMod__reportConfig__root__helper3 : (forall z : ReportConfigToAddMod__reportConfig__root__Type, ReportConfigToAddMod__reportConfig__root__F2 (ReportConfigToAddMod__reportConfig__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition ReportConfigToAddMod__reportConfig__root__helper4 : (forall y : ReportConfigNR__Type, ReportConfigNR__cond y -> ReportConfigToAddMod__reportConfig__root__cond (ReportConfigToAddMod__reportConfig__root__F2 y) /\  ReportConfigToAddMod__reportConfig__root__F1 (ReportConfigToAddMod__reportConfig__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition ReportConfigToAddMod__reportConfig__root__Format : T_Format ReportConfigToAddMod__reportConfig__root__Type ReportConfigToAddMod__reportConfig__root__cond :=
  proj2_format ReportConfigToAddMod__reportConfig__root__cond ReportConfigNR__Format ReportConfigToAddMod__reportConfig__root__F1 ReportConfigToAddMod__reportConfig__root__F2 ReportConfigToAddMod__reportConfig__root__helper2 ReportConfigToAddMod__reportConfig__root__helper3 ReportConfigToAddMod__reportConfig__root__helper4.
Opaque ReportConfigToAddMod__reportConfig__root__cond ReportConfigToAddMod__reportConfig__root__Format.


Definition ReportConfigToAddMod__reportConfig__ext__Format_Type := Eval cbn in get_formats ReportConfigToAddMod__reportConfig__ext__list.
Definition ReportConfigToAddMod__reportConfig__ext__Format_list : ReportConfigToAddMod__reportConfig__ext__Format_Type :=
  (ReportConfigInterRAT__Format, (ReportConfigNR_SL_r16__Format, unit__Format)).
Definition ReportConfigToAddMod__reportConfig__ext__list__Format := Eval compute in choice_ext_format ReportConfigToAddMod__reportConfig__ext__list ReportConfigToAddMod__reportConfig__ext__Format_list.
Definition ReportConfigToAddMod__reportConfig__ext__F1 (z : ReportConfigToAddMod__reportConfig__ext__Type) : (choice ReportConfigToAddMod__reportConfig__ext__list) :=
  match z with
   | ReportConfigToAddMod__reportConfig__ext__reportConfigInterRAT t => existT _ 0 t
  | ReportConfigToAddMod__reportConfig__ext__reportConfigNR_SL_r16 t => existT _ 1 t
  end.
Definition ReportConfigToAddMod__reportConfig__ext__g := (fun n => typ_set (get_nth_typ ReportConfigToAddMod__reportConfig__ext__list n)).
Definition ReportConfigToAddMod__reportConfig__ext__F2 (y : choice ReportConfigToAddMod__reportConfig__ext__list) : ReportConfigToAddMod__reportConfig__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReportConfigToAddMod__reportConfig__ext__g n -> ReportConfigToAddMod__reportConfig__ext__Type) with
    | 0 => fun (t : ReportConfigInterRAT__Type) => ReportConfigToAddMod__reportConfig__ext__reportConfigInterRAT t 
    | 1 => fun (t : ReportConfigNR_SL_r16__Type) => ReportConfigToAddMod__reportConfig__ext__reportConfigNR_SL_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ReportConfigToAddMod__reportConfig__ext__g (S (S x'))) =>let t' :=
                       eq_rect (get_nth_typ ReportConfigToAddMod__reportConfig__ext__list (S (S x')))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len ReportConfigToAddMod__reportConfig__ext__list (S (S x'))
                       (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ReportConfigToAddMod__reportConfig__ext__Type with end) n0
                       end t0).

Lemma ReportConfigToAddMod__reportConfig__ext__helper2 :  forall (y : ReportConfigToAddMod__reportConfig__ext__Type), ReportConfigToAddMod__reportConfig__ext__cond y -> choice_cond ReportConfigToAddMod__reportConfig__ext__list (ReportConfigToAddMod__reportConfig__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReportConfigToAddMod__reportConfig__ext__helper3 :  forall (y : ReportConfigToAddMod__reportConfig__ext__Type), ReportConfigToAddMod__reportConfig__ext__F2 (ReportConfigToAddMod__reportConfig__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReportConfigToAddMod__reportConfig__ext__helper4 : (forall b : choice ReportConfigToAddMod__reportConfig__ext__list, choice_cond ReportConfigToAddMod__reportConfig__ext__list b -> ReportConfigToAddMod__reportConfig__ext__cond (ReportConfigToAddMod__reportConfig__ext__F2 b) /\ ReportConfigToAddMod__reportConfig__ext__F1 (ReportConfigToAddMod__reportConfig__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReportConfigToAddMod__reportConfig__ext__F1 ReportConfigToAddMod__reportConfig__ext__F2.
Definition ReportConfigToAddMod__reportConfig__ext__Format : T_Format ReportConfigToAddMod__reportConfig__ext__Type ReportConfigToAddMod__reportConfig__ext__cond :=
          proj2_format ReportConfigToAddMod__reportConfig__ext__cond ReportConfigToAddMod__reportConfig__ext__list__Format ReportConfigToAddMod__reportConfig__ext__F1 ReportConfigToAddMod__reportConfig__ext__F2 ReportConfigToAddMod__reportConfig__ext__helper2 ReportConfigToAddMod__reportConfig__ext__helper3 ReportConfigToAddMod__reportConfig__ext__helper4.
Opaque ReportConfigToAddMod__reportConfig__ext__cond ReportConfigToAddMod__reportConfig__ext__Format.

Definition ReportConfigToAddMod__reportConfig__Format : T_Format ReportConfigToAddMod__reportConfig__Type ReportConfigToAddMod__reportConfig__cond := sum_format ReportConfigToAddMod__reportConfig__root__Format ReportConfigToAddMod__reportConfig__ext__Format.
Opaque ReportConfigToAddMod__reportConfig__cond ReportConfigToAddMod__reportConfig__Format.


Definition ReportConfigToAddMod__Format_Type := Eval cbn in seq_format_prod ReportConfigToAddMod__list.
Definition ReportConfigToAddMod__Format_list : ReportConfigToAddMod__Format_Type :=
  (ReportConfigId__Format, (ReportConfigToAddMod__reportConfig__Format, unit_format)).
Definition ReportConfigToAddMod__list__Format := (*Eval compute in *) seq_format ReportConfigToAddMod__list ReportConfigToAddMod__Format_list.
Definition ReportConfigToAddMod__F1 z :=
  (ReportConfigToAddMod__reportConfigId z, (ReportConfigToAddMod__reportConfig z, tt)).
Definition ReportConfigToAddMod__F2 (y : seq_type ReportConfigToAddMod__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ReportConfigToAddMod__Type i0 i1
  end.
Lemma ReportConfigToAddMod__F1F2_cond (z : ReportConfigToAddMod__Type)
  : ReportConfigToAddMod__cond z ->
  (seq_cond ReportConfigToAddMod__list (ReportConfigToAddMod__F1 z)).
intro H. unfold ReportConfigToAddMod__cond in H. simpl. auto. Qed.
Lemma ReportConfigToAddMod__F1F2_cond2 (z : ReportConfigToAddMod__Type)
 : ReportConfigToAddMod__F2 (ReportConfigToAddMod__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReportConfigToAddMod__F2F1_cond (y : seq_type ReportConfigToAddMod__list)
  : seq_cond ReportConfigToAddMod__list y ->
 (ReportConfigToAddMod__cond (ReportConfigToAddMod__F2 y)) /\  ReportConfigToAddMod__F1 (ReportConfigToAddMod__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReportConfigToAddMod__cond. simpl in *. auto.
 - simpl. unfold ReportConfigToAddMod__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReportConfigToAddMod__Format : T_Format ReportConfigToAddMod__Type ReportConfigToAddMod__cond :=
        proj2_format  ReportConfigToAddMod__cond ReportConfigToAddMod__list__Format
    ReportConfigToAddMod__F1 ReportConfigToAddMod__F2 ReportConfigToAddMod__F1F2_cond  ReportConfigToAddMod__F1F2_cond2 ReportConfigToAddMod__F2F1_cond.
Opaque ReportConfigToAddMod__cond ReportConfigToAddMod__Format.

