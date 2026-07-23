Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma UAC_BarringPerPLMN__plmn_IdentityIndex__helper1 : (1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma UAC_BarringPerPLMN__plmn_IdentityIndex__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UAC_BarringPerPLMN__plmn_IdentityIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UAC_BarringPerPLMN__plmn_IdentityIndex__Type := Z.
Definition UAC_BarringPerPLMN__plmn_IdentityIndex__cond := (fun z => (1 <= z <= maxPLMN)%Z).
Require Import NR.UAC_BarringInfoSetIndex.

Opaque UAC_BarringInfoSetIndex__cond UAC_BarringInfoSetIndex__Format.

Definition UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Type := list UAC_BarringInfoSetIndex__Type.

Definition UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__cond (z : UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Type) := (list_and UAC_BarringInfoSetIndex__cond z) /\ (length z = Z.to_nat maxAccessCat_1).

Require Import NR.UAC_BarringPerCatList.

Opaque UAC_BarringPerCatList__cond UAC_BarringPerCatList__Format.


Inductive UAC_BarringPerPLMN__uac_ACBarringListType__Type : Set :=
  | UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList : UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Type -> UAC_BarringPerPLMN__uac_ACBarringListType__Type
  | UAC_BarringPerPLMN__uac_ACBarringListType__uac_ExplicitACBarringList : UAC_BarringPerCatList__Type -> UAC_BarringPerPLMN__uac_ACBarringListType__Type
.
Definition UAC_BarringPerPLMN__uac_ACBarringListType__list : list typ := (
typ_cons UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Type UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__cond ::
typ_cons UAC_BarringPerCatList__Type UAC_BarringPerCatList__cond ::
 nil).
Definition UAC_BarringPerPLMN__uac_ACBarringListType__cond (c : UAC_BarringPerPLMN__uac_ACBarringListType__Type) := 
  match c with
  | UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList t => UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__cond t 
  | UAC_BarringPerPLMN__uac_ACBarringListType__uac_ExplicitACBarringList t => UAC_BarringPerCatList__cond t 
  end.

Lemma UAC_BarringPerPLMN__uac_ACBarringListType__len_helper1 : to_bit_sz (length UAC_BarringPerPLMN__uac_ACBarringListType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UAC_BarringPerPLMN__uac_ACBarringListType__len_helper2 : 2 <= length2 UAC_BarringPerPLMN__uac_ACBarringListType__list.
 simpl. lia. Qed.
Record UAC_BarringPerPLMN__Type : Set :=
  make__UAC_BarringPerPLMN__Type {
    UAC_BarringPerPLMN__plmn_IdentityIndex : Z ;
    UAC_BarringPerPLMN__uac_ACBarringListType : option UAC_BarringPerPLMN__uac_ACBarringListType__Type ;
}.
Definition UAC_BarringPerPLMN__list := (
 Nor Z UAC_BarringPerPLMN__plmn_IdentityIndex__cond ::
 Opt UAC_BarringPerPLMN__uac_ACBarringListType__Type UAC_BarringPerPLMN__uac_ACBarringListType__cond ::
 nil).
Definition UAC_BarringPerPLMN__cond z := 
  UAC_BarringPerPLMN__plmn_IdentityIndex__cond (UAC_BarringPerPLMN__plmn_IdentityIndex z) /\
  opt_cond UAC_BarringPerPLMN__uac_ACBarringListType__cond (UAC_BarringPerPLMN__uac_ACBarringListType z) /\
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
Definition UAC_BarringPerPLMN__plmn_IdentityIndex__Format : T_Format Z UAC_BarringPerPLMN__plmn_IdentityIndex__cond :=
 ranged_int_format (1) (maxPLMN) UAC_BarringPerPLMN__plmn_IdentityIndex__helper1 UAC_BarringPerPLMN__plmn_IdentityIndex__helper2.

Opaque UAC_BarringPerPLMN__plmn_IdentityIndex__cond UAC_BarringPerPLMN__plmn_IdentityIndex__Format.

Definition UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Format : T_Format UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Type UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__cond := seq_of_fixed_format UAC_BarringInfoSetIndex__Format maxAccessCat_1.

Opaque UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__cond UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Format.


Definition UAC_BarringPerPLMN__uac_ACBarringListType__Format_Type := Eval cbn in get_formats UAC_BarringPerPLMN__uac_ACBarringListType__list.
Definition UAC_BarringPerPLMN__uac_ACBarringListType__Format_list : UAC_BarringPerPLMN__uac_ACBarringListType__Format_Type :=
  (UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Format, (UAC_BarringPerCatList__Format, unit__Format)).
Definition UAC_BarringPerPLMN__uac_ACBarringListType__list__Format := Eval compute in choice_format UAC_BarringPerPLMN__uac_ACBarringListType__list UAC_BarringPerPLMN__uac_ACBarringListType__len_helper1 UAC_BarringPerPLMN__uac_ACBarringListType__len_helper2  UAC_BarringPerPLMN__uac_ACBarringListType__Format_list.
Definition UAC_BarringPerPLMN__uac_ACBarringListType__F1 (z : UAC_BarringPerPLMN__uac_ACBarringListType__Type) : (choice UAC_BarringPerPLMN__uac_ACBarringListType__list) :=
  match z with
   | UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList t => existT _ 0 t
  | UAC_BarringPerPLMN__uac_ACBarringListType__uac_ExplicitACBarringList t => existT _ 1 t
  end.
Definition UAC_BarringPerPLMN__uac_ACBarringListType__g := (fun n => typ_set (get_nth_typ UAC_BarringPerPLMN__uac_ACBarringListType__list n)).
Definition UAC_BarringPerPLMN__uac_ACBarringListType__F2 (y : choice UAC_BarringPerPLMN__uac_ACBarringListType__list) : UAC_BarringPerPLMN__uac_ACBarringListType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UAC_BarringPerPLMN__uac_ACBarringListType__g n -> UAC_BarringPerPLMN__uac_ACBarringListType__Type) with
    | 0 => fun (t : UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList__Type) => UAC_BarringPerPLMN__uac_ACBarringListType__uac_ImplicitACBarringList t 
    | 1 => fun (t : UAC_BarringPerCatList__Type) => UAC_BarringPerPLMN__uac_ACBarringListType__uac_ExplicitACBarringList t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UAC_BarringPerPLMN__uac_ACBarringListType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UAC_BarringPerPLMN__uac_ACBarringListType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UAC_BarringPerPLMN__uac_ACBarringListType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UAC_BarringPerPLMN__uac_ACBarringListType__Type with end) n0
           end t0).

Lemma UAC_BarringPerPLMN__uac_ACBarringListType__helper2 :  forall (y : UAC_BarringPerPLMN__uac_ACBarringListType__Type), UAC_BarringPerPLMN__uac_ACBarringListType__cond y -> choice_cond UAC_BarringPerPLMN__uac_ACBarringListType__list (UAC_BarringPerPLMN__uac_ACBarringListType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UAC_BarringPerPLMN__uac_ACBarringListType__helper3 :  forall (y : UAC_BarringPerPLMN__uac_ACBarringListType__Type), UAC_BarringPerPLMN__uac_ACBarringListType__F2 (UAC_BarringPerPLMN__uac_ACBarringListType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UAC_BarringPerPLMN__uac_ACBarringListType__helper4 : (forall b : choice UAC_BarringPerPLMN__uac_ACBarringListType__list, choice_cond UAC_BarringPerPLMN__uac_ACBarringListType__list b -> UAC_BarringPerPLMN__uac_ACBarringListType__cond (UAC_BarringPerPLMN__uac_ACBarringListType__F2 b) /\ UAC_BarringPerPLMN__uac_ACBarringListType__F1 (UAC_BarringPerPLMN__uac_ACBarringListType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UAC_BarringPerPLMN__uac_ACBarringListType__F1 UAC_BarringPerPLMN__uac_ACBarringListType__F2.
Definition UAC_BarringPerPLMN__uac_ACBarringListType__Format : T_Format UAC_BarringPerPLMN__uac_ACBarringListType__Type UAC_BarringPerPLMN__uac_ACBarringListType__cond :=
  (* Eval compute in *) proj2_format UAC_BarringPerPLMN__uac_ACBarringListType__cond UAC_BarringPerPLMN__uac_ACBarringListType__list__Format UAC_BarringPerPLMN__uac_ACBarringListType__F1 UAC_BarringPerPLMN__uac_ACBarringListType__F2 UAC_BarringPerPLMN__uac_ACBarringListType__helper2 UAC_BarringPerPLMN__uac_ACBarringListType__helper3 UAC_BarringPerPLMN__uac_ACBarringListType__helper4.
Opaque UAC_BarringPerPLMN__uac_ACBarringListType__cond UAC_BarringPerPLMN__uac_ACBarringListType__Format.


Definition UAC_BarringPerPLMN__Format_Type := Eval cbn in seq_format_prod UAC_BarringPerPLMN__list.
Definition UAC_BarringPerPLMN__Format_list : UAC_BarringPerPLMN__Format_Type :=
  (UAC_BarringPerPLMN__plmn_IdentityIndex__Format, (UAC_BarringPerPLMN__uac_ACBarringListType__Format, unit_format)).
Definition UAC_BarringPerPLMN__list__Format := (*Eval compute in *) seq_format UAC_BarringPerPLMN__list UAC_BarringPerPLMN__Format_list.
Definition UAC_BarringPerPLMN__F1 z :=
  (UAC_BarringPerPLMN__plmn_IdentityIndex z, (UAC_BarringPerPLMN__uac_ACBarringListType z, tt)).
Definition UAC_BarringPerPLMN__F2 (y : seq_type UAC_BarringPerPLMN__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UAC_BarringPerPLMN__Type i0 i1
  end.
Lemma UAC_BarringPerPLMN__F1F2_cond (z : UAC_BarringPerPLMN__Type)
  : UAC_BarringPerPLMN__cond z ->
  (seq_cond UAC_BarringPerPLMN__list (UAC_BarringPerPLMN__F1 z)).
intro H. unfold UAC_BarringPerPLMN__cond in H. simpl. auto. Qed.
Lemma UAC_BarringPerPLMN__F1F2_cond2 (z : UAC_BarringPerPLMN__Type)
 : UAC_BarringPerPLMN__F2 (UAC_BarringPerPLMN__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UAC_BarringPerPLMN__F2F1_cond (y : seq_type UAC_BarringPerPLMN__list)
  : seq_cond UAC_BarringPerPLMN__list y ->
 (UAC_BarringPerPLMN__cond (UAC_BarringPerPLMN__F2 y)) /\  UAC_BarringPerPLMN__F1 (UAC_BarringPerPLMN__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UAC_BarringPerPLMN__cond. simpl in *. auto.
 - simpl. unfold UAC_BarringPerPLMN__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UAC_BarringPerPLMN__Format : T_Format UAC_BarringPerPLMN__Type UAC_BarringPerPLMN__cond :=
        proj2_format  UAC_BarringPerPLMN__cond UAC_BarringPerPLMN__list__Format
    UAC_BarringPerPLMN__F1 UAC_BarringPerPLMN__F2 UAC_BarringPerPLMN__F1F2_cond  UAC_BarringPerPLMN__F1F2_cond2 UAC_BarringPerPLMN__F2F1_cond.
Opaque UAC_BarringPerPLMN__cond UAC_BarringPerPLMN__Format.

