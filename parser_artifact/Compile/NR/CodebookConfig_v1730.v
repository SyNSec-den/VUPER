Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CodebookConfig_v1730__codebookType__type1__codebookMode__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma CodebookConfig_v1730__codebookType__type1__codebookMode__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookConfig_v1730__codebookType__type1__codebookMode__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookConfig_v1730__codebookType__type1__codebookMode__Type := Z.
Definition CodebookConfig_v1730__codebookType__type1__codebookMode__cond := (fun z => (1 <= z <= 2)%Z).
Record CodebookConfig_v1730__codebookType__type1__Type : Set :=
  make__CodebookConfig_v1730__codebookType__type1__Type {
    CodebookConfig_v1730__codebookType__type1__codebookMode : option Z ;
}.
Definition CodebookConfig_v1730__codebookType__type1__list := (
 Opt Z CodebookConfig_v1730__codebookType__type1__codebookMode__cond ::
 nil).
Definition CodebookConfig_v1730__codebookType__type1__cond z := 
  opt_cond CodebookConfig_v1730__codebookType__type1__codebookMode__cond (CodebookConfig_v1730__codebookType__type1__codebookMode z) /\
  True.


Inductive CodebookConfig_v1730__codebookType__Type : Set := | CodebookConfig_v1730__codebookType__type1 : CodebookConfig_v1730__codebookType__type1__Type -> CodebookConfig_v1730__codebookType__Type.
Definition CodebookConfig_v1730__codebookType__cond (c : CodebookConfig_v1730__codebookType__Type) := 
  match c with
  | CodebookConfig_v1730__codebookType__type1 t => CodebookConfig_v1730__codebookType__type1__cond t 
  end.

Record CodebookConfig_v1730__Type : Set :=
  make__CodebookConfig_v1730__Type {
    CodebookConfig_v1730__codebookType : CodebookConfig_v1730__codebookType__Type ;
}.
Definition CodebookConfig_v1730__list := (
 Nor CodebookConfig_v1730__codebookType__Type CodebookConfig_v1730__codebookType__cond ::
 nil).
Definition CodebookConfig_v1730__cond z := 
  CodebookConfig_v1730__codebookType__cond (CodebookConfig_v1730__codebookType z) /\
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
Definition CodebookConfig_v1730__codebookType__type1__codebookMode__Format : T_Format Z CodebookConfig_v1730__codebookType__type1__codebookMode__cond :=
 ranged_int_format (1) (2) CodebookConfig_v1730__codebookType__type1__codebookMode__helper1 CodebookConfig_v1730__codebookType__type1__codebookMode__helper2.

Opaque CodebookConfig_v1730__codebookType__type1__codebookMode__cond CodebookConfig_v1730__codebookType__type1__codebookMode__Format.


Definition CodebookConfig_v1730__codebookType__type1__Format_Type := Eval cbn in seq_format_prod CodebookConfig_v1730__codebookType__type1__list.
Definition CodebookConfig_v1730__codebookType__type1__Format_list : CodebookConfig_v1730__codebookType__type1__Format_Type :=
  (CodebookConfig_v1730__codebookType__type1__codebookMode__Format, unit_format).
Definition CodebookConfig_v1730__codebookType__type1__list__Format := (*Eval compute in *) seq_format CodebookConfig_v1730__codebookType__type1__list CodebookConfig_v1730__codebookType__type1__Format_list.
Definition CodebookConfig_v1730__codebookType__type1__F1 z :=
  (CodebookConfig_v1730__codebookType__type1__codebookMode z, tt).
Definition CodebookConfig_v1730__codebookType__type1__F2 (y : seq_type CodebookConfig_v1730__codebookType__type1__list) :=
  match y with
  | (i0, _)=>
    make__CodebookConfig_v1730__codebookType__type1__Type i0
  end.
Lemma CodebookConfig_v1730__codebookType__type1__F1F2_cond (z : CodebookConfig_v1730__codebookType__type1__Type)
  : CodebookConfig_v1730__codebookType__type1__cond z ->
  (seq_cond CodebookConfig_v1730__codebookType__type1__list (CodebookConfig_v1730__codebookType__type1__F1 z)).
intro H. unfold CodebookConfig_v1730__codebookType__type1__cond in H. simpl. auto. Qed.
Lemma CodebookConfig_v1730__codebookType__type1__F1F2_cond2 (z : CodebookConfig_v1730__codebookType__type1__Type)
 : CodebookConfig_v1730__codebookType__type1__F2 (CodebookConfig_v1730__codebookType__type1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookConfig_v1730__codebookType__type1__F2F1_cond (y : seq_type CodebookConfig_v1730__codebookType__type1__list)
  : seq_cond CodebookConfig_v1730__codebookType__type1__list y ->
 (CodebookConfig_v1730__codebookType__type1__cond (CodebookConfig_v1730__codebookType__type1__F2 y)) /\  CodebookConfig_v1730__codebookType__type1__F1 (CodebookConfig_v1730__codebookType__type1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookConfig_v1730__codebookType__type1__cond. simpl in *. auto.
 - simpl. unfold CodebookConfig_v1730__codebookType__type1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookConfig_v1730__codebookType__type1__Format : T_Format CodebookConfig_v1730__codebookType__type1__Type CodebookConfig_v1730__codebookType__type1__cond :=
        proj2_format  CodebookConfig_v1730__codebookType__type1__cond CodebookConfig_v1730__codebookType__type1__list__Format
    CodebookConfig_v1730__codebookType__type1__F1 CodebookConfig_v1730__codebookType__type1__F2 CodebookConfig_v1730__codebookType__type1__F1F2_cond  CodebookConfig_v1730__codebookType__type1__F1F2_cond2 CodebookConfig_v1730__codebookType__type1__F2F1_cond.
Opaque CodebookConfig_v1730__codebookType__type1__cond CodebookConfig_v1730__codebookType__type1__Format.

Definition CodebookConfig_v1730__codebookType__F1 (z : CodebookConfig_v1730__codebookType__Type) : CodebookConfig_v1730__codebookType__type1__Type := 
  match z with
  | CodebookConfig_v1730__codebookType__type1 t => t
  end.
Definition CodebookConfig_v1730__codebookType__F2 (y : CodebookConfig_v1730__codebookType__type1__Type) : CodebookConfig_v1730__codebookType__Type := CodebookConfig_v1730__codebookType__type1 y.

Definition CodebookConfig_v1730__codebookType__helper2 : (forall z : CodebookConfig_v1730__codebookType__Type, CodebookConfig_v1730__codebookType__cond z -> CodebookConfig_v1730__codebookType__type1__cond (CodebookConfig_v1730__codebookType__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition CodebookConfig_v1730__codebookType__helper3 : (forall z : CodebookConfig_v1730__codebookType__Type, CodebookConfig_v1730__codebookType__F2 (CodebookConfig_v1730__codebookType__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition CodebookConfig_v1730__codebookType__helper4 : (forall y : CodebookConfig_v1730__codebookType__type1__Type, CodebookConfig_v1730__codebookType__type1__cond y -> CodebookConfig_v1730__codebookType__cond (CodebookConfig_v1730__codebookType__F2 y) /\  CodebookConfig_v1730__codebookType__F1 (CodebookConfig_v1730__codebookType__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition CodebookConfig_v1730__codebookType__Format : T_Format CodebookConfig_v1730__codebookType__Type CodebookConfig_v1730__codebookType__cond :=
  proj2_format CodebookConfig_v1730__codebookType__cond CodebookConfig_v1730__codebookType__type1__Format CodebookConfig_v1730__codebookType__F1 CodebookConfig_v1730__codebookType__F2 CodebookConfig_v1730__codebookType__helper2 CodebookConfig_v1730__codebookType__helper3 CodebookConfig_v1730__codebookType__helper4.
Opaque CodebookConfig_v1730__codebookType__cond CodebookConfig_v1730__codebookType__Format.


Definition CodebookConfig_v1730__Format_Type := Eval cbn in seq_format_prod CodebookConfig_v1730__list.
Definition CodebookConfig_v1730__Format_list : CodebookConfig_v1730__Format_Type :=
  (CodebookConfig_v1730__codebookType__Format, unit_format).
Definition CodebookConfig_v1730__list__Format := (*Eval compute in *) seq_format CodebookConfig_v1730__list CodebookConfig_v1730__Format_list.
Definition CodebookConfig_v1730__F1 z :=
  (CodebookConfig_v1730__codebookType z, tt).
Definition CodebookConfig_v1730__F2 (y : seq_type CodebookConfig_v1730__list) :=
  match y with
  | (i0, _)=>
    make__CodebookConfig_v1730__Type i0
  end.
Lemma CodebookConfig_v1730__F1F2_cond (z : CodebookConfig_v1730__Type)
  : CodebookConfig_v1730__cond z ->
  (seq_cond CodebookConfig_v1730__list (CodebookConfig_v1730__F1 z)).
intro H. unfold CodebookConfig_v1730__cond in H. simpl. auto. Qed.
Lemma CodebookConfig_v1730__F1F2_cond2 (z : CodebookConfig_v1730__Type)
 : CodebookConfig_v1730__F2 (CodebookConfig_v1730__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookConfig_v1730__F2F1_cond (y : seq_type CodebookConfig_v1730__list)
  : seq_cond CodebookConfig_v1730__list y ->
 (CodebookConfig_v1730__cond (CodebookConfig_v1730__F2 y)) /\  CodebookConfig_v1730__F1 (CodebookConfig_v1730__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookConfig_v1730__cond. simpl in *. auto.
 - simpl. unfold CodebookConfig_v1730__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookConfig_v1730__Format : T_Format CodebookConfig_v1730__Type CodebookConfig_v1730__cond :=
        proj2_format  CodebookConfig_v1730__cond CodebookConfig_v1730__list__Format
    CodebookConfig_v1730__F1 CodebookConfig_v1730__F2 CodebookConfig_v1730__F1F2_cond  CodebookConfig_v1730__F1F2_cond2 CodebookConfig_v1730__F2F1_cond.
Opaque CodebookConfig_v1730__cond CodebookConfig_v1730__Format.

