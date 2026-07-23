Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__Type := Z.
Definition CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Type := list Z.

Lemma CodebookParametersfetype2PerBC_r17__fetype2basic_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookParametersfetype2PerBC_r17__fetype2basic_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersfetype2PerBC_r17__fetype2basic_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersfetype2PerBC_r17__fetype2basic_r17__cond (z : CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__cond z) .

Lemma CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__Type := Z.
Definition CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Type := list Z.

Lemma CodebookParametersfetype2PerBC_r17__fetype2R1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r17)%Z. unfold maxNrofCSI_RS_ResourcesExt_r17.
 lia. Qed.
Lemma CodebookParametersfetype2PerBC_r17__fetype2R1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersfetype2PerBC_r17__fetype2R1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersfetype2PerBC_r17__fetype2R1_r17__cond (z : CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r17)%Z /\ (list_and CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__cond z) .

Lemma CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__Type := Z.
Definition CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Type := list Z.

Lemma CodebookParametersfetype2PerBC_r17__fetype2R2_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r17)%Z. unfold maxNrofCSI_RS_ResourcesExt_r17.
 lia. Qed.
Lemma CodebookParametersfetype2PerBC_r17__fetype2R2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersfetype2PerBC_r17__fetype2R2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersfetype2PerBC_r17__fetype2R2_r17__cond (z : CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r17)%Z /\ (list_and CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__cond z) .

Record CodebookParametersfetype2PerBC_r17__Type : Set :=
  make__CodebookParametersfetype2PerBC_r17__Type {
    CodebookParametersfetype2PerBC_r17__fetype2basic_r17 : CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Type ;
    CodebookParametersfetype2PerBC_r17__fetype2R1_r17 : option CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Type ;
    CodebookParametersfetype2PerBC_r17__fetype2R2_r17 : option CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Type ;
}.
Definition CodebookParametersfetype2PerBC_r17__list := (
 Nor CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Type CodebookParametersfetype2PerBC_r17__fetype2basic_r17__cond ::
 Opt CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Type CodebookParametersfetype2PerBC_r17__fetype2R1_r17__cond ::
 Opt CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Type CodebookParametersfetype2PerBC_r17__fetype2R2_r17__cond ::
 nil).
Definition CodebookParametersfetype2PerBC_r17__cond z := 
  CodebookParametersfetype2PerBC_r17__fetype2basic_r17__cond (CodebookParametersfetype2PerBC_r17__fetype2basic_r17 z) /\
  opt_cond CodebookParametersfetype2PerBC_r17__fetype2R1_r17__cond (CodebookParametersfetype2PerBC_r17__fetype2R1_r17 z) /\
  opt_cond CodebookParametersfetype2PerBC_r17__fetype2R2_r17__cond (CodebookParametersfetype2PerBC_r17__fetype2R2_r17 z) /\
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
Definition CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__Format : T_Format Z CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__helper1 CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__helper2.

Opaque CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__cond CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__Format.

Definition CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Format : T_Format CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Type CodebookParametersfetype2PerBC_r17__fetype2basic_r17__cond := seq_of_format CodebookParametersfetype2PerBC_r17__fetype2basic_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookParametersfetype2PerBC_r17__fetype2basic_r17__helper1 CodebookParametersfetype2PerBC_r17__fetype2basic_r17__helper2.

Opaque CodebookParametersfetype2PerBC_r17__fetype2basic_r17__cond CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Format.

Definition CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__Format : T_Format Z CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__helper1 CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__helper2.

Opaque CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__cond CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__Format.

Definition CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Format : T_Format CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Type CodebookParametersfetype2PerBC_r17__fetype2R1_r17__cond := seq_of_format CodebookParametersfetype2PerBC_r17__fetype2R1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r17 CodebookParametersfetype2PerBC_r17__fetype2R1_r17__helper1 CodebookParametersfetype2PerBC_r17__fetype2R1_r17__helper2.

Opaque CodebookParametersfetype2PerBC_r17__fetype2R1_r17__cond CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Format.

Definition CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__Format : T_Format Z CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__helper1 CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__helper2.

Opaque CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__cond CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__Format.

Definition CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Format : T_Format CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Type CodebookParametersfetype2PerBC_r17__fetype2R2_r17__cond := seq_of_format CodebookParametersfetype2PerBC_r17__fetype2R2_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r17 CodebookParametersfetype2PerBC_r17__fetype2R2_r17__helper1 CodebookParametersfetype2PerBC_r17__fetype2R2_r17__helper2.

Opaque CodebookParametersfetype2PerBC_r17__fetype2R2_r17__cond CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Format.


Definition CodebookParametersfetype2PerBC_r17__Format_Type := Eval cbn in seq_format_prod CodebookParametersfetype2PerBC_r17__list.
Definition CodebookParametersfetype2PerBC_r17__Format_list : CodebookParametersfetype2PerBC_r17__Format_Type :=
  (CodebookParametersfetype2PerBC_r17__fetype2basic_r17__Format, (CodebookParametersfetype2PerBC_r17__fetype2R1_r17__Format, (CodebookParametersfetype2PerBC_r17__fetype2R2_r17__Format, unit_format))).
Definition CodebookParametersfetype2PerBC_r17__list__Format := (*Eval compute in *) seq_format CodebookParametersfetype2PerBC_r17__list CodebookParametersfetype2PerBC_r17__Format_list.
Definition CodebookParametersfetype2PerBC_r17__F1 z :=
  (CodebookParametersfetype2PerBC_r17__fetype2basic_r17 z, (CodebookParametersfetype2PerBC_r17__fetype2R1_r17 z, (CodebookParametersfetype2PerBC_r17__fetype2R2_r17 z, tt))).
Definition CodebookParametersfetype2PerBC_r17__F2 (y : seq_type CodebookParametersfetype2PerBC_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CodebookParametersfetype2PerBC_r17__Type i0 i1 i2
  end.
Lemma CodebookParametersfetype2PerBC_r17__F1F2_cond (z : CodebookParametersfetype2PerBC_r17__Type)
  : CodebookParametersfetype2PerBC_r17__cond z ->
  (seq_cond CodebookParametersfetype2PerBC_r17__list (CodebookParametersfetype2PerBC_r17__F1 z)).
intro H. unfold CodebookParametersfetype2PerBC_r17__cond in H. simpl. auto. Qed.
Lemma CodebookParametersfetype2PerBC_r17__F1F2_cond2 (z : CodebookParametersfetype2PerBC_r17__Type)
 : CodebookParametersfetype2PerBC_r17__F2 (CodebookParametersfetype2PerBC_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParametersfetype2PerBC_r17__F2F1_cond (y : seq_type CodebookParametersfetype2PerBC_r17__list)
  : seq_cond CodebookParametersfetype2PerBC_r17__list y ->
 (CodebookParametersfetype2PerBC_r17__cond (CodebookParametersfetype2PerBC_r17__F2 y)) /\  CodebookParametersfetype2PerBC_r17__F1 (CodebookParametersfetype2PerBC_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParametersfetype2PerBC_r17__cond. simpl in *. auto.
 - simpl. unfold CodebookParametersfetype2PerBC_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParametersfetype2PerBC_r17__Format : T_Format CodebookParametersfetype2PerBC_r17__Type CodebookParametersfetype2PerBC_r17__cond :=
        proj2_format  CodebookParametersfetype2PerBC_r17__cond CodebookParametersfetype2PerBC_r17__list__Format
    CodebookParametersfetype2PerBC_r17__F1 CodebookParametersfetype2PerBC_r17__F2 CodebookParametersfetype2PerBC_r17__F1F2_cond  CodebookParametersfetype2PerBC_r17__F1F2_cond2 CodebookParametersfetype2PerBC_r17__F2F1_cond.
Opaque CodebookParametersfetype2PerBC_r17__cond CodebookParametersfetype2PerBC_r17__Format.

