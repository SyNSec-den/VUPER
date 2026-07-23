Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__Type := Z.
Definition CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersAdditionPerBC_r16__etype2R1_r16__Type := list Z.

Lemma CodebookParametersAdditionPerBC_r16__etype2R1_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R1_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R1_r16__cond (z : CodebookParametersAdditionPerBC_r16__etype2R1_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__cond z) .

Lemma CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__Type := Z.
Definition CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersAdditionPerBC_r16__etype2R2_r16__Type := list Z.

Lemma CodebookParametersAdditionPerBC_r16__etype2R2_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R2_r16__cond (z : CodebookParametersAdditionPerBC_r16__etype2R2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__cond z) .

Lemma CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__Type := Z.
Definition CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Type := list Z.

Lemma CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__cond (z : CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__cond z) .

Lemma CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__Type := Z.
Definition CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Type := list Z.

Lemma CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__cond (z : CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__cond z) .

Record CodebookParametersAdditionPerBC_r16__Type : Set :=
  make__CodebookParametersAdditionPerBC_r16__Type {
    CodebookParametersAdditionPerBC_r16__etype2R1_r16 : option CodebookParametersAdditionPerBC_r16__etype2R1_r16__Type ;
    CodebookParametersAdditionPerBC_r16__etype2R2_r16 : option CodebookParametersAdditionPerBC_r16__etype2R2_r16__Type ;
    CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16 : option CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Type ;
    CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16 : option CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Type ;
}.
Definition CodebookParametersAdditionPerBC_r16__list := (
 Opt CodebookParametersAdditionPerBC_r16__etype2R1_r16__Type CodebookParametersAdditionPerBC_r16__etype2R1_r16__cond ::
 Opt CodebookParametersAdditionPerBC_r16__etype2R2_r16__Type CodebookParametersAdditionPerBC_r16__etype2R2_r16__cond ::
 Opt CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Type CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__cond ::
 Opt CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Type CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__cond ::
 nil).
Definition CodebookParametersAdditionPerBC_r16__cond z := 
  opt_cond CodebookParametersAdditionPerBC_r16__etype2R1_r16__cond (CodebookParametersAdditionPerBC_r16__etype2R1_r16 z) /\
  opt_cond CodebookParametersAdditionPerBC_r16__etype2R2_r16__cond (CodebookParametersAdditionPerBC_r16__etype2R2_r16 z) /\
  opt_cond CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__cond (CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16 z) /\
  opt_cond CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__cond (CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16 z) /\
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
Definition CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__Format : T_Format Z CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__helper1 CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__cond CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R1_r16__Format : T_Format CodebookParametersAdditionPerBC_r16__etype2R1_r16__Type CodebookParametersAdditionPerBC_r16__etype2R1_r16__cond := seq_of_format CodebookParametersAdditionPerBC_r16__etype2R1_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookParametersAdditionPerBC_r16__etype2R1_r16__helper1 CodebookParametersAdditionPerBC_r16__etype2R1_r16__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R1_r16__cond CodebookParametersAdditionPerBC_r16__etype2R1_r16__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__Format : T_Format Z CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__helper1 CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__cond CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R2_r16__Format : T_Format CodebookParametersAdditionPerBC_r16__etype2R2_r16__Type CodebookParametersAdditionPerBC_r16__etype2R2_r16__cond := seq_of_format CodebookParametersAdditionPerBC_r16__etype2R2_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookParametersAdditionPerBC_r16__etype2R2_r16__helper1 CodebookParametersAdditionPerBC_r16__etype2R2_r16__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R2_r16__cond CodebookParametersAdditionPerBC_r16__etype2R2_r16__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__Format : T_Format Z CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__helper1 CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__cond CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Format : T_Format CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Type CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__cond := seq_of_format CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__helper1 CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__cond CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__Format : T_Format Z CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__helper1 CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__cond CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__Format.

Definition CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Format : T_Format CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Type CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__cond := seq_of_format CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__helper1 CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__helper2.

Opaque CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__cond CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Format.


Definition CodebookParametersAdditionPerBC_r16__Format_Type := Eval cbn in seq_format_prod CodebookParametersAdditionPerBC_r16__list.
Definition CodebookParametersAdditionPerBC_r16__Format_list : CodebookParametersAdditionPerBC_r16__Format_Type :=
  (CodebookParametersAdditionPerBC_r16__etype2R1_r16__Format, (CodebookParametersAdditionPerBC_r16__etype2R2_r16__Format, (CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16__Format, (CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16__Format, unit_format)))).
Definition CodebookParametersAdditionPerBC_r16__list__Format := (*Eval compute in *) seq_format CodebookParametersAdditionPerBC_r16__list CodebookParametersAdditionPerBC_r16__Format_list.
Definition CodebookParametersAdditionPerBC_r16__F1 z :=
  (CodebookParametersAdditionPerBC_r16__etype2R1_r16 z, (CodebookParametersAdditionPerBC_r16__etype2R2_r16 z, (CodebookParametersAdditionPerBC_r16__etype2R1_PortSelection_r16 z, (CodebookParametersAdditionPerBC_r16__etype2R2_PortSelection_r16 z, tt)))).
Definition CodebookParametersAdditionPerBC_r16__F2 (y : seq_type CodebookParametersAdditionPerBC_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CodebookParametersAdditionPerBC_r16__Type i0 i1 i2 i3
  end.
Lemma CodebookParametersAdditionPerBC_r16__F1F2_cond (z : CodebookParametersAdditionPerBC_r16__Type)
  : CodebookParametersAdditionPerBC_r16__cond z ->
  (seq_cond CodebookParametersAdditionPerBC_r16__list (CodebookParametersAdditionPerBC_r16__F1 z)).
intro H. unfold CodebookParametersAdditionPerBC_r16__cond in H. simpl. auto. Qed.
Lemma CodebookParametersAdditionPerBC_r16__F1F2_cond2 (z : CodebookParametersAdditionPerBC_r16__Type)
 : CodebookParametersAdditionPerBC_r16__F2 (CodebookParametersAdditionPerBC_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParametersAdditionPerBC_r16__F2F1_cond (y : seq_type CodebookParametersAdditionPerBC_r16__list)
  : seq_cond CodebookParametersAdditionPerBC_r16__list y ->
 (CodebookParametersAdditionPerBC_r16__cond (CodebookParametersAdditionPerBC_r16__F2 y)) /\  CodebookParametersAdditionPerBC_r16__F1 (CodebookParametersAdditionPerBC_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParametersAdditionPerBC_r16__cond. simpl in *. auto.
 - simpl. unfold CodebookParametersAdditionPerBC_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParametersAdditionPerBC_r16__Format : T_Format CodebookParametersAdditionPerBC_r16__Type CodebookParametersAdditionPerBC_r16__cond :=
        proj2_format  CodebookParametersAdditionPerBC_r16__cond CodebookParametersAdditionPerBC_r16__list__Format
    CodebookParametersAdditionPerBC_r16__F1 CodebookParametersAdditionPerBC_r16__F2 CodebookParametersAdditionPerBC_r16__F1F2_cond  CodebookParametersAdditionPerBC_r16__F1F2_cond2 CodebookParametersAdditionPerBC_r16__F2F1_cond.
Opaque CodebookParametersAdditionPerBC_r16__cond CodebookParametersAdditionPerBC_r16__Format.

