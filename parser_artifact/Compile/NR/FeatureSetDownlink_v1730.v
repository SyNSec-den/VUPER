Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Type : Set :=
 | FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__supported
.
Definition FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__cond := (fun (_ : FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Type) => True).
Lemma FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__nat__helper.

Definition FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__supported
  | _ => FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__supported
  end.
Lemma FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1F2 : forall x : FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Type, (FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1 x <= 0) /\ FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F2 (FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1 (FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetDownlink_v1730__Type : Set :=
  make__FeatureSetDownlink_v1730__Type {
    FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17 : option FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Type ;
}.
Definition FeatureSetDownlink_v1730__list := (
 Opt FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Type FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__cond ::
 nil).
Definition FeatureSetDownlink_v1730__cond z := 
  opt_cond FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__cond (FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17 z) /\
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
Definition FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Format : T_Format FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__nat__Format FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1 FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F2 FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F1F2 FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__F2F1.

Opaque FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__cond FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Format.


Definition FeatureSetDownlink_v1730__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink_v1730__list.
Definition FeatureSetDownlink_v1730__Format_list : FeatureSetDownlink_v1730__Format_Type :=
  (FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17__Format, unit_format).
Definition FeatureSetDownlink_v1730__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink_v1730__list FeatureSetDownlink_v1730__Format_list.
Definition FeatureSetDownlink_v1730__F1 z :=
  (FeatureSetDownlink_v1730__prs_AsSpatialRelationRS_For_SRS_r17 z, tt).
Definition FeatureSetDownlink_v1730__F2 (y : seq_type FeatureSetDownlink_v1730__list) :=
  match y with
  | (i0, _)=>
    make__FeatureSetDownlink_v1730__Type i0
  end.
Lemma FeatureSetDownlink_v1730__F1F2_cond (z : FeatureSetDownlink_v1730__Type)
  : FeatureSetDownlink_v1730__cond z ->
  (seq_cond FeatureSetDownlink_v1730__list (FeatureSetDownlink_v1730__F1 z)).
intro H. unfold FeatureSetDownlink_v1730__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1730__F1F2_cond2 (z : FeatureSetDownlink_v1730__Type)
 : FeatureSetDownlink_v1730__F2 (FeatureSetDownlink_v1730__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1730__F2F1_cond (y : seq_type FeatureSetDownlink_v1730__list)
  : seq_cond FeatureSetDownlink_v1730__list y ->
 (FeatureSetDownlink_v1730__cond (FeatureSetDownlink_v1730__F2 y)) /\  FeatureSetDownlink_v1730__F1 (FeatureSetDownlink_v1730__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink_v1730__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink_v1730__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink_v1730__Format : T_Format FeatureSetDownlink_v1730__Type FeatureSetDownlink_v1730__cond :=
        proj2_format  FeatureSetDownlink_v1730__cond FeatureSetDownlink_v1730__list__Format
    FeatureSetDownlink_v1730__F1 FeatureSetDownlink_v1730__F2 FeatureSetDownlink_v1730__F1F2_cond  FeatureSetDownlink_v1730__F1F2_cond2 FeatureSetDownlink_v1730__F2F1_cond.
Opaque FeatureSetDownlink_v1730__cond FeatureSetDownlink_v1730__Format.

