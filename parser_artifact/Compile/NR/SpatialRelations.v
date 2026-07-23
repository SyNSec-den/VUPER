Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SpatialRelations__maxNumberConfiguredSpatialRelations__Type : Set :=
 | SpatialRelations__maxNumberConfiguredSpatialRelations__n4
 | SpatialRelations__maxNumberConfiguredSpatialRelations__n8
 | SpatialRelations__maxNumberConfiguredSpatialRelations__n16
 | SpatialRelations__maxNumberConfiguredSpatialRelations__n32
 | SpatialRelations__maxNumberConfiguredSpatialRelations__n64
 | SpatialRelations__maxNumberConfiguredSpatialRelations__n96
.
Definition SpatialRelations__maxNumberConfiguredSpatialRelations__cond := (fun (_ : SpatialRelations__maxNumberConfiguredSpatialRelations__Type) => True).
Lemma SpatialRelations__maxNumberConfiguredSpatialRelations__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpatialRelations__maxNumberConfiguredSpatialRelations__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 SpatialRelations__maxNumberConfiguredSpatialRelations__nat__helper.

Definition SpatialRelations__maxNumberConfiguredSpatialRelations__F1 t :=
  match t with
  | SpatialRelations__maxNumberConfiguredSpatialRelations__n4 => 0
  | SpatialRelations__maxNumberConfiguredSpatialRelations__n8 => 1
  | SpatialRelations__maxNumberConfiguredSpatialRelations__n16 => 2
  | SpatialRelations__maxNumberConfiguredSpatialRelations__n32 => 3
  | SpatialRelations__maxNumberConfiguredSpatialRelations__n64 => 4
  | SpatialRelations__maxNumberConfiguredSpatialRelations__n96 => 5
  end.
Definition SpatialRelations__maxNumberConfiguredSpatialRelations__F2 n :=
  match n with
  | 0 => SpatialRelations__maxNumberConfiguredSpatialRelations__n4
  | 1 => SpatialRelations__maxNumberConfiguredSpatialRelations__n8
  | 2 => SpatialRelations__maxNumberConfiguredSpatialRelations__n16
  | 3 => SpatialRelations__maxNumberConfiguredSpatialRelations__n32
  | 4 => SpatialRelations__maxNumberConfiguredSpatialRelations__n64
  | 5 => SpatialRelations__maxNumberConfiguredSpatialRelations__n96
  | _ => SpatialRelations__maxNumberConfiguredSpatialRelations__n4
  end.
Lemma SpatialRelations__maxNumberConfiguredSpatialRelations__F1F2 : forall x : SpatialRelations__maxNumberConfiguredSpatialRelations__Type, (SpatialRelations__maxNumberConfiguredSpatialRelations__F1 x <= 5) /\ SpatialRelations__maxNumberConfiguredSpatialRelations__F2 (SpatialRelations__maxNumberConfiguredSpatialRelations__F1 x) = x. imp_solve. Qed.
Lemma SpatialRelations__maxNumberConfiguredSpatialRelations__F2F1 : forall (y : nat) (H : y <= 5), SpatialRelations__maxNumberConfiguredSpatialRelations__F1 (SpatialRelations__maxNumberConfiguredSpatialRelations__F2 y) = y. enum_solve H y. Qed.

Inductive SpatialRelations__maxNumberActiveSpatialRelations__Type : Set :=
 | SpatialRelations__maxNumberActiveSpatialRelations__n1
 | SpatialRelations__maxNumberActiveSpatialRelations__n2
 | SpatialRelations__maxNumberActiveSpatialRelations__n4
 | SpatialRelations__maxNumberActiveSpatialRelations__n8
 | SpatialRelations__maxNumberActiveSpatialRelations__n14
.
Definition SpatialRelations__maxNumberActiveSpatialRelations__cond := (fun (_ : SpatialRelations__maxNumberActiveSpatialRelations__Type) => True).
Lemma SpatialRelations__maxNumberActiveSpatialRelations__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpatialRelations__maxNumberActiveSpatialRelations__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SpatialRelations__maxNumberActiveSpatialRelations__nat__helper.

Definition SpatialRelations__maxNumberActiveSpatialRelations__F1 t :=
  match t with
  | SpatialRelations__maxNumberActiveSpatialRelations__n1 => 0
  | SpatialRelations__maxNumberActiveSpatialRelations__n2 => 1
  | SpatialRelations__maxNumberActiveSpatialRelations__n4 => 2
  | SpatialRelations__maxNumberActiveSpatialRelations__n8 => 3
  | SpatialRelations__maxNumberActiveSpatialRelations__n14 => 4
  end.
Definition SpatialRelations__maxNumberActiveSpatialRelations__F2 n :=
  match n with
  | 0 => SpatialRelations__maxNumberActiveSpatialRelations__n1
  | 1 => SpatialRelations__maxNumberActiveSpatialRelations__n2
  | 2 => SpatialRelations__maxNumberActiveSpatialRelations__n4
  | 3 => SpatialRelations__maxNumberActiveSpatialRelations__n8
  | 4 => SpatialRelations__maxNumberActiveSpatialRelations__n14
  | _ => SpatialRelations__maxNumberActiveSpatialRelations__n1
  end.
Lemma SpatialRelations__maxNumberActiveSpatialRelations__F1F2 : forall x : SpatialRelations__maxNumberActiveSpatialRelations__Type, (SpatialRelations__maxNumberActiveSpatialRelations__F1 x <= 4) /\ SpatialRelations__maxNumberActiveSpatialRelations__F2 (SpatialRelations__maxNumberActiveSpatialRelations__F1 x) = x. imp_solve. Qed.
Lemma SpatialRelations__maxNumberActiveSpatialRelations__F2F1 : forall (y : nat) (H : y <= 4), SpatialRelations__maxNumberActiveSpatialRelations__F1 (SpatialRelations__maxNumberActiveSpatialRelations__F2 y) = y. enum_solve H y. Qed.

Inductive SpatialRelations__additionalActiveSpatialRelationPUCCH__Type : Set :=
 | SpatialRelations__additionalActiveSpatialRelationPUCCH__supported
.
Definition SpatialRelations__additionalActiveSpatialRelationPUCCH__cond := (fun (_ : SpatialRelations__additionalActiveSpatialRelationPUCCH__Type) => True).
Lemma SpatialRelations__additionalActiveSpatialRelationPUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpatialRelations__additionalActiveSpatialRelationPUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SpatialRelations__additionalActiveSpatialRelationPUCCH__nat__helper.

Definition SpatialRelations__additionalActiveSpatialRelationPUCCH__F1 t :=
  match t with
  | SpatialRelations__additionalActiveSpatialRelationPUCCH__supported => 0
  end.
Definition SpatialRelations__additionalActiveSpatialRelationPUCCH__F2 n :=
  match n with
  | 0 => SpatialRelations__additionalActiveSpatialRelationPUCCH__supported
  | _ => SpatialRelations__additionalActiveSpatialRelationPUCCH__supported
  end.
Lemma SpatialRelations__additionalActiveSpatialRelationPUCCH__F1F2 : forall x : SpatialRelations__additionalActiveSpatialRelationPUCCH__Type, (SpatialRelations__additionalActiveSpatialRelationPUCCH__F1 x <= 0) /\ SpatialRelations__additionalActiveSpatialRelationPUCCH__F2 (SpatialRelations__additionalActiveSpatialRelationPUCCH__F1 x) = x. imp_solve. Qed.
Lemma SpatialRelations__additionalActiveSpatialRelationPUCCH__F2F1 : forall (y : nat) (H : y <= 0), SpatialRelations__additionalActiveSpatialRelationPUCCH__F1 (SpatialRelations__additionalActiveSpatialRelationPUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive SpatialRelations__maxNumberDL_RS_QCL_TypeD__Type : Set :=
 | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n1
 | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n2
 | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n4
 | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n8
 | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n14
.
Definition SpatialRelations__maxNumberDL_RS_QCL_TypeD__cond := (fun (_ : SpatialRelations__maxNumberDL_RS_QCL_TypeD__Type) => True).
Lemma SpatialRelations__maxNumberDL_RS_QCL_TypeD__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpatialRelations__maxNumberDL_RS_QCL_TypeD__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SpatialRelations__maxNumberDL_RS_QCL_TypeD__nat__helper.

Definition SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1 t :=
  match t with
  | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n1 => 0
  | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n2 => 1
  | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n4 => 2
  | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n8 => 3
  | SpatialRelations__maxNumberDL_RS_QCL_TypeD__n14 => 4
  end.
Definition SpatialRelations__maxNumberDL_RS_QCL_TypeD__F2 n :=
  match n with
  | 0 => SpatialRelations__maxNumberDL_RS_QCL_TypeD__n1
  | 1 => SpatialRelations__maxNumberDL_RS_QCL_TypeD__n2
  | 2 => SpatialRelations__maxNumberDL_RS_QCL_TypeD__n4
  | 3 => SpatialRelations__maxNumberDL_RS_QCL_TypeD__n8
  | 4 => SpatialRelations__maxNumberDL_RS_QCL_TypeD__n14
  | _ => SpatialRelations__maxNumberDL_RS_QCL_TypeD__n1
  end.
Lemma SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1F2 : forall x : SpatialRelations__maxNumberDL_RS_QCL_TypeD__Type, (SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1 x <= 4) /\ SpatialRelations__maxNumberDL_RS_QCL_TypeD__F2 (SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1 x) = x. imp_solve. Qed.
Lemma SpatialRelations__maxNumberDL_RS_QCL_TypeD__F2F1 : forall (y : nat) (H : y <= 4), SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1 (SpatialRelations__maxNumberDL_RS_QCL_TypeD__F2 y) = y. enum_solve H y. Qed.

Record SpatialRelations__Type : Set :=
  make__SpatialRelations__Type {
    SpatialRelations__maxNumberConfiguredSpatialRelations : SpatialRelations__maxNumberConfiguredSpatialRelations__Type ;
    SpatialRelations__maxNumberActiveSpatialRelations : SpatialRelations__maxNumberActiveSpatialRelations__Type ;
    SpatialRelations__additionalActiveSpatialRelationPUCCH : option SpatialRelations__additionalActiveSpatialRelationPUCCH__Type ;
    SpatialRelations__maxNumberDL_RS_QCL_TypeD : SpatialRelations__maxNumberDL_RS_QCL_TypeD__Type ;
}.
Definition SpatialRelations__list := (
 Nor SpatialRelations__maxNumberConfiguredSpatialRelations__Type SpatialRelations__maxNumberConfiguredSpatialRelations__cond ::
 Nor SpatialRelations__maxNumberActiveSpatialRelations__Type SpatialRelations__maxNumberActiveSpatialRelations__cond ::
 Opt SpatialRelations__additionalActiveSpatialRelationPUCCH__Type SpatialRelations__additionalActiveSpatialRelationPUCCH__cond ::
 Nor SpatialRelations__maxNumberDL_RS_QCL_TypeD__Type SpatialRelations__maxNumberDL_RS_QCL_TypeD__cond ::
 nil).
Definition SpatialRelations__cond z := 
  SpatialRelations__maxNumberConfiguredSpatialRelations__cond (SpatialRelations__maxNumberConfiguredSpatialRelations z) /\
  SpatialRelations__maxNumberActiveSpatialRelations__cond (SpatialRelations__maxNumberActiveSpatialRelations z) /\
  opt_cond SpatialRelations__additionalActiveSpatialRelationPUCCH__cond (SpatialRelations__additionalActiveSpatialRelationPUCCH z) /\
  SpatialRelations__maxNumberDL_RS_QCL_TypeD__cond (SpatialRelations__maxNumberDL_RS_QCL_TypeD z) /\
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
Definition SpatialRelations__maxNumberConfiguredSpatialRelations__Format : T_Format SpatialRelations__maxNumberConfiguredSpatialRelations__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpatialRelations__maxNumberConfiguredSpatialRelations__nat__Format SpatialRelations__maxNumberConfiguredSpatialRelations__F1 SpatialRelations__maxNumberConfiguredSpatialRelations__F2 SpatialRelations__maxNumberConfiguredSpatialRelations__F1F2 SpatialRelations__maxNumberConfiguredSpatialRelations__F2F1.

Opaque SpatialRelations__maxNumberConfiguredSpatialRelations__cond SpatialRelations__maxNumberConfiguredSpatialRelations__Format.

Definition SpatialRelations__maxNumberActiveSpatialRelations__Format : T_Format SpatialRelations__maxNumberActiveSpatialRelations__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpatialRelations__maxNumberActiveSpatialRelations__nat__Format SpatialRelations__maxNumberActiveSpatialRelations__F1 SpatialRelations__maxNumberActiveSpatialRelations__F2 SpatialRelations__maxNumberActiveSpatialRelations__F1F2 SpatialRelations__maxNumberActiveSpatialRelations__F2F1.

Opaque SpatialRelations__maxNumberActiveSpatialRelations__cond SpatialRelations__maxNumberActiveSpatialRelations__Format.

Definition SpatialRelations__additionalActiveSpatialRelationPUCCH__Format : T_Format SpatialRelations__additionalActiveSpatialRelationPUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpatialRelations__additionalActiveSpatialRelationPUCCH__nat__Format SpatialRelations__additionalActiveSpatialRelationPUCCH__F1 SpatialRelations__additionalActiveSpatialRelationPUCCH__F2 SpatialRelations__additionalActiveSpatialRelationPUCCH__F1F2 SpatialRelations__additionalActiveSpatialRelationPUCCH__F2F1.

Opaque SpatialRelations__additionalActiveSpatialRelationPUCCH__cond SpatialRelations__additionalActiveSpatialRelationPUCCH__Format.

Definition SpatialRelations__maxNumberDL_RS_QCL_TypeD__Format : T_Format SpatialRelations__maxNumberDL_RS_QCL_TypeD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpatialRelations__maxNumberDL_RS_QCL_TypeD__nat__Format SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1 SpatialRelations__maxNumberDL_RS_QCL_TypeD__F2 SpatialRelations__maxNumberDL_RS_QCL_TypeD__F1F2 SpatialRelations__maxNumberDL_RS_QCL_TypeD__F2F1.

Opaque SpatialRelations__maxNumberDL_RS_QCL_TypeD__cond SpatialRelations__maxNumberDL_RS_QCL_TypeD__Format.


Definition SpatialRelations__Format_Type := Eval cbn in seq_format_prod SpatialRelations__list.
Definition SpatialRelations__Format_list : SpatialRelations__Format_Type :=
  (SpatialRelations__maxNumberConfiguredSpatialRelations__Format, (SpatialRelations__maxNumberActiveSpatialRelations__Format, (SpatialRelations__additionalActiveSpatialRelationPUCCH__Format, (SpatialRelations__maxNumberDL_RS_QCL_TypeD__Format, unit_format)))).
Definition SpatialRelations__list__Format := (*Eval compute in *) seq_format SpatialRelations__list SpatialRelations__Format_list.
Definition SpatialRelations__F1 z :=
  (SpatialRelations__maxNumberConfiguredSpatialRelations z, (SpatialRelations__maxNumberActiveSpatialRelations z, (SpatialRelations__additionalActiveSpatialRelationPUCCH z, (SpatialRelations__maxNumberDL_RS_QCL_TypeD z, tt)))).
Definition SpatialRelations__F2 (y : seq_type SpatialRelations__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SpatialRelations__Type i0 i1 i2 i3
  end.
Lemma SpatialRelations__F1F2_cond (z : SpatialRelations__Type)
  : SpatialRelations__cond z ->
  (seq_cond SpatialRelations__list (SpatialRelations__F1 z)).
intro H. unfold SpatialRelations__cond in H. simpl. auto. Qed.
Lemma SpatialRelations__F1F2_cond2 (z : SpatialRelations__Type)
 : SpatialRelations__F2 (SpatialRelations__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SpatialRelations__F2F1_cond (y : seq_type SpatialRelations__list)
  : seq_cond SpatialRelations__list y ->
 (SpatialRelations__cond (SpatialRelations__F2 y)) /\  SpatialRelations__F1 (SpatialRelations__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SpatialRelations__cond. simpl in *. auto.
 - simpl. unfold SpatialRelations__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SpatialRelations__Format : T_Format SpatialRelations__Type SpatialRelations__cond :=
        proj2_format  SpatialRelations__cond SpatialRelations__list__Format
    SpatialRelations__F1 SpatialRelations__F2 SpatialRelations__F1F2_cond  SpatialRelations__F1F2_cond2 SpatialRelations__F2F1_cond.
Opaque SpatialRelations__cond SpatialRelations__Format.

