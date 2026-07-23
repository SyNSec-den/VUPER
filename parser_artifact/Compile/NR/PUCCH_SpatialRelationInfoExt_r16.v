Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_SpatialRelationInfoId_v1610.

Opaque PUCCH_SpatialRelationInfoId_v1610__cond PUCCH_SpatialRelationInfoId_v1610__Format.

Require Import NR.PUCCH_PathlossReferenceRS_Id_v1610.

Opaque PUCCH_PathlossReferenceRS_Id_v1610__cond PUCCH_PathlossReferenceRS_Id_v1610__Format.

Record PUCCH_SpatialRelationInfoExt_r16__Type : Set :=
  make__PUCCH_SpatialRelationInfoExt_r16__Type {
    PUCCH_SpatialRelationInfoExt_r16__pucch_SpatialRelationInfoId_v1610 : option PUCCH_SpatialRelationInfoId_v1610__Type ;
    PUCCH_SpatialRelationInfoExt_r16__pucch_PathlossReferenceRS_Id_v1610 : option PUCCH_PathlossReferenceRS_Id_v1610__Type ;
}.
Definition PUCCH_SpatialRelationInfoExt_r16__root_list : list seq_elem := (
 Opt PUCCH_SpatialRelationInfoId_v1610__Type PUCCH_SpatialRelationInfoId_v1610__cond ::
 Opt PUCCH_PathlossReferenceRS_Id_v1610__Type PUCCH_PathlossReferenceRS_Id_v1610__cond ::
 nil).
Definition PUCCH_SpatialRelationInfoExt_r16__ext_list : list typ := (
  nil).
Definition PUCCH_SpatialRelationInfoExt_r16__cond (z : PUCCH_SpatialRelationInfoExt_r16__Type) := 
(  opt_cond PUCCH_SpatialRelationInfoId_v1610__cond (PUCCH_SpatialRelationInfoExt_r16__pucch_SpatialRelationInfoId_v1610 z) /\
  opt_cond PUCCH_PathlossReferenceRS_Id_v1610__cond (PUCCH_SpatialRelationInfoExt_r16__pucch_PathlossReferenceRS_Id_v1610 z) /\
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

Definition PUCCH_SpatialRelationInfoExt_r16__root_Format_Type := Eval cbn in seq_format_prod PUCCH_SpatialRelationInfoExt_r16__root_list.
Definition PUCCH_SpatialRelationInfoExt_r16__root_Format_list : PUCCH_SpatialRelationInfoExt_r16__root_Format_Type :=
  (PUCCH_SpatialRelationInfoId_v1610__Format, (PUCCH_PathlossReferenceRS_Id_v1610__Format, unit_format)).

Definition PUCCH_SpatialRelationInfoExt_r16__ext_Format_Type := Eval cbn in get_formats PUCCH_SpatialRelationInfoExt_r16__ext_list.
Definition PUCCH_SpatialRelationInfoExt_r16__ext_Format_list : PUCCH_SpatialRelationInfoExt_r16__ext_Format_Type :=
  unit__Format.

Definition PUCCH_SpatialRelationInfoExt_r16__list_type : Set := (seq_type PUCCH_SpatialRelationInfoExt_r16__root_list) * (seq_ext_type PUCCH_SpatialRelationInfoExt_r16__ext_list).
Definition PUCCH_SpatialRelationInfoExt_r16__list_cond (z : PUCCH_SpatialRelationInfoExt_r16__list_type) : Prop :=
        (seq_cond PUCCH_SpatialRelationInfoExt_r16__root_list (fst z)) /\ (seq_ext_cond PUCCH_SpatialRelationInfoExt_r16__ext_list (snd z)).
Definition PUCCH_SpatialRelationInfoExt_r16__list_format : T_Format PUCCH_SpatialRelationInfoExt_r16__list_type PUCCH_SpatialRelationInfoExt_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PUCCH_SpatialRelationInfoExt_r16__root_list PUCCH_SpatialRelationInfoExt_r16__root_Format_list PUCCH_SpatialRelationInfoExt_r16__ext_list PUCCH_SpatialRelationInfoExt_r16__ext_Format_list.

Opaque PUCCH_SpatialRelationInfoExt_r16__list_format.
Definition PUCCH_SpatialRelationInfoExt_r16__F1 (z : PUCCH_SpatialRelationInfoExt_r16__Type) : PUCCH_SpatialRelationInfoExt_r16__list_type :=
  (((PUCCH_SpatialRelationInfoExt_r16__pucch_SpatialRelationInfoId_v1610 z, (PUCCH_SpatialRelationInfoExt_r16__pucch_PathlossReferenceRS_Id_v1610 z, tt))), (
tt)).
Definition PUCCH_SpatialRelationInfoExt_r16__F2 (y : PUCCH_SpatialRelationInfoExt_r16__list_type) : PUCCH_SpatialRelationInfoExt_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__PUCCH_SpatialRelationInfoExt_r16__Type j0 j1
  end.
Definition PUCCH_SpatialRelationInfoExt_r16__helper1 : (forall a : PUCCH_SpatialRelationInfoExt_r16__Type, PUCCH_SpatialRelationInfoExt_r16__cond a -> PUCCH_SpatialRelationInfoExt_r16__list_cond (PUCCH_SpatialRelationInfoExt_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUCCH_SpatialRelationInfoExt_r16__helper2 : (forall a : PUCCH_SpatialRelationInfoExt_r16__Type, PUCCH_SpatialRelationInfoExt_r16__F2 (PUCCH_SpatialRelationInfoExt_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUCCH_SpatialRelationInfoExt_r16__helper3 : (forall b : PUCCH_SpatialRelationInfoExt_r16__list_type, PUCCH_SpatialRelationInfoExt_r16__list_cond b -> PUCCH_SpatialRelationInfoExt_r16__cond (PUCCH_SpatialRelationInfoExt_r16__F2 b) /\ PUCCH_SpatialRelationInfoExt_r16__F1 (PUCCH_SpatialRelationInfoExt_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUCCH_SpatialRelationInfoExt_r16__cond, PUCCH_SpatialRelationInfoExt_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUCCH_SpatialRelationInfoExt_r16__Format : T_Format PUCCH_SpatialRelationInfoExt_r16__Type PUCCH_SpatialRelationInfoExt_r16__cond :=
 proj2_format PUCCH_SpatialRelationInfoExt_r16__cond PUCCH_SpatialRelationInfoExt_r16__list_format  PUCCH_SpatialRelationInfoExt_r16__F1 PUCCH_SpatialRelationInfoExt_r16__F2 PUCCH_SpatialRelationInfoExt_r16__helper1 PUCCH_SpatialRelationInfoExt_r16__helper2 PUCCH_SpatialRelationInfoExt_r16__helper3.

Opaque PUCCH_SpatialRelationInfoExt_r16__cond PUCCH_SpatialRelationInfoExt_r16__Format.

