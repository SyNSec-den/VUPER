Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RA_PrioritizationSliceInfoList_r17.

Opaque RA_PrioritizationSliceInfoList_r17__cond RA_PrioritizationSliceInfoList_r17__Format.

Record RA_PrioritizationForSlicing_r17__Type : Set :=
  make__RA_PrioritizationForSlicing_r17__Type {
    RA_PrioritizationForSlicing_r17__ra_PrioritizationSliceInfoList_r17 : RA_PrioritizationSliceInfoList_r17__Type ;
}.
Definition RA_PrioritizationForSlicing_r17__root_list : list seq_elem := (
 Nor RA_PrioritizationSliceInfoList_r17__Type RA_PrioritizationSliceInfoList_r17__cond ::
 nil).
Definition RA_PrioritizationForSlicing_r17__ext_list : list typ := (
  nil).
Definition RA_PrioritizationForSlicing_r17__cond (z : RA_PrioritizationForSlicing_r17__Type) := 
(  RA_PrioritizationSliceInfoList_r17__cond (RA_PrioritizationForSlicing_r17__ra_PrioritizationSliceInfoList_r17 z) /\
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

Definition RA_PrioritizationForSlicing_r17__root_Format_Type := Eval cbn in seq_format_prod RA_PrioritizationForSlicing_r17__root_list.
Definition RA_PrioritizationForSlicing_r17__root_Format_list : RA_PrioritizationForSlicing_r17__root_Format_Type :=
  (RA_PrioritizationSliceInfoList_r17__Format, unit_format).

Definition RA_PrioritizationForSlicing_r17__ext_Format_Type := Eval cbn in get_formats RA_PrioritizationForSlicing_r17__ext_list.
Definition RA_PrioritizationForSlicing_r17__ext_Format_list : RA_PrioritizationForSlicing_r17__ext_Format_Type :=
  unit__Format.

Definition RA_PrioritizationForSlicing_r17__list_type : Set := (seq_type RA_PrioritizationForSlicing_r17__root_list) * (seq_ext_type RA_PrioritizationForSlicing_r17__ext_list).
Definition RA_PrioritizationForSlicing_r17__list_cond (z : RA_PrioritizationForSlicing_r17__list_type) : Prop :=
        (seq_cond RA_PrioritizationForSlicing_r17__root_list (fst z)) /\ (seq_ext_cond RA_PrioritizationForSlicing_r17__ext_list (snd z)).
Definition RA_PrioritizationForSlicing_r17__list_format : T_Format RA_PrioritizationForSlicing_r17__list_type RA_PrioritizationForSlicing_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RA_PrioritizationForSlicing_r17__root_list RA_PrioritizationForSlicing_r17__root_Format_list RA_PrioritizationForSlicing_r17__ext_list RA_PrioritizationForSlicing_r17__ext_Format_list.

Opaque RA_PrioritizationForSlicing_r17__list_format.
Definition RA_PrioritizationForSlicing_r17__F1 (z : RA_PrioritizationForSlicing_r17__Type) : RA_PrioritizationForSlicing_r17__list_type :=
  (((RA_PrioritizationForSlicing_r17__ra_PrioritizationSliceInfoList_r17 z, tt)), (
tt)).
Definition RA_PrioritizationForSlicing_r17__F2 (y : RA_PrioritizationForSlicing_r17__list_type) : RA_PrioritizationForSlicing_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__RA_PrioritizationForSlicing_r17__Type j0
  end.
Definition RA_PrioritizationForSlicing_r17__helper1 : (forall a : RA_PrioritizationForSlicing_r17__Type, RA_PrioritizationForSlicing_r17__cond a -> RA_PrioritizationForSlicing_r17__list_cond (RA_PrioritizationForSlicing_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RA_PrioritizationForSlicing_r17__helper2 : (forall a : RA_PrioritizationForSlicing_r17__Type, RA_PrioritizationForSlicing_r17__F2 (RA_PrioritizationForSlicing_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RA_PrioritizationForSlicing_r17__helper3 : (forall b : RA_PrioritizationForSlicing_r17__list_type, RA_PrioritizationForSlicing_r17__list_cond b -> RA_PrioritizationForSlicing_r17__cond (RA_PrioritizationForSlicing_r17__F2 b) /\ RA_PrioritizationForSlicing_r17__F1 (RA_PrioritizationForSlicing_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RA_PrioritizationForSlicing_r17__cond, RA_PrioritizationForSlicing_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RA_PrioritizationForSlicing_r17__Format : T_Format RA_PrioritizationForSlicing_r17__Type RA_PrioritizationForSlicing_r17__cond :=
 proj2_format RA_PrioritizationForSlicing_r17__cond RA_PrioritizationForSlicing_r17__list_format  RA_PrioritizationForSlicing_r17__F1 RA_PrioritizationForSlicing_r17__F2 RA_PrioritizationForSlicing_r17__helper1 RA_PrioritizationForSlicing_r17__helper2 RA_PrioritizationForSlicing_r17__helper3.

Opaque RA_PrioritizationForSlicing_r17__cond RA_PrioritizationForSlicing_r17__Format.

