Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TAG_Id.

Opaque TAG_Id__cond TAG_Id__Format.

Require Import NR.TimeAlignmentTimer.

Opaque TimeAlignmentTimer__cond TimeAlignmentTimer__Format.

Record TAG__Type : Set :=
  make__TAG__Type {
    TAG__tag_Id : TAG_Id__Type ;
    TAG__timeAlignmentTimer : TimeAlignmentTimer__Type ;
}.
Definition TAG__root_list : list seq_elem := (
 Nor TAG_Id__Type TAG_Id__cond ::
 Nor TimeAlignmentTimer__Type TimeAlignmentTimer__cond ::
 nil).
Definition TAG__ext_list : list typ := (
  nil).
Definition TAG__cond (z : TAG__Type) := 
(  TAG_Id__cond (TAG__tag_Id z) /\
  TimeAlignmentTimer__cond (TAG__timeAlignmentTimer z) /\
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

Definition TAG__root_Format_Type := Eval cbn in seq_format_prod TAG__root_list.
Definition TAG__root_Format_list : TAG__root_Format_Type :=
  (TAG_Id__Format, (TimeAlignmentTimer__Format, unit_format)).

Definition TAG__ext_Format_Type := Eval cbn in get_formats TAG__ext_list.
Definition TAG__ext_Format_list : TAG__ext_Format_Type :=
  unit__Format.

Definition TAG__list_type : Set := (seq_type TAG__root_list) * (seq_ext_type TAG__ext_list).
Definition TAG__list_cond (z : TAG__list_type) : Prop :=
        (seq_cond TAG__root_list (fst z)) /\ (seq_ext_cond TAG__ext_list (snd z)).
Definition TAG__list_format : T_Format TAG__list_type TAG__list_cond :=
 (* Eval compute in *) seq_ext_format TAG__root_list TAG__root_Format_list TAG__ext_list TAG__ext_Format_list.

Opaque TAG__list_format.
Definition TAG__F1 (z : TAG__Type) : TAG__list_type :=
  (((TAG__tag_Id z, (TAG__timeAlignmentTimer z, tt))), (
tt)).
Definition TAG__F2 (y : TAG__list_type) : TAG__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__TAG__Type j0 j1
  end.
Definition TAG__helper1 : (forall a : TAG__Type, TAG__cond a -> TAG__list_cond (TAG__F1 a)).
                     intros. destruct a. auto. Qed.
Definition TAG__helper2 : (forall a : TAG__Type, TAG__F2 (TAG__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition TAG__helper3 : (forall b : TAG__list_type, TAG__list_cond b -> TAG__cond (TAG__F2 b) /\ TAG__F1 (TAG__F2 b) = b).
                     intros. destruct b as [y y1]. unfold TAG__cond, TAG__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition TAG__Format : T_Format TAG__Type TAG__cond :=
 proj2_format TAG__cond TAG__list_format  TAG__F1 TAG__F2 TAG__helper1 TAG__helper2 TAG__helper3.

Opaque TAG__cond TAG__Format.

