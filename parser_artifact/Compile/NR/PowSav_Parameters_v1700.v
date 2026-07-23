Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PowSav_ParametersFR2_2_r17.

Opaque PowSav_ParametersFR2_2_r17__cond PowSav_ParametersFR2_2_r17__Format.

Record PowSav_Parameters_v1700__Type : Set :=
  make__PowSav_Parameters_v1700__Type {
    PowSav_Parameters_v1700__powSav_ParametersFR2_2_r17 : option PowSav_ParametersFR2_2_r17__Type ;
}.
Definition PowSav_Parameters_v1700__root_list : list seq_elem := (
 Opt PowSav_ParametersFR2_2_r17__Type PowSav_ParametersFR2_2_r17__cond ::
 nil).
Definition PowSav_Parameters_v1700__ext_list : list typ := (
  nil).
Definition PowSav_Parameters_v1700__cond (z : PowSav_Parameters_v1700__Type) := 
(  opt_cond PowSav_ParametersFR2_2_r17__cond (PowSav_Parameters_v1700__powSav_ParametersFR2_2_r17 z) /\
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

Definition PowSav_Parameters_v1700__root_Format_Type := Eval cbn in seq_format_prod PowSav_Parameters_v1700__root_list.
Definition PowSav_Parameters_v1700__root_Format_list : PowSav_Parameters_v1700__root_Format_Type :=
  (PowSav_ParametersFR2_2_r17__Format, unit_format).

Definition PowSav_Parameters_v1700__ext_Format_Type := Eval cbn in get_formats PowSav_Parameters_v1700__ext_list.
Definition PowSav_Parameters_v1700__ext_Format_list : PowSav_Parameters_v1700__ext_Format_Type :=
  unit__Format.

Definition PowSav_Parameters_v1700__list_type : Set := (seq_type PowSav_Parameters_v1700__root_list) * (seq_ext_type PowSav_Parameters_v1700__ext_list).
Definition PowSav_Parameters_v1700__list_cond (z : PowSav_Parameters_v1700__list_type) : Prop :=
        (seq_cond PowSav_Parameters_v1700__root_list (fst z)) /\ (seq_ext_cond PowSav_Parameters_v1700__ext_list (snd z)).
Definition PowSav_Parameters_v1700__list_format : T_Format PowSav_Parameters_v1700__list_type PowSav_Parameters_v1700__list_cond :=
 (* Eval compute in *) seq_ext_format PowSav_Parameters_v1700__root_list PowSav_Parameters_v1700__root_Format_list PowSav_Parameters_v1700__ext_list PowSav_Parameters_v1700__ext_Format_list.

Opaque PowSav_Parameters_v1700__list_format.
Definition PowSav_Parameters_v1700__F1 (z : PowSav_Parameters_v1700__Type) : PowSav_Parameters_v1700__list_type :=
  (((PowSav_Parameters_v1700__powSav_ParametersFR2_2_r17 z, tt)), (
tt)).
Definition PowSav_Parameters_v1700__F2 (y : PowSav_Parameters_v1700__list_type) : PowSav_Parameters_v1700__Type :=
  match y with
  | ((j0, _), _)=>
    make__PowSav_Parameters_v1700__Type j0
  end.
Definition PowSav_Parameters_v1700__helper1 : (forall a : PowSav_Parameters_v1700__Type, PowSav_Parameters_v1700__cond a -> PowSav_Parameters_v1700__list_cond (PowSav_Parameters_v1700__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PowSav_Parameters_v1700__helper2 : (forall a : PowSav_Parameters_v1700__Type, PowSav_Parameters_v1700__F2 (PowSav_Parameters_v1700__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PowSav_Parameters_v1700__helper3 : (forall b : PowSav_Parameters_v1700__list_type, PowSav_Parameters_v1700__list_cond b -> PowSav_Parameters_v1700__cond (PowSav_Parameters_v1700__F2 b) /\ PowSav_Parameters_v1700__F1 (PowSav_Parameters_v1700__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PowSav_Parameters_v1700__cond, PowSav_Parameters_v1700__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PowSav_Parameters_v1700__Format : T_Format PowSav_Parameters_v1700__Type PowSav_Parameters_v1700__cond :=
 proj2_format PowSav_Parameters_v1700__cond PowSav_Parameters_v1700__list_format  PowSav_Parameters_v1700__F1 PowSav_Parameters_v1700__F2 PowSav_Parameters_v1700__helper1 PowSav_Parameters_v1700__helper2 PowSav_Parameters_v1700__helper3.

Opaque PowSav_Parameters_v1700__cond PowSav_Parameters_v1700__Format.

