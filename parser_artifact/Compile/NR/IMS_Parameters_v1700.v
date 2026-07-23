Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.IMS_ParametersFR2_2_r17.

Opaque IMS_ParametersFR2_2_r17__cond IMS_ParametersFR2_2_r17__Format.

Record IMS_Parameters_v1700__Type : Set :=
  make__IMS_Parameters_v1700__Type {
    IMS_Parameters_v1700__ims_ParametersFR2_2_r17 : option IMS_ParametersFR2_2_r17__Type ;
}.
Definition IMS_Parameters_v1700__list := (
 Opt IMS_ParametersFR2_2_r17__Type IMS_ParametersFR2_2_r17__cond ::
 nil).
Definition IMS_Parameters_v1700__cond z := 
  opt_cond IMS_ParametersFR2_2_r17__cond (IMS_Parameters_v1700__ims_ParametersFR2_2_r17 z) /\
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

Definition IMS_Parameters_v1700__Format_Type := Eval cbn in seq_format_prod IMS_Parameters_v1700__list.
Definition IMS_Parameters_v1700__Format_list : IMS_Parameters_v1700__Format_Type :=
  (IMS_ParametersFR2_2_r17__Format, unit_format).
Definition IMS_Parameters_v1700__list__Format := (*Eval compute in *) seq_format IMS_Parameters_v1700__list IMS_Parameters_v1700__Format_list.
Definition IMS_Parameters_v1700__F1 z :=
  (IMS_Parameters_v1700__ims_ParametersFR2_2_r17 z, tt).
Definition IMS_Parameters_v1700__F2 (y : seq_type IMS_Parameters_v1700__list) :=
  match y with
  | (i0, _)=>
    make__IMS_Parameters_v1700__Type i0
  end.
Lemma IMS_Parameters_v1700__F1F2_cond (z : IMS_Parameters_v1700__Type)
  : IMS_Parameters_v1700__cond z ->
  (seq_cond IMS_Parameters_v1700__list (IMS_Parameters_v1700__F1 z)).
intro H. unfold IMS_Parameters_v1700__cond in H. simpl. auto. Qed.
Lemma IMS_Parameters_v1700__F1F2_cond2 (z : IMS_Parameters_v1700__Type)
 : IMS_Parameters_v1700__F2 (IMS_Parameters_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IMS_Parameters_v1700__F2F1_cond (y : seq_type IMS_Parameters_v1700__list)
  : seq_cond IMS_Parameters_v1700__list y ->
 (IMS_Parameters_v1700__cond (IMS_Parameters_v1700__F2 y)) /\  IMS_Parameters_v1700__F1 (IMS_Parameters_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IMS_Parameters_v1700__cond. simpl in *. auto.
 - simpl. unfold IMS_Parameters_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IMS_Parameters_v1700__Format : T_Format IMS_Parameters_v1700__Type IMS_Parameters_v1700__cond :=
        proj2_format  IMS_Parameters_v1700__cond IMS_Parameters_v1700__list__Format
    IMS_Parameters_v1700__F1 IMS_Parameters_v1700__F2 IMS_Parameters_v1700__F1F2_cond  IMS_Parameters_v1700__F1F2_cond2 IMS_Parameters_v1700__F2F1_cond.
Opaque IMS_Parameters_v1700__cond IMS_Parameters_v1700__Format.

