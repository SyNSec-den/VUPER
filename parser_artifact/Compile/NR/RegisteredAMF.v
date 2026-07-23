Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.AMF_Identifier.

Opaque AMF_Identifier__cond AMF_Identifier__Format.

Record RegisteredAMF__Type : Set :=
  make__RegisteredAMF__Type {
    RegisteredAMF__plmn_Identity : option PLMN_Identity__Type ;
    RegisteredAMF__amf_Identifier : AMF_Identifier__Type ;
}.
Definition RegisteredAMF__list := (
 Opt PLMN_Identity__Type PLMN_Identity__cond ::
 Nor AMF_Identifier__Type AMF_Identifier__cond ::
 nil).
Definition RegisteredAMF__cond z := 
  opt_cond PLMN_Identity__cond (RegisteredAMF__plmn_Identity z) /\
  AMF_Identifier__cond (RegisteredAMF__amf_Identifier z) /\
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

Definition RegisteredAMF__Format_Type := Eval cbn in seq_format_prod RegisteredAMF__list.
Definition RegisteredAMF__Format_list : RegisteredAMF__Format_Type :=
  (PLMN_Identity__Format, (AMF_Identifier__Format, unit_format)).
Definition RegisteredAMF__list__Format := (*Eval compute in *) seq_format RegisteredAMF__list RegisteredAMF__Format_list.
Definition RegisteredAMF__F1 z :=
  (RegisteredAMF__plmn_Identity z, (RegisteredAMF__amf_Identifier z, tt)).
Definition RegisteredAMF__F2 (y : seq_type RegisteredAMF__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RegisteredAMF__Type i0 i1
  end.
Lemma RegisteredAMF__F1F2_cond (z : RegisteredAMF__Type)
  : RegisteredAMF__cond z ->
  (seq_cond RegisteredAMF__list (RegisteredAMF__F1 z)).
intro H. unfold RegisteredAMF__cond in H. simpl. auto. Qed.
Lemma RegisteredAMF__F1F2_cond2 (z : RegisteredAMF__Type)
 : RegisteredAMF__F2 (RegisteredAMF__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RegisteredAMF__F2F1_cond (y : seq_type RegisteredAMF__list)
  : seq_cond RegisteredAMF__list y ->
 (RegisteredAMF__cond (RegisteredAMF__F2 y)) /\  RegisteredAMF__F1 (RegisteredAMF__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RegisteredAMF__cond. simpl in *. auto.
 - simpl. unfold RegisteredAMF__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RegisteredAMF__Format : T_Format RegisteredAMF__Type RegisteredAMF__cond :=
        proj2_format  RegisteredAMF__cond RegisteredAMF__list__Format
    RegisteredAMF__F1 RegisteredAMF__F2 RegisteredAMF__F1F2_cond  RegisteredAMF__F1F2_cond2 RegisteredAMF__F2F1_cond.
Opaque RegisteredAMF__cond RegisteredAMF__Format.

