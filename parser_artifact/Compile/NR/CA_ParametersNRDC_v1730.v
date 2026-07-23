Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CA_ParametersNR_v1730.

Opaque CA_ParametersNR_v1730__cond CA_ParametersNR_v1730__Format.

Record CA_ParametersNRDC_v1730__Type : Set :=
  make__CA_ParametersNRDC_v1730__Type {
    CA_ParametersNRDC_v1730__ca_ParametersNR_ForDC_v1730 : option CA_ParametersNR_v1730__Type ;
}.
Definition CA_ParametersNRDC_v1730__list := (
 Opt CA_ParametersNR_v1730__Type CA_ParametersNR_v1730__cond ::
 nil).
Definition CA_ParametersNRDC_v1730__cond z := 
  opt_cond CA_ParametersNR_v1730__cond (CA_ParametersNRDC_v1730__ca_ParametersNR_ForDC_v1730 z) /\
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

Definition CA_ParametersNRDC_v1730__Format_Type := Eval cbn in seq_format_prod CA_ParametersNRDC_v1730__list.
Definition CA_ParametersNRDC_v1730__Format_list : CA_ParametersNRDC_v1730__Format_Type :=
  (CA_ParametersNR_v1730__Format, unit_format).
Definition CA_ParametersNRDC_v1730__list__Format := (*Eval compute in *) seq_format CA_ParametersNRDC_v1730__list CA_ParametersNRDC_v1730__Format_list.
Definition CA_ParametersNRDC_v1730__F1 z :=
  (CA_ParametersNRDC_v1730__ca_ParametersNR_ForDC_v1730 z, tt).
Definition CA_ParametersNRDC_v1730__F2 (y : seq_type CA_ParametersNRDC_v1730__list) :=
  match y with
  | (i0, _)=>
    make__CA_ParametersNRDC_v1730__Type i0
  end.
Lemma CA_ParametersNRDC_v1730__F1F2_cond (z : CA_ParametersNRDC_v1730__Type)
  : CA_ParametersNRDC_v1730__cond z ->
  (seq_cond CA_ParametersNRDC_v1730__list (CA_ParametersNRDC_v1730__F1 z)).
intro H. unfold CA_ParametersNRDC_v1730__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNRDC_v1730__F1F2_cond2 (z : CA_ParametersNRDC_v1730__Type)
 : CA_ParametersNRDC_v1730__F2 (CA_ParametersNRDC_v1730__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNRDC_v1730__F2F1_cond (y : seq_type CA_ParametersNRDC_v1730__list)
  : seq_cond CA_ParametersNRDC_v1730__list y ->
 (CA_ParametersNRDC_v1730__cond (CA_ParametersNRDC_v1730__F2 y)) /\  CA_ParametersNRDC_v1730__F1 (CA_ParametersNRDC_v1730__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNRDC_v1730__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNRDC_v1730__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNRDC_v1730__Format : T_Format CA_ParametersNRDC_v1730__Type CA_ParametersNRDC_v1730__cond :=
        proj2_format  CA_ParametersNRDC_v1730__cond CA_ParametersNRDC_v1730__list__Format
    CA_ParametersNRDC_v1730__F1 CA_ParametersNRDC_v1730__F2 CA_ParametersNRDC_v1730__F1F2_cond  CA_ParametersNRDC_v1730__F1F2_cond2 CA_ParametersNRDC_v1730__F2F1_cond.
Opaque CA_ParametersNRDC_v1730__cond CA_ParametersNRDC_v1730__Format.

