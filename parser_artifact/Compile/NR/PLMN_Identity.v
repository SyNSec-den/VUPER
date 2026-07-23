Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MCC.

Opaque MCC__cond MCC__Format.

Require Import NR.MNC.

Opaque MNC__cond MNC__Format.

Record PLMN_Identity__Type : Set :=
  make__PLMN_Identity__Type {
    PLMN_Identity__mcc : option MCC__Type ;
    PLMN_Identity__mnc : MNC__Type ;
}.
Definition PLMN_Identity__list := (
 Opt MCC__Type MCC__cond ::
 Nor MNC__Type MNC__cond ::
 nil).
Definition PLMN_Identity__cond z := 
  opt_cond MCC__cond (PLMN_Identity__mcc z) /\
  MNC__cond (PLMN_Identity__mnc z) /\
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

Definition PLMN_Identity__Format_Type := Eval cbn in seq_format_prod PLMN_Identity__list.
Definition PLMN_Identity__Format_list : PLMN_Identity__Format_Type :=
  (MCC__Format, (MNC__Format, unit_format)).
Definition PLMN_Identity__list__Format := (*Eval compute in *) seq_format PLMN_Identity__list PLMN_Identity__Format_list.
Definition PLMN_Identity__F1 z :=
  (PLMN_Identity__mcc z, (PLMN_Identity__mnc z, tt)).
Definition PLMN_Identity__F2 (y : seq_type PLMN_Identity__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PLMN_Identity__Type i0 i1
  end.
Lemma PLMN_Identity__F1F2_cond (z : PLMN_Identity__Type)
  : PLMN_Identity__cond z ->
  (seq_cond PLMN_Identity__list (PLMN_Identity__F1 z)).
intro H. unfold PLMN_Identity__cond in H. simpl. auto. Qed.
Lemma PLMN_Identity__F1F2_cond2 (z : PLMN_Identity__Type)
 : PLMN_Identity__F2 (PLMN_Identity__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PLMN_Identity__F2F1_cond (y : seq_type PLMN_Identity__list)
  : seq_cond PLMN_Identity__list y ->
 (PLMN_Identity__cond (PLMN_Identity__F2 y)) /\  PLMN_Identity__F1 (PLMN_Identity__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PLMN_Identity__cond. simpl in *. auto.
 - simpl. unfold PLMN_Identity__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PLMN_Identity__Format : T_Format PLMN_Identity__Type PLMN_Identity__cond :=
        proj2_format  PLMN_Identity__cond PLMN_Identity__list__Format
    PLMN_Identity__F1 PLMN_Identity__F2 PLMN_Identity__F1F2_cond  PLMN_Identity__F1F2_cond2 PLMN_Identity__F2F1_cond.
Opaque PLMN_Identity__cond PLMN_Identity__Format.

