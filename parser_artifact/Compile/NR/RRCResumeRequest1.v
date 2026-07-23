Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRCResumeRequest1_IEs.

Opaque RRCResumeRequest1_IEs__cond RRCResumeRequest1_IEs__Format.

Record RRCResumeRequest1__Type : Set :=
  make__RRCResumeRequest1__Type {
    RRCResumeRequest1__rrcResumeRequest1 : RRCResumeRequest1_IEs__Type ;
}.
Definition RRCResumeRequest1__list := (
 Nor RRCResumeRequest1_IEs__Type RRCResumeRequest1_IEs__cond ::
 nil).
Definition RRCResumeRequest1__cond z := 
  RRCResumeRequest1_IEs__cond (RRCResumeRequest1__rrcResumeRequest1 z) /\
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

Definition RRCResumeRequest1__Format_Type := Eval cbn in seq_format_prod RRCResumeRequest1__list.
Definition RRCResumeRequest1__Format_list : RRCResumeRequest1__Format_Type :=
  (RRCResumeRequest1_IEs__Format, unit_format).
Definition RRCResumeRequest1__list__Format := (*Eval compute in *) seq_format RRCResumeRequest1__list RRCResumeRequest1__Format_list.
Definition RRCResumeRequest1__F1 z :=
  (RRCResumeRequest1__rrcResumeRequest1 z, tt).
Definition RRCResumeRequest1__F2 (y : seq_type RRCResumeRequest1__list) :=
  match y with
  | (i0, _)=>
    make__RRCResumeRequest1__Type i0
  end.
Lemma RRCResumeRequest1__F1F2_cond (z : RRCResumeRequest1__Type)
  : RRCResumeRequest1__cond z ->
  (seq_cond RRCResumeRequest1__list (RRCResumeRequest1__F1 z)).
intro H. unfold RRCResumeRequest1__cond in H. simpl. auto. Qed.
Lemma RRCResumeRequest1__F1F2_cond2 (z : RRCResumeRequest1__Type)
 : RRCResumeRequest1__F2 (RRCResumeRequest1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResumeRequest1__F2F1_cond (y : seq_type RRCResumeRequest1__list)
  : seq_cond RRCResumeRequest1__list y ->
 (RRCResumeRequest1__cond (RRCResumeRequest1__F2 y)) /\  RRCResumeRequest1__F1 (RRCResumeRequest1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResumeRequest1__cond. simpl in *. auto.
 - simpl. unfold RRCResumeRequest1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResumeRequest1__Format : T_Format RRCResumeRequest1__Type RRCResumeRequest1__cond :=
        proj2_format  RRCResumeRequest1__cond RRCResumeRequest1__list__Format
    RRCResumeRequest1__F1 RRCResumeRequest1__F2 RRCResumeRequest1__F1F2_cond  RRCResumeRequest1__F1F2_cond2 RRCResumeRequest1__F2F1_cond.
Opaque RRCResumeRequest1__cond RRCResumeRequest1__Format.

