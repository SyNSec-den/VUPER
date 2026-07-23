Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_PosResources_r16.

Opaque SRS_PosResources_r16__cond SRS_PosResources_r16__Format.

Require Import NR.SRS_PosResourceAP_r16.

Opaque SRS_PosResourceAP_r16__cond SRS_PosResourceAP_r16__Format.

Require Import NR.SRS_PosResourceSP_r16.

Opaque SRS_PosResourceSP_r16__cond SRS_PosResourceSP_r16__Format.

Record SRS_AllPosResources_r16__Type : Set :=
  make__SRS_AllPosResources_r16__Type {
    SRS_AllPosResources_r16__srs_PosResources_r16 : SRS_PosResources_r16__Type ;
    SRS_AllPosResources_r16__srs_PosResourceAP_r16 : option SRS_PosResourceAP_r16__Type ;
    SRS_AllPosResources_r16__srs_PosResourceSP_r16 : option SRS_PosResourceSP_r16__Type ;
}.
Definition SRS_AllPosResources_r16__list := (
 Nor SRS_PosResources_r16__Type SRS_PosResources_r16__cond ::
 Opt SRS_PosResourceAP_r16__Type SRS_PosResourceAP_r16__cond ::
 Opt SRS_PosResourceSP_r16__Type SRS_PosResourceSP_r16__cond ::
 nil).
Definition SRS_AllPosResources_r16__cond z := 
  SRS_PosResources_r16__cond (SRS_AllPosResources_r16__srs_PosResources_r16 z) /\
  opt_cond SRS_PosResourceAP_r16__cond (SRS_AllPosResources_r16__srs_PosResourceAP_r16 z) /\
  opt_cond SRS_PosResourceSP_r16__cond (SRS_AllPosResources_r16__srs_PosResourceSP_r16 z) /\
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

Definition SRS_AllPosResources_r16__Format_Type := Eval cbn in seq_format_prod SRS_AllPosResources_r16__list.
Definition SRS_AllPosResources_r16__Format_list : SRS_AllPosResources_r16__Format_Type :=
  (SRS_PosResources_r16__Format, (SRS_PosResourceAP_r16__Format, (SRS_PosResourceSP_r16__Format, unit_format))).
Definition SRS_AllPosResources_r16__list__Format := (*Eval compute in *) seq_format SRS_AllPosResources_r16__list SRS_AllPosResources_r16__Format_list.
Definition SRS_AllPosResources_r16__F1 z :=
  (SRS_AllPosResources_r16__srs_PosResources_r16 z, (SRS_AllPosResources_r16__srs_PosResourceAP_r16 z, (SRS_AllPosResources_r16__srs_PosResourceSP_r16 z, tt))).
Definition SRS_AllPosResources_r16__F2 (y : seq_type SRS_AllPosResources_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SRS_AllPosResources_r16__Type i0 i1 i2
  end.
Lemma SRS_AllPosResources_r16__F1F2_cond (z : SRS_AllPosResources_r16__Type)
  : SRS_AllPosResources_r16__cond z ->
  (seq_cond SRS_AllPosResources_r16__list (SRS_AllPosResources_r16__F1 z)).
intro H. unfold SRS_AllPosResources_r16__cond in H. simpl. auto. Qed.
Lemma SRS_AllPosResources_r16__F1F2_cond2 (z : SRS_AllPosResources_r16__Type)
 : SRS_AllPosResources_r16__F2 (SRS_AllPosResources_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_AllPosResources_r16__F2F1_cond (y : seq_type SRS_AllPosResources_r16__list)
  : seq_cond SRS_AllPosResources_r16__list y ->
 (SRS_AllPosResources_r16__cond (SRS_AllPosResources_r16__F2 y)) /\  SRS_AllPosResources_r16__F1 (SRS_AllPosResources_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_AllPosResources_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_AllPosResources_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_AllPosResources_r16__Format : T_Format SRS_AllPosResources_r16__Type SRS_AllPosResources_r16__cond :=
        proj2_format  SRS_AllPosResources_r16__cond SRS_AllPosResources_r16__list__Format
    SRS_AllPosResources_r16__F1 SRS_AllPosResources_r16__F2 SRS_AllPosResources_r16__F1F2_cond  SRS_AllPosResources_r16__F1F2_cond2 SRS_AllPosResources_r16__F2F1_cond.
Opaque SRS_AllPosResources_r16__cond SRS_AllPosResources_r16__Format.

