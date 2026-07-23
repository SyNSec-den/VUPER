Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.ShortMAC_I.

Opaque ShortMAC_I__cond ShortMAC_I__Format.

Record ReestabUE_Identity__Type : Set :=
  make__ReestabUE_Identity__Type {
    ReestabUE_Identity__c_RNTI : RNTI_Value__Type ;
    ReestabUE_Identity__physCellId : PhysCellId__Type ;
    ReestabUE_Identity__shortMAC_I : ShortMAC_I__Type ;
}.
Definition ReestabUE_Identity__list := (
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor ShortMAC_I__Type ShortMAC_I__cond ::
 nil).
Definition ReestabUE_Identity__cond z := 
  RNTI_Value__cond (ReestabUE_Identity__c_RNTI z) /\
  PhysCellId__cond (ReestabUE_Identity__physCellId z) /\
  ShortMAC_I__cond (ReestabUE_Identity__shortMAC_I z) /\
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

Definition ReestabUE_Identity__Format_Type := Eval cbn in seq_format_prod ReestabUE_Identity__list.
Definition ReestabUE_Identity__Format_list : ReestabUE_Identity__Format_Type :=
  (RNTI_Value__Format, (PhysCellId__Format, (ShortMAC_I__Format, unit_format))).
Definition ReestabUE_Identity__list__Format := (*Eval compute in *) seq_format ReestabUE_Identity__list ReestabUE_Identity__Format_list.
Definition ReestabUE_Identity__F1 z :=
  (ReestabUE_Identity__c_RNTI z, (ReestabUE_Identity__physCellId z, (ReestabUE_Identity__shortMAC_I z, tt))).
Definition ReestabUE_Identity__F2 (y : seq_type ReestabUE_Identity__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ReestabUE_Identity__Type i0 i1 i2
  end.
Lemma ReestabUE_Identity__F1F2_cond (z : ReestabUE_Identity__Type)
  : ReestabUE_Identity__cond z ->
  (seq_cond ReestabUE_Identity__list (ReestabUE_Identity__F1 z)).
intro H. unfold ReestabUE_Identity__cond in H. simpl. auto. Qed.
Lemma ReestabUE_Identity__F1F2_cond2 (z : ReestabUE_Identity__Type)
 : ReestabUE_Identity__F2 (ReestabUE_Identity__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReestabUE_Identity__F2F1_cond (y : seq_type ReestabUE_Identity__list)
  : seq_cond ReestabUE_Identity__list y ->
 (ReestabUE_Identity__cond (ReestabUE_Identity__F2 y)) /\  ReestabUE_Identity__F1 (ReestabUE_Identity__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReestabUE_Identity__cond. simpl in *. auto.
 - simpl. unfold ReestabUE_Identity__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReestabUE_Identity__Format : T_Format ReestabUE_Identity__Type ReestabUE_Identity__cond :=
        proj2_format  ReestabUE_Identity__cond ReestabUE_Identity__list__Format
    ReestabUE_Identity__F1 ReestabUE_Identity__F2 ReestabUE_Identity__F1F2_cond  ReestabUE_Identity__F1F2_cond2 ReestabUE_Identity__F2F1_cond.
Opaque ReestabUE_Identity__cond ReestabUE_Identity__Format.

