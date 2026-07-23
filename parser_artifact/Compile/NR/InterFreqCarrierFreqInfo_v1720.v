Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_MTC4List_r17.

Opaque SSB_MTC4List_r17__cond SSB_MTC4List_r17__Format.

Record InterFreqCarrierFreqInfo_v1720__Type : Set :=
  make__InterFreqCarrierFreqInfo_v1720__Type {
    InterFreqCarrierFreqInfo_v1720__smtc4list_r17 : option SSB_MTC4List_r17__Type ;
}.
Definition InterFreqCarrierFreqInfo_v1720__list := (
 Opt SSB_MTC4List_r17__Type SSB_MTC4List_r17__cond ::
 nil).
Definition InterFreqCarrierFreqInfo_v1720__cond z := 
  opt_cond SSB_MTC4List_r17__cond (InterFreqCarrierFreqInfo_v1720__smtc4list_r17 z) /\
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

Definition InterFreqCarrierFreqInfo_v1720__Format_Type := Eval cbn in seq_format_prod InterFreqCarrierFreqInfo_v1720__list.
Definition InterFreqCarrierFreqInfo_v1720__Format_list : InterFreqCarrierFreqInfo_v1720__Format_Type :=
  (SSB_MTC4List_r17__Format, unit_format).
Definition InterFreqCarrierFreqInfo_v1720__list__Format := (*Eval compute in *) seq_format InterFreqCarrierFreqInfo_v1720__list InterFreqCarrierFreqInfo_v1720__Format_list.
Definition InterFreqCarrierFreqInfo_v1720__F1 z :=
  (InterFreqCarrierFreqInfo_v1720__smtc4list_r17 z, tt).
Definition InterFreqCarrierFreqInfo_v1720__F2 (y : seq_type InterFreqCarrierFreqInfo_v1720__list) :=
  match y with
  | (i0, _)=>
    make__InterFreqCarrierFreqInfo_v1720__Type i0
  end.
Lemma InterFreqCarrierFreqInfo_v1720__F1F2_cond (z : InterFreqCarrierFreqInfo_v1720__Type)
  : InterFreqCarrierFreqInfo_v1720__cond z ->
  (seq_cond InterFreqCarrierFreqInfo_v1720__list (InterFreqCarrierFreqInfo_v1720__F1 z)).
intro H. unfold InterFreqCarrierFreqInfo_v1720__cond in H. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo_v1720__F1F2_cond2 (z : InterFreqCarrierFreqInfo_v1720__Type)
 : InterFreqCarrierFreqInfo_v1720__F2 (InterFreqCarrierFreqInfo_v1720__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo_v1720__F2F1_cond (y : seq_type InterFreqCarrierFreqInfo_v1720__list)
  : seq_cond InterFreqCarrierFreqInfo_v1720__list y ->
 (InterFreqCarrierFreqInfo_v1720__cond (InterFreqCarrierFreqInfo_v1720__F2 y)) /\  InterFreqCarrierFreqInfo_v1720__F1 (InterFreqCarrierFreqInfo_v1720__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold InterFreqCarrierFreqInfo_v1720__cond. simpl in *. auto.
 - simpl. unfold InterFreqCarrierFreqInfo_v1720__F1. simpl. destruct_all_unit. auto.   Qed.
Definition InterFreqCarrierFreqInfo_v1720__Format : T_Format InterFreqCarrierFreqInfo_v1720__Type InterFreqCarrierFreqInfo_v1720__cond :=
        proj2_format  InterFreqCarrierFreqInfo_v1720__cond InterFreqCarrierFreqInfo_v1720__list__Format
    InterFreqCarrierFreqInfo_v1720__F1 InterFreqCarrierFreqInfo_v1720__F2 InterFreqCarrierFreqInfo_v1720__F1F2_cond  InterFreqCarrierFreqInfo_v1720__F1F2_cond2 InterFreqCarrierFreqInfo_v1720__F2F1_cond.
Opaque InterFreqCarrierFreqInfo_v1720__cond InterFreqCarrierFreqInfo_v1720__Format.

