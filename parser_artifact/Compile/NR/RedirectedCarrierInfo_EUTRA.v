Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Inductive RedirectedCarrierInfo_EUTRA__cnType__Type : Set :=
 | RedirectedCarrierInfo_EUTRA__cnType__epc
 | RedirectedCarrierInfo_EUTRA__cnType__fiveGC
.
Definition RedirectedCarrierInfo_EUTRA__cnType__cond := (fun (_ : RedirectedCarrierInfo_EUTRA__cnType__Type) => True).
Lemma RedirectedCarrierInfo_EUTRA__cnType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RedirectedCarrierInfo_EUTRA__cnType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RedirectedCarrierInfo_EUTRA__cnType__nat__helper.

Definition RedirectedCarrierInfo_EUTRA__cnType__F1 t :=
  match t with
  | RedirectedCarrierInfo_EUTRA__cnType__epc => 0
  | RedirectedCarrierInfo_EUTRA__cnType__fiveGC => 1
  end.
Definition RedirectedCarrierInfo_EUTRA__cnType__F2 n :=
  match n with
  | 0 => RedirectedCarrierInfo_EUTRA__cnType__epc
  | 1 => RedirectedCarrierInfo_EUTRA__cnType__fiveGC
  | _ => RedirectedCarrierInfo_EUTRA__cnType__epc
  end.
Lemma RedirectedCarrierInfo_EUTRA__cnType__F1F2 : forall x : RedirectedCarrierInfo_EUTRA__cnType__Type, (RedirectedCarrierInfo_EUTRA__cnType__F1 x <= 1) /\ RedirectedCarrierInfo_EUTRA__cnType__F2 (RedirectedCarrierInfo_EUTRA__cnType__F1 x) = x. imp_solve. Qed.
Lemma RedirectedCarrierInfo_EUTRA__cnType__F2F1 : forall (y : nat) (H : y <= 1), RedirectedCarrierInfo_EUTRA__cnType__F1 (RedirectedCarrierInfo_EUTRA__cnType__F2 y) = y. enum_solve H y. Qed.

Record RedirectedCarrierInfo_EUTRA__Type : Set :=
  make__RedirectedCarrierInfo_EUTRA__Type {
    RedirectedCarrierInfo_EUTRA__eutraFrequency : ARFCN_ValueEUTRA__Type ;
    RedirectedCarrierInfo_EUTRA__cnType : option RedirectedCarrierInfo_EUTRA__cnType__Type ;
}.
Definition RedirectedCarrierInfo_EUTRA__list := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Opt RedirectedCarrierInfo_EUTRA__cnType__Type RedirectedCarrierInfo_EUTRA__cnType__cond ::
 nil).
Definition RedirectedCarrierInfo_EUTRA__cond z := 
  ARFCN_ValueEUTRA__cond (RedirectedCarrierInfo_EUTRA__eutraFrequency z) /\
  opt_cond RedirectedCarrierInfo_EUTRA__cnType__cond (RedirectedCarrierInfo_EUTRA__cnType z) /\
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
Definition RedirectedCarrierInfo_EUTRA__cnType__Format : T_Format RedirectedCarrierInfo_EUTRA__cnType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RedirectedCarrierInfo_EUTRA__cnType__nat__Format RedirectedCarrierInfo_EUTRA__cnType__F1 RedirectedCarrierInfo_EUTRA__cnType__F2 RedirectedCarrierInfo_EUTRA__cnType__F1F2 RedirectedCarrierInfo_EUTRA__cnType__F2F1.

Opaque RedirectedCarrierInfo_EUTRA__cnType__cond RedirectedCarrierInfo_EUTRA__cnType__Format.


Definition RedirectedCarrierInfo_EUTRA__Format_Type := Eval cbn in seq_format_prod RedirectedCarrierInfo_EUTRA__list.
Definition RedirectedCarrierInfo_EUTRA__Format_list : RedirectedCarrierInfo_EUTRA__Format_Type :=
  (ARFCN_ValueEUTRA__Format, (RedirectedCarrierInfo_EUTRA__cnType__Format, unit_format)).
Definition RedirectedCarrierInfo_EUTRA__list__Format := (*Eval compute in *) seq_format RedirectedCarrierInfo_EUTRA__list RedirectedCarrierInfo_EUTRA__Format_list.
Definition RedirectedCarrierInfo_EUTRA__F1 z :=
  (RedirectedCarrierInfo_EUTRA__eutraFrequency z, (RedirectedCarrierInfo_EUTRA__cnType z, tt)).
Definition RedirectedCarrierInfo_EUTRA__F2 (y : seq_type RedirectedCarrierInfo_EUTRA__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RedirectedCarrierInfo_EUTRA__Type i0 i1
  end.
Lemma RedirectedCarrierInfo_EUTRA__F1F2_cond (z : RedirectedCarrierInfo_EUTRA__Type)
  : RedirectedCarrierInfo_EUTRA__cond z ->
  (seq_cond RedirectedCarrierInfo_EUTRA__list (RedirectedCarrierInfo_EUTRA__F1 z)).
intro H. unfold RedirectedCarrierInfo_EUTRA__cond in H. simpl. auto. Qed.
Lemma RedirectedCarrierInfo_EUTRA__F1F2_cond2 (z : RedirectedCarrierInfo_EUTRA__Type)
 : RedirectedCarrierInfo_EUTRA__F2 (RedirectedCarrierInfo_EUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RedirectedCarrierInfo_EUTRA__F2F1_cond (y : seq_type RedirectedCarrierInfo_EUTRA__list)
  : seq_cond RedirectedCarrierInfo_EUTRA__list y ->
 (RedirectedCarrierInfo_EUTRA__cond (RedirectedCarrierInfo_EUTRA__F2 y)) /\  RedirectedCarrierInfo_EUTRA__F1 (RedirectedCarrierInfo_EUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RedirectedCarrierInfo_EUTRA__cond. simpl in *. auto.
 - simpl. unfold RedirectedCarrierInfo_EUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RedirectedCarrierInfo_EUTRA__Format : T_Format RedirectedCarrierInfo_EUTRA__Type RedirectedCarrierInfo_EUTRA__cond :=
        proj2_format  RedirectedCarrierInfo_EUTRA__cond RedirectedCarrierInfo_EUTRA__list__Format
    RedirectedCarrierInfo_EUTRA__F1 RedirectedCarrierInfo_EUTRA__F2 RedirectedCarrierInfo_EUTRA__F1F2_cond  RedirectedCarrierInfo_EUTRA__F1F2_cond2 RedirectedCarrierInfo_EUTRA__F2F1_cond.
Opaque RedirectedCarrierInfo_EUTRA__cond RedirectedCarrierInfo_EUTRA__Format.

