Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Type : Set :=
 | MRDC_Parameters_v1580__dynamicPowerSharingNEDC__supported
.
Definition MRDC_Parameters_v1580__dynamicPowerSharingNEDC__cond := (fun (_ : MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Type) => True).
Lemma MRDC_Parameters_v1580__dynamicPowerSharingNEDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters_v1580__dynamicPowerSharingNEDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters_v1580__dynamicPowerSharingNEDC__nat__helper.

Definition MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1 t :=
  match t with
  | MRDC_Parameters_v1580__dynamicPowerSharingNEDC__supported => 0
  end.
Definition MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F2 n :=
  match n with
  | 0 => MRDC_Parameters_v1580__dynamicPowerSharingNEDC__supported
  | _ => MRDC_Parameters_v1580__dynamicPowerSharingNEDC__supported
  end.
Lemma MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1F2 : forall x : MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Type, (MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1 x <= 0) /\ MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F2 (MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1 (MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F2 y) = y. enum_solve H y. Qed.

Record MRDC_Parameters_v1580__Type : Set :=
  make__MRDC_Parameters_v1580__Type {
    MRDC_Parameters_v1580__dynamicPowerSharingNEDC : option MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Type ;
}.
Definition MRDC_Parameters_v1580__list := (
 Opt MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Type MRDC_Parameters_v1580__dynamicPowerSharingNEDC__cond ::
 nil).
Definition MRDC_Parameters_v1580__cond z := 
  opt_cond MRDC_Parameters_v1580__dynamicPowerSharingNEDC__cond (MRDC_Parameters_v1580__dynamicPowerSharingNEDC z) /\
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
Definition MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Format : T_Format MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters_v1580__dynamicPowerSharingNEDC__nat__Format MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1 MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F2 MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F1F2 MRDC_Parameters_v1580__dynamicPowerSharingNEDC__F2F1.

Opaque MRDC_Parameters_v1580__dynamicPowerSharingNEDC__cond MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Format.


Definition MRDC_Parameters_v1580__Format_Type := Eval cbn in seq_format_prod MRDC_Parameters_v1580__list.
Definition MRDC_Parameters_v1580__Format_list : MRDC_Parameters_v1580__Format_Type :=
  (MRDC_Parameters_v1580__dynamicPowerSharingNEDC__Format, unit_format).
Definition MRDC_Parameters_v1580__list__Format := (*Eval compute in *) seq_format MRDC_Parameters_v1580__list MRDC_Parameters_v1580__Format_list.
Definition MRDC_Parameters_v1580__F1 z :=
  (MRDC_Parameters_v1580__dynamicPowerSharingNEDC z, tt).
Definition MRDC_Parameters_v1580__F2 (y : seq_type MRDC_Parameters_v1580__list) :=
  match y with
  | (i0, _)=>
    make__MRDC_Parameters_v1580__Type i0
  end.
Lemma MRDC_Parameters_v1580__F1F2_cond (z : MRDC_Parameters_v1580__Type)
  : MRDC_Parameters_v1580__cond z ->
  (seq_cond MRDC_Parameters_v1580__list (MRDC_Parameters_v1580__F1 z)).
intro H. unfold MRDC_Parameters_v1580__cond in H. simpl. auto. Qed.
Lemma MRDC_Parameters_v1580__F1F2_cond2 (z : MRDC_Parameters_v1580__Type)
 : MRDC_Parameters_v1580__F2 (MRDC_Parameters_v1580__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRDC_Parameters_v1580__F2F1_cond (y : seq_type MRDC_Parameters_v1580__list)
  : seq_cond MRDC_Parameters_v1580__list y ->
 (MRDC_Parameters_v1580__cond (MRDC_Parameters_v1580__F2 y)) /\  MRDC_Parameters_v1580__F1 (MRDC_Parameters_v1580__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRDC_Parameters_v1580__cond. simpl in *. auto.
 - simpl. unfold MRDC_Parameters_v1580__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRDC_Parameters_v1580__Format : T_Format MRDC_Parameters_v1580__Type MRDC_Parameters_v1580__cond :=
        proj2_format  MRDC_Parameters_v1580__cond MRDC_Parameters_v1580__list__Format
    MRDC_Parameters_v1580__F1 MRDC_Parameters_v1580__F2 MRDC_Parameters_v1580__F1F2_cond  MRDC_Parameters_v1580__F1F2_cond2 MRDC_Parameters_v1580__F2F1_cond.
Opaque MRDC_Parameters_v1580__cond MRDC_Parameters_v1580__Format.

