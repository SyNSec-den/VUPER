Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Type : Set :=
 | PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__supported
.
Definition PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__cond := (fun (_ : PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Type) => True).
Lemma PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__nat__helper.

Definition PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1 t :=
  match t with
  | PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__supported => 0
  end.
Definition PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F2 n :=
  match n with
  | 0 => PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__supported
  | _ => PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__supported
  end.
Lemma PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1F2 : forall x : PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Type, (PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1 x <= 0) /\ PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F2 (PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1 (PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Record PDCP_ParametersMRDC_v1610__Type : Set :=
  make__PDCP_ParametersMRDC_v1610__Type {
    PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16 : option PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Type ;
}.
Definition PDCP_ParametersMRDC_v1610__list := (
 Opt PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Type PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__cond ::
 nil).
Definition PDCP_ParametersMRDC_v1610__cond z := 
  opt_cond PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__cond (PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16 z) /\
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
Definition PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Format : T_Format PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__nat__Format PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1 PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F2 PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F1F2 PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__F2F1.

Opaque PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__cond PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Format.


Definition PDCP_ParametersMRDC_v1610__Format_Type := Eval cbn in seq_format_prod PDCP_ParametersMRDC_v1610__list.
Definition PDCP_ParametersMRDC_v1610__Format_list : PDCP_ParametersMRDC_v1610__Format_Type :=
  (PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16__Format, unit_format).
Definition PDCP_ParametersMRDC_v1610__list__Format := (*Eval compute in *) seq_format PDCP_ParametersMRDC_v1610__list PDCP_ParametersMRDC_v1610__Format_list.
Definition PDCP_ParametersMRDC_v1610__F1 z :=
  (PDCP_ParametersMRDC_v1610__scg_DRB_NR_IAB_r16 z, tt).
Definition PDCP_ParametersMRDC_v1610__F2 (y : seq_type PDCP_ParametersMRDC_v1610__list) :=
  match y with
  | (i0, _)=>
    make__PDCP_ParametersMRDC_v1610__Type i0
  end.
Lemma PDCP_ParametersMRDC_v1610__F1F2_cond (z : PDCP_ParametersMRDC_v1610__Type)
  : PDCP_ParametersMRDC_v1610__cond z ->
  (seq_cond PDCP_ParametersMRDC_v1610__list (PDCP_ParametersMRDC_v1610__F1 z)).
intro H. unfold PDCP_ParametersMRDC_v1610__cond in H. simpl. auto. Qed.
Lemma PDCP_ParametersMRDC_v1610__F1F2_cond2 (z : PDCP_ParametersMRDC_v1610__Type)
 : PDCP_ParametersMRDC_v1610__F2 (PDCP_ParametersMRDC_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_ParametersMRDC_v1610__F2F1_cond (y : seq_type PDCP_ParametersMRDC_v1610__list)
  : seq_cond PDCP_ParametersMRDC_v1610__list y ->
 (PDCP_ParametersMRDC_v1610__cond (PDCP_ParametersMRDC_v1610__F2 y)) /\  PDCP_ParametersMRDC_v1610__F1 (PDCP_ParametersMRDC_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_ParametersMRDC_v1610__cond. simpl in *. auto.
 - simpl. unfold PDCP_ParametersMRDC_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_ParametersMRDC_v1610__Format : T_Format PDCP_ParametersMRDC_v1610__Type PDCP_ParametersMRDC_v1610__cond :=
        proj2_format  PDCP_ParametersMRDC_v1610__cond PDCP_ParametersMRDC_v1610__list__Format
    PDCP_ParametersMRDC_v1610__F1 PDCP_ParametersMRDC_v1610__F2 PDCP_ParametersMRDC_v1610__F1F2_cond  PDCP_ParametersMRDC_v1610__F1F2_cond2 PDCP_ParametersMRDC_v1610__F2F1_cond.
Opaque PDCP_ParametersMRDC_v1610__cond PDCP_ParametersMRDC_v1610__Format.

