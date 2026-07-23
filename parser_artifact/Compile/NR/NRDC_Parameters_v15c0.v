Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Type : Set :=
 | NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__supported
.
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__cond := (fun (_ : NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Type) => True).
Lemma NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__nat__helper.

Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1 t :=
  match t with
  | NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__supported => 0
  end.
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F2 n :=
  match n with
  | 0 => NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__supported
  | _ => NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__supported
  end.
Lemma NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1F2 : forall x : NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Type, (NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1 x <= 0) /\ NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F2 (NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1 x) = x. imp_solve. Qed.
Lemma NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F2F1 : forall (y : nat) (H : y <= 0), NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1 (NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F2 y) = y. enum_solve H y. Qed.

Inductive NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Type : Set :=
 | NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__supported
.
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__cond := (fun (_ : NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Type) => True).
Lemma NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__nat__helper.

Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1 t :=
  match t with
  | NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__supported => 0
  end.
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F2 n :=
  match n with
  | 0 => NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__supported
  | _ => NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__supported
  end.
Lemma NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1F2 : forall x : NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Type, (NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1 x <= 0) /\ NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F2 (NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1 x) = x. imp_solve. Qed.
Lemma NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F2F1 : forall (y : nat) (H : y <= 0), NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1 (NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F2 y) = y. enum_solve H y. Qed.

Record NRDC_Parameters_v15c0__Type : Set :=
  make__NRDC_Parameters_v15c0__Type {
    NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB : option NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Type ;
    NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB : option NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Type ;
}.
Definition NRDC_Parameters_v15c0__list := (
 Opt NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Type NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__cond ::
 Opt NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Type NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__cond ::
 nil).
Definition NRDC_Parameters_v15c0__cond z := 
  opt_cond NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__cond (NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB z) /\
  opt_cond NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__cond (NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB z) /\
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
Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Format : T_Format NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__nat__Format NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1 NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F2 NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F1F2 NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__F2F1.

Opaque NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__cond NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Format.

Definition NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Format : T_Format NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__nat__Format NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1 NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F2 NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F1F2 NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__F2F1.

Opaque NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__cond NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Format.


Definition NRDC_Parameters_v15c0__Format_Type := Eval cbn in seq_format_prod NRDC_Parameters_v15c0__list.
Definition NRDC_Parameters_v15c0__Format_list : NRDC_Parameters_v15c0__Format_Type :=
  (NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB__Format, (NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB__Format, unit_format)).
Definition NRDC_Parameters_v15c0__list__Format := (*Eval compute in *) seq_format NRDC_Parameters_v15c0__list NRDC_Parameters_v15c0__Format_list.
Definition NRDC_Parameters_v15c0__F1 z :=
  (NRDC_Parameters_v15c0__pdcp_DuplicationSplitSRB z, (NRDC_Parameters_v15c0__pdcp_DuplicationSplitDRB z, tt)).
Definition NRDC_Parameters_v15c0__F2 (y : seq_type NRDC_Parameters_v15c0__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NRDC_Parameters_v15c0__Type i0 i1
  end.
Lemma NRDC_Parameters_v15c0__F1F2_cond (z : NRDC_Parameters_v15c0__Type)
  : NRDC_Parameters_v15c0__cond z ->
  (seq_cond NRDC_Parameters_v15c0__list (NRDC_Parameters_v15c0__F1 z)).
intro H. unfold NRDC_Parameters_v15c0__cond in H. simpl. auto. Qed.
Lemma NRDC_Parameters_v15c0__F1F2_cond2 (z : NRDC_Parameters_v15c0__Type)
 : NRDC_Parameters_v15c0__F2 (NRDC_Parameters_v15c0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NRDC_Parameters_v15c0__F2F1_cond (y : seq_type NRDC_Parameters_v15c0__list)
  : seq_cond NRDC_Parameters_v15c0__list y ->
 (NRDC_Parameters_v15c0__cond (NRDC_Parameters_v15c0__F2 y)) /\  NRDC_Parameters_v15c0__F1 (NRDC_Parameters_v15c0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NRDC_Parameters_v15c0__cond. simpl in *. auto.
 - simpl. unfold NRDC_Parameters_v15c0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NRDC_Parameters_v15c0__Format : T_Format NRDC_Parameters_v15c0__Type NRDC_Parameters_v15c0__cond :=
        proj2_format  NRDC_Parameters_v15c0__cond NRDC_Parameters_v15c0__list__Format
    NRDC_Parameters_v15c0__F1 NRDC_Parameters_v15c0__F2 NRDC_Parameters_v15c0__F1F2_cond  NRDC_Parameters_v15c0__F1F2_cond2 NRDC_Parameters_v15c0__F2F1_cond.
Opaque NRDC_Parameters_v15c0__cond NRDC_Parameters_v15c0__Format.

