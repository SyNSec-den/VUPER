Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PDCCH_RepetitionParameters_r17__supportedMode_r17__Type : Set :=
 | PDCCH_RepetitionParameters_r17__supportedMode_r17__intra_span
 | PDCCH_RepetitionParameters_r17__supportedMode_r17__inter_span
 | PDCCH_RepetitionParameters_r17__supportedMode_r17__both
.
Definition PDCCH_RepetitionParameters_r17__supportedMode_r17__cond := (fun (_ : PDCCH_RepetitionParameters_r17__supportedMode_r17__Type) => True).
Lemma PDCCH_RepetitionParameters_r17__supportedMode_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCCH_RepetitionParameters_r17__supportedMode_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDCCH_RepetitionParameters_r17__supportedMode_r17__nat__helper.

Definition PDCCH_RepetitionParameters_r17__supportedMode_r17__F1 t :=
  match t with
  | PDCCH_RepetitionParameters_r17__supportedMode_r17__intra_span => 0
  | PDCCH_RepetitionParameters_r17__supportedMode_r17__inter_span => 1
  | PDCCH_RepetitionParameters_r17__supportedMode_r17__both => 2
  end.
Definition PDCCH_RepetitionParameters_r17__supportedMode_r17__F2 n :=
  match n with
  | 0 => PDCCH_RepetitionParameters_r17__supportedMode_r17__intra_span
  | 1 => PDCCH_RepetitionParameters_r17__supportedMode_r17__inter_span
  | 2 => PDCCH_RepetitionParameters_r17__supportedMode_r17__both
  | _ => PDCCH_RepetitionParameters_r17__supportedMode_r17__intra_span
  end.
Lemma PDCCH_RepetitionParameters_r17__supportedMode_r17__F1F2 : forall x : PDCCH_RepetitionParameters_r17__supportedMode_r17__Type, (PDCCH_RepetitionParameters_r17__supportedMode_r17__F1 x <= 2) /\ PDCCH_RepetitionParameters_r17__supportedMode_r17__F2 (PDCCH_RepetitionParameters_r17__supportedMode_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCCH_RepetitionParameters_r17__supportedMode_r17__F2F1 : forall (y : nat) (H : y <= 2), PDCCH_RepetitionParameters_r17__supportedMode_r17__F1 (PDCCH_RepetitionParameters_r17__supportedMode_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Type : Set :=
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n4
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n8
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n16
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n32
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n44
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n64
 | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nolimit
.
Definition PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__cond := (fun (_ : PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Type) => True).
Lemma PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nat__helper.

Definition PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1 t :=
  match t with
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n4 => 0
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n8 => 1
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n16 => 2
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n32 => 3
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n44 => 4
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n64 => 5
  | PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nolimit => 6
  end.
Definition PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F2 n :=
  match n with
  | 0 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n4
  | 1 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n8
  | 2 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n16
  | 3 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n32
  | 4 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n44
  | 5 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n64
  | 6 => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nolimit
  | _ => PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__n4
  end.
Lemma PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1F2 : forall x : PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Type, (PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1 x <= 6) /\ PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F2 (PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F2F1 : forall (y : nat) (H : y <= 6), PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1 (PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Type : Set :=
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n4
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n8
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n16
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n32
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n44
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n64
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n128
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n256
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n512
 | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nolimit
.
Definition PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__cond := (fun (_ : PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Type) => True).
Lemma PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nat__helper.

Definition PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1 t :=
  match t with
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n4 => 0
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n8 => 1
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n16 => 2
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n32 => 3
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n44 => 4
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n64 => 5
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n128 => 6
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n256 => 7
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n512 => 8
  | PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nolimit => 9
  end.
Definition PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F2 n :=
  match n with
  | 0 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n4
  | 1 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n8
  | 2 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n16
  | 3 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n32
  | 4 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n44
  | 5 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n64
  | 6 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n128
  | 7 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n256
  | 8 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n512
  | 9 => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nolimit
  | _ => PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__n4
  end.
Lemma PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1F2 : forall x : PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Type, (PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1 x <= 9) /\ PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F2 (PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 9), PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1 (PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Record PDCCH_RepetitionParameters_r17__Type : Set :=
  make__PDCCH_RepetitionParameters_r17__Type {
    PDCCH_RepetitionParameters_r17__supportedMode_r17 : PDCCH_RepetitionParameters_r17__supportedMode_r17__Type ;
    PDCCH_RepetitionParameters_r17__limitX_PerCC_r17 : option PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Type ;
    PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17 : option PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Type ;
}.
Definition PDCCH_RepetitionParameters_r17__list := (
 Nor PDCCH_RepetitionParameters_r17__supportedMode_r17__Type PDCCH_RepetitionParameters_r17__supportedMode_r17__cond ::
 Opt PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Type PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__cond ::
 Opt PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Type PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__cond ::
 nil).
Definition PDCCH_RepetitionParameters_r17__cond z := 
  PDCCH_RepetitionParameters_r17__supportedMode_r17__cond (PDCCH_RepetitionParameters_r17__supportedMode_r17 z) /\
  opt_cond PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__cond (PDCCH_RepetitionParameters_r17__limitX_PerCC_r17 z) /\
  opt_cond PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__cond (PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17 z) /\
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
Definition PDCCH_RepetitionParameters_r17__supportedMode_r17__Format : T_Format PDCCH_RepetitionParameters_r17__supportedMode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCCH_RepetitionParameters_r17__supportedMode_r17__nat__Format PDCCH_RepetitionParameters_r17__supportedMode_r17__F1 PDCCH_RepetitionParameters_r17__supportedMode_r17__F2 PDCCH_RepetitionParameters_r17__supportedMode_r17__F1F2 PDCCH_RepetitionParameters_r17__supportedMode_r17__F2F1.

Opaque PDCCH_RepetitionParameters_r17__supportedMode_r17__cond PDCCH_RepetitionParameters_r17__supportedMode_r17__Format.

Definition PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Format : T_Format PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__nat__Format PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1 PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F2 PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F1F2 PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__F2F1.

Opaque PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__cond PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Format.

Definition PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Format : T_Format PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__nat__Format PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1 PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F2 PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F1F2 PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__F2F1.

Opaque PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__cond PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Format.


Definition PDCCH_RepetitionParameters_r17__Format_Type := Eval cbn in seq_format_prod PDCCH_RepetitionParameters_r17__list.
Definition PDCCH_RepetitionParameters_r17__Format_list : PDCCH_RepetitionParameters_r17__Format_Type :=
  (PDCCH_RepetitionParameters_r17__supportedMode_r17__Format, (PDCCH_RepetitionParameters_r17__limitX_PerCC_r17__Format, (PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17__Format, unit_format))).
Definition PDCCH_RepetitionParameters_r17__list__Format := (*Eval compute in *) seq_format PDCCH_RepetitionParameters_r17__list PDCCH_RepetitionParameters_r17__Format_list.
Definition PDCCH_RepetitionParameters_r17__F1 z :=
  (PDCCH_RepetitionParameters_r17__supportedMode_r17 z, (PDCCH_RepetitionParameters_r17__limitX_PerCC_r17 z, (PDCCH_RepetitionParameters_r17__limitX_AcrossCC_r17 z, tt))).
Definition PDCCH_RepetitionParameters_r17__F2 (y : seq_type PDCCH_RepetitionParameters_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDCCH_RepetitionParameters_r17__Type i0 i1 i2
  end.
Lemma PDCCH_RepetitionParameters_r17__F1F2_cond (z : PDCCH_RepetitionParameters_r17__Type)
  : PDCCH_RepetitionParameters_r17__cond z ->
  (seq_cond PDCCH_RepetitionParameters_r17__list (PDCCH_RepetitionParameters_r17__F1 z)).
intro H. unfold PDCCH_RepetitionParameters_r17__cond in H. simpl. auto. Qed.
Lemma PDCCH_RepetitionParameters_r17__F1F2_cond2 (z : PDCCH_RepetitionParameters_r17__Type)
 : PDCCH_RepetitionParameters_r17__F2 (PDCCH_RepetitionParameters_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_RepetitionParameters_r17__F2F1_cond (y : seq_type PDCCH_RepetitionParameters_r17__list)
  : seq_cond PDCCH_RepetitionParameters_r17__list y ->
 (PDCCH_RepetitionParameters_r17__cond (PDCCH_RepetitionParameters_r17__F2 y)) /\  PDCCH_RepetitionParameters_r17__F1 (PDCCH_RepetitionParameters_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_RepetitionParameters_r17__cond. simpl in *. auto.
 - simpl. unfold PDCCH_RepetitionParameters_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_RepetitionParameters_r17__Format : T_Format PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond :=
        proj2_format  PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__list__Format
    PDCCH_RepetitionParameters_r17__F1 PDCCH_RepetitionParameters_r17__F2 PDCCH_RepetitionParameters_r17__F1F2_cond  PDCCH_RepetitionParameters_r17__F1F2_cond2 PDCCH_RepetitionParameters_r17__F2F1_cond.
Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

