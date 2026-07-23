Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PUCCH_FormatConfig__interslotFrequencyHopping__Type : Set :=
 | PUCCH_FormatConfig__interslotFrequencyHopping__enabled
.
Definition PUCCH_FormatConfig__interslotFrequencyHopping__cond := (fun (_ : PUCCH_FormatConfig__interslotFrequencyHopping__Type) => True).
Lemma PUCCH_FormatConfig__interslotFrequencyHopping__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_FormatConfig__interslotFrequencyHopping__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_FormatConfig__interslotFrequencyHopping__nat__helper.

Definition PUCCH_FormatConfig__interslotFrequencyHopping__F1 t :=
  match t with
  | PUCCH_FormatConfig__interslotFrequencyHopping__enabled => 0
  end.
Definition PUCCH_FormatConfig__interslotFrequencyHopping__F2 n :=
  match n with
  | 0 => PUCCH_FormatConfig__interslotFrequencyHopping__enabled
  | _ => PUCCH_FormatConfig__interslotFrequencyHopping__enabled
  end.
Lemma PUCCH_FormatConfig__interslotFrequencyHopping__F1F2 : forall x : PUCCH_FormatConfig__interslotFrequencyHopping__Type, (PUCCH_FormatConfig__interslotFrequencyHopping__F1 x <= 0) /\ PUCCH_FormatConfig__interslotFrequencyHopping__F2 (PUCCH_FormatConfig__interslotFrequencyHopping__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_FormatConfig__interslotFrequencyHopping__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_FormatConfig__interslotFrequencyHopping__F1 (PUCCH_FormatConfig__interslotFrequencyHopping__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_FormatConfig__additionalDMRS__Type : Set :=
 | PUCCH_FormatConfig__additionalDMRS__true
.
Definition PUCCH_FormatConfig__additionalDMRS__cond := (fun (_ : PUCCH_FormatConfig__additionalDMRS__Type) => True).
Lemma PUCCH_FormatConfig__additionalDMRS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_FormatConfig__additionalDMRS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_FormatConfig__additionalDMRS__nat__helper.

Definition PUCCH_FormatConfig__additionalDMRS__F1 t :=
  match t with
  | PUCCH_FormatConfig__additionalDMRS__true => 0
  end.
Definition PUCCH_FormatConfig__additionalDMRS__F2 n :=
  match n with
  | 0 => PUCCH_FormatConfig__additionalDMRS__true
  | _ => PUCCH_FormatConfig__additionalDMRS__true
  end.
Lemma PUCCH_FormatConfig__additionalDMRS__F1F2 : forall x : PUCCH_FormatConfig__additionalDMRS__Type, (PUCCH_FormatConfig__additionalDMRS__F1 x <= 0) /\ PUCCH_FormatConfig__additionalDMRS__F2 (PUCCH_FormatConfig__additionalDMRS__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_FormatConfig__additionalDMRS__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_FormatConfig__additionalDMRS__F1 (PUCCH_FormatConfig__additionalDMRS__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_MaxCodeRate.

Opaque PUCCH_MaxCodeRate__cond PUCCH_MaxCodeRate__Format.

Inductive PUCCH_FormatConfig__nrofSlots__Type : Set :=
 | PUCCH_FormatConfig__nrofSlots__n2
 | PUCCH_FormatConfig__nrofSlots__n4
 | PUCCH_FormatConfig__nrofSlots__n8
.
Definition PUCCH_FormatConfig__nrofSlots__cond := (fun (_ : PUCCH_FormatConfig__nrofSlots__Type) => True).
Lemma PUCCH_FormatConfig__nrofSlots__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_FormatConfig__nrofSlots__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUCCH_FormatConfig__nrofSlots__nat__helper.

Definition PUCCH_FormatConfig__nrofSlots__F1 t :=
  match t with
  | PUCCH_FormatConfig__nrofSlots__n2 => 0
  | PUCCH_FormatConfig__nrofSlots__n4 => 1
  | PUCCH_FormatConfig__nrofSlots__n8 => 2
  end.
Definition PUCCH_FormatConfig__nrofSlots__F2 n :=
  match n with
  | 0 => PUCCH_FormatConfig__nrofSlots__n2
  | 1 => PUCCH_FormatConfig__nrofSlots__n4
  | 2 => PUCCH_FormatConfig__nrofSlots__n8
  | _ => PUCCH_FormatConfig__nrofSlots__n2
  end.
Lemma PUCCH_FormatConfig__nrofSlots__F1F2 : forall x : PUCCH_FormatConfig__nrofSlots__Type, (PUCCH_FormatConfig__nrofSlots__F1 x <= 2) /\ PUCCH_FormatConfig__nrofSlots__F2 (PUCCH_FormatConfig__nrofSlots__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_FormatConfig__nrofSlots__F2F1 : forall (y : nat) (H : y <= 2), PUCCH_FormatConfig__nrofSlots__F1 (PUCCH_FormatConfig__nrofSlots__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_FormatConfig__pi2BPSK__Type : Set :=
 | PUCCH_FormatConfig__pi2BPSK__enabled
.
Definition PUCCH_FormatConfig__pi2BPSK__cond := (fun (_ : PUCCH_FormatConfig__pi2BPSK__Type) => True).
Lemma PUCCH_FormatConfig__pi2BPSK__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_FormatConfig__pi2BPSK__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_FormatConfig__pi2BPSK__nat__helper.

Definition PUCCH_FormatConfig__pi2BPSK__F1 t :=
  match t with
  | PUCCH_FormatConfig__pi2BPSK__enabled => 0
  end.
Definition PUCCH_FormatConfig__pi2BPSK__F2 n :=
  match n with
  | 0 => PUCCH_FormatConfig__pi2BPSK__enabled
  | _ => PUCCH_FormatConfig__pi2BPSK__enabled
  end.
Lemma PUCCH_FormatConfig__pi2BPSK__F1F2 : forall x : PUCCH_FormatConfig__pi2BPSK__Type, (PUCCH_FormatConfig__pi2BPSK__F1 x <= 0) /\ PUCCH_FormatConfig__pi2BPSK__F2 (PUCCH_FormatConfig__pi2BPSK__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_FormatConfig__pi2BPSK__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_FormatConfig__pi2BPSK__F1 (PUCCH_FormatConfig__pi2BPSK__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Type : Set :=
 | PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__true
.
Definition PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__cond := (fun (_ : PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Type) => True).
Lemma PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__nat__helper.

Definition PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1 t :=
  match t with
  | PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__true => 0
  end.
Definition PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F2 n :=
  match n with
  | 0 => PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__true
  | _ => PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__true
  end.
Lemma PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1F2 : forall x : PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Type, (PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1 x <= 0) /\ PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F2 (PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1 (PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F2 y) = y. enum_solve H y. Qed.

Record PUCCH_FormatConfig__Type : Set :=
  make__PUCCH_FormatConfig__Type {
    PUCCH_FormatConfig__interslotFrequencyHopping : option PUCCH_FormatConfig__interslotFrequencyHopping__Type ;
    PUCCH_FormatConfig__additionalDMRS : option PUCCH_FormatConfig__additionalDMRS__Type ;
    PUCCH_FormatConfig__maxCodeRate : option PUCCH_MaxCodeRate__Type ;
    PUCCH_FormatConfig__nrofSlots : option PUCCH_FormatConfig__nrofSlots__Type ;
    PUCCH_FormatConfig__pi2BPSK : option PUCCH_FormatConfig__pi2BPSK__Type ;
    PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI : option PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Type ;
}.
Definition PUCCH_FormatConfig__list := (
 Opt PUCCH_FormatConfig__interslotFrequencyHopping__Type PUCCH_FormatConfig__interslotFrequencyHopping__cond ::
 Opt PUCCH_FormatConfig__additionalDMRS__Type PUCCH_FormatConfig__additionalDMRS__cond ::
 Opt PUCCH_MaxCodeRate__Type PUCCH_MaxCodeRate__cond ::
 Opt PUCCH_FormatConfig__nrofSlots__Type PUCCH_FormatConfig__nrofSlots__cond ::
 Opt PUCCH_FormatConfig__pi2BPSK__Type PUCCH_FormatConfig__pi2BPSK__cond ::
 Opt PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Type PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__cond ::
 nil).
Definition PUCCH_FormatConfig__cond z := 
  opt_cond PUCCH_FormatConfig__interslotFrequencyHopping__cond (PUCCH_FormatConfig__interslotFrequencyHopping z) /\
  opt_cond PUCCH_FormatConfig__additionalDMRS__cond (PUCCH_FormatConfig__additionalDMRS z) /\
  opt_cond PUCCH_MaxCodeRate__cond (PUCCH_FormatConfig__maxCodeRate z) /\
  opt_cond PUCCH_FormatConfig__nrofSlots__cond (PUCCH_FormatConfig__nrofSlots z) /\
  opt_cond PUCCH_FormatConfig__pi2BPSK__cond (PUCCH_FormatConfig__pi2BPSK z) /\
  opt_cond PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__cond (PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI z) /\
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
Definition PUCCH_FormatConfig__interslotFrequencyHopping__Format : T_Format PUCCH_FormatConfig__interslotFrequencyHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_FormatConfig__interslotFrequencyHopping__nat__Format PUCCH_FormatConfig__interslotFrequencyHopping__F1 PUCCH_FormatConfig__interslotFrequencyHopping__F2 PUCCH_FormatConfig__interslotFrequencyHopping__F1F2 PUCCH_FormatConfig__interslotFrequencyHopping__F2F1.

Opaque PUCCH_FormatConfig__interslotFrequencyHopping__cond PUCCH_FormatConfig__interslotFrequencyHopping__Format.

Definition PUCCH_FormatConfig__additionalDMRS__Format : T_Format PUCCH_FormatConfig__additionalDMRS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_FormatConfig__additionalDMRS__nat__Format PUCCH_FormatConfig__additionalDMRS__F1 PUCCH_FormatConfig__additionalDMRS__F2 PUCCH_FormatConfig__additionalDMRS__F1F2 PUCCH_FormatConfig__additionalDMRS__F2F1.

Opaque PUCCH_FormatConfig__additionalDMRS__cond PUCCH_FormatConfig__additionalDMRS__Format.

Definition PUCCH_FormatConfig__nrofSlots__Format : T_Format PUCCH_FormatConfig__nrofSlots__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_FormatConfig__nrofSlots__nat__Format PUCCH_FormatConfig__nrofSlots__F1 PUCCH_FormatConfig__nrofSlots__F2 PUCCH_FormatConfig__nrofSlots__F1F2 PUCCH_FormatConfig__nrofSlots__F2F1.

Opaque PUCCH_FormatConfig__nrofSlots__cond PUCCH_FormatConfig__nrofSlots__Format.

Definition PUCCH_FormatConfig__pi2BPSK__Format : T_Format PUCCH_FormatConfig__pi2BPSK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_FormatConfig__pi2BPSK__nat__Format PUCCH_FormatConfig__pi2BPSK__F1 PUCCH_FormatConfig__pi2BPSK__F2 PUCCH_FormatConfig__pi2BPSK__F1F2 PUCCH_FormatConfig__pi2BPSK__F2F1.

Opaque PUCCH_FormatConfig__pi2BPSK__cond PUCCH_FormatConfig__pi2BPSK__Format.

Definition PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Format : T_Format PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__nat__Format PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1 PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F2 PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F1F2 PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__F2F1.

Opaque PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__cond PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Format.


Definition PUCCH_FormatConfig__Format_Type := Eval cbn in seq_format_prod PUCCH_FormatConfig__list.
Definition PUCCH_FormatConfig__Format_list : PUCCH_FormatConfig__Format_Type :=
  (PUCCH_FormatConfig__interslotFrequencyHopping__Format, (PUCCH_FormatConfig__additionalDMRS__Format, (PUCCH_MaxCodeRate__Format, (PUCCH_FormatConfig__nrofSlots__Format, (PUCCH_FormatConfig__pi2BPSK__Format, (PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI__Format, unit_format)))))).
Definition PUCCH_FormatConfig__list__Format := (*Eval compute in *) seq_format PUCCH_FormatConfig__list PUCCH_FormatConfig__Format_list.
Definition PUCCH_FormatConfig__F1 z :=
  (PUCCH_FormatConfig__interslotFrequencyHopping z, (PUCCH_FormatConfig__additionalDMRS z, (PUCCH_FormatConfig__maxCodeRate z, (PUCCH_FormatConfig__nrofSlots z, (PUCCH_FormatConfig__pi2BPSK z, (PUCCH_FormatConfig__simultaneousHARQ_ACK_CSI z, tt)))))).
Definition PUCCH_FormatConfig__F2 (y : seq_type PUCCH_FormatConfig__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__PUCCH_FormatConfig__Type i0 i1 i2 i3 i4 i5
  end.
Lemma PUCCH_FormatConfig__F1F2_cond (z : PUCCH_FormatConfig__Type)
  : PUCCH_FormatConfig__cond z ->
  (seq_cond PUCCH_FormatConfig__list (PUCCH_FormatConfig__F1 z)).
intro H. unfold PUCCH_FormatConfig__cond in H. simpl. auto. Qed.
Lemma PUCCH_FormatConfig__F1F2_cond2 (z : PUCCH_FormatConfig__Type)
 : PUCCH_FormatConfig__F2 (PUCCH_FormatConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_FormatConfig__F2F1_cond (y : seq_type PUCCH_FormatConfig__list)
  : seq_cond PUCCH_FormatConfig__list y ->
 (PUCCH_FormatConfig__cond (PUCCH_FormatConfig__F2 y)) /\  PUCCH_FormatConfig__F1 (PUCCH_FormatConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_FormatConfig__cond. simpl in *. auto.
 - simpl. unfold PUCCH_FormatConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_FormatConfig__Format : T_Format PUCCH_FormatConfig__Type PUCCH_FormatConfig__cond :=
        proj2_format  PUCCH_FormatConfig__cond PUCCH_FormatConfig__list__Format
    PUCCH_FormatConfig__F1 PUCCH_FormatConfig__F2 PUCCH_FormatConfig__F1F2_cond  PUCCH_FormatConfig__F1F2_cond2 PUCCH_FormatConfig__F2F1_cond.
Opaque PUCCH_FormatConfig__cond PUCCH_FormatConfig__Format.

