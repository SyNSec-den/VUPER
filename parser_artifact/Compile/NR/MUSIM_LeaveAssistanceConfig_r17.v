Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Type : Set :=
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms10
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms20
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms40
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms60
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms80
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms100
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__spare2
 | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__spare1
.
Definition MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__cond := (fun (_ : MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Type) => True).
Lemma MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__nat__helper.

Definition MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1 t :=
  match t with
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms10 => 0
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms20 => 1
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms40 => 2
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms60 => 3
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms80 => 4
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms100 => 5
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__spare2 => 6
  | MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__spare1 => 7
  end.
Definition MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F2 n :=
  match n with
  | 0 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms10
  | 1 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms20
  | 2 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms40
  | 3 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms60
  | 4 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms80
  | 5 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms100
  | 6 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__spare2
  | 7 => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__spare1
  | _ => MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__ms10
  end.
Lemma MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1F2 : forall x : MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Type, (MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1 x <= 7) /\ MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F2 (MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F2F1 : forall (y : nat) (H : y <= 7), MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1 (MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F2 y) = y. enum_solve H y. Qed.

Record MUSIM_LeaveAssistanceConfig_r17__Type : Set :=
  make__MUSIM_LeaveAssistanceConfig_r17__Type {
    MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17 : MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Type ;
}.
Definition MUSIM_LeaveAssistanceConfig_r17__list := (
 Nor MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Type MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__cond ::
 nil).
Definition MUSIM_LeaveAssistanceConfig_r17__cond z := 
  MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__cond (MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17 z) /\
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
Definition MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Format : T_Format MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__nat__Format MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1 MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F2 MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F1F2 MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__F2F1.

Opaque MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__cond MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Format.


Definition MUSIM_LeaveAssistanceConfig_r17__Format_Type := Eval cbn in seq_format_prod MUSIM_LeaveAssistanceConfig_r17__list.
Definition MUSIM_LeaveAssistanceConfig_r17__Format_list : MUSIM_LeaveAssistanceConfig_r17__Format_Type :=
  (MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17__Format, unit_format).
Definition MUSIM_LeaveAssistanceConfig_r17__list__Format := (*Eval compute in *) seq_format MUSIM_LeaveAssistanceConfig_r17__list MUSIM_LeaveAssistanceConfig_r17__Format_list.
Definition MUSIM_LeaveAssistanceConfig_r17__F1 z :=
  (MUSIM_LeaveAssistanceConfig_r17__musim_LeaveWithoutResponseTimer_r17 z, tt).
Definition MUSIM_LeaveAssistanceConfig_r17__F2 (y : seq_type MUSIM_LeaveAssistanceConfig_r17__list) :=
  match y with
  | (i0, _)=>
    make__MUSIM_LeaveAssistanceConfig_r17__Type i0
  end.
Lemma MUSIM_LeaveAssistanceConfig_r17__F1F2_cond (z : MUSIM_LeaveAssistanceConfig_r17__Type)
  : MUSIM_LeaveAssistanceConfig_r17__cond z ->
  (seq_cond MUSIM_LeaveAssistanceConfig_r17__list (MUSIM_LeaveAssistanceConfig_r17__F1 z)).
intro H. unfold MUSIM_LeaveAssistanceConfig_r17__cond in H. simpl. auto. Qed.
Lemma MUSIM_LeaveAssistanceConfig_r17__F1F2_cond2 (z : MUSIM_LeaveAssistanceConfig_r17__Type)
 : MUSIM_LeaveAssistanceConfig_r17__F2 (MUSIM_LeaveAssistanceConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MUSIM_LeaveAssistanceConfig_r17__F2F1_cond (y : seq_type MUSIM_LeaveAssistanceConfig_r17__list)
  : seq_cond MUSIM_LeaveAssistanceConfig_r17__list y ->
 (MUSIM_LeaveAssistanceConfig_r17__cond (MUSIM_LeaveAssistanceConfig_r17__F2 y)) /\  MUSIM_LeaveAssistanceConfig_r17__F1 (MUSIM_LeaveAssistanceConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MUSIM_LeaveAssistanceConfig_r17__cond. simpl in *. auto.
 - simpl. unfold MUSIM_LeaveAssistanceConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MUSIM_LeaveAssistanceConfig_r17__Format : T_Format MUSIM_LeaveAssistanceConfig_r17__Type MUSIM_LeaveAssistanceConfig_r17__cond :=
        proj2_format  MUSIM_LeaveAssistanceConfig_r17__cond MUSIM_LeaveAssistanceConfig_r17__list__Format
    MUSIM_LeaveAssistanceConfig_r17__F1 MUSIM_LeaveAssistanceConfig_r17__F2 MUSIM_LeaveAssistanceConfig_r17__F1F2_cond  MUSIM_LeaveAssistanceConfig_r17__F1F2_cond2 MUSIM_LeaveAssistanceConfig_r17__F2F1_cond.
Opaque MUSIM_LeaveAssistanceConfig_r17__cond MUSIM_LeaveAssistanceConfig_r17__Format.

