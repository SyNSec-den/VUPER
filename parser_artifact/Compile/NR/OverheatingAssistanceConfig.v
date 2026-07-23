Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Type : Set :=
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0dot5
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s1
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s2
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s5
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s10
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s20
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s30
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s60
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s90
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s120
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s300
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s600
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare3
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare2
 | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare1
.
Definition OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__cond := (fun (_ : OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Type) => True).
Lemma OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__nat__helper.

Definition OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1 t :=
  match t with
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0 => 0
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0dot5 => 1
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s1 => 2
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s2 => 3
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s5 => 4
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s10 => 5
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s20 => 6
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s30 => 7
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s60 => 8
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s90 => 9
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s120 => 10
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s300 => 11
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s600 => 12
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare3 => 13
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare2 => 14
  | OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare1 => 15
  end.
Definition OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F2 n :=
  match n with
  | 0 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0
  | 1 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0dot5
  | 2 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s1
  | 3 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s2
  | 4 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s5
  | 5 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s10
  | 6 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s20
  | 7 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s30
  | 8 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s60
  | 9 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s90
  | 10 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s120
  | 11 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s300
  | 12 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s600
  | 13 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare3
  | 14 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare2
  | 15 => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__spare1
  | _ => OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__s0
  end.
Lemma OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1F2 : forall x : OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Type, (OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1 x <= 15) /\ OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F2 (OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F2F1 : forall (y : nat) (H : y <= 15), OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1 (OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Record OverheatingAssistanceConfig__Type : Set :=
  make__OverheatingAssistanceConfig__Type {
    OverheatingAssistanceConfig__overheatingIndicationProhibitTimer : OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Type ;
}.
Definition OverheatingAssistanceConfig__list := (
 Nor OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Type OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__cond ::
 nil).
Definition OverheatingAssistanceConfig__cond z := 
  OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__cond (OverheatingAssistanceConfig__overheatingIndicationProhibitTimer z) /\
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
Definition OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Format : T_Format OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__nat__Format OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1 OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F2 OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F1F2 OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__F2F1.

Opaque OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__cond OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Format.


Definition OverheatingAssistanceConfig__Format_Type := Eval cbn in seq_format_prod OverheatingAssistanceConfig__list.
Definition OverheatingAssistanceConfig__Format_list : OverheatingAssistanceConfig__Format_Type :=
  (OverheatingAssistanceConfig__overheatingIndicationProhibitTimer__Format, unit_format).
Definition OverheatingAssistanceConfig__list__Format := (*Eval compute in *) seq_format OverheatingAssistanceConfig__list OverheatingAssistanceConfig__Format_list.
Definition OverheatingAssistanceConfig__F1 z :=
  (OverheatingAssistanceConfig__overheatingIndicationProhibitTimer z, tt).
Definition OverheatingAssistanceConfig__F2 (y : seq_type OverheatingAssistanceConfig__list) :=
  match y with
  | (i0, _)=>
    make__OverheatingAssistanceConfig__Type i0
  end.
Lemma OverheatingAssistanceConfig__F1F2_cond (z : OverheatingAssistanceConfig__Type)
  : OverheatingAssistanceConfig__cond z ->
  (seq_cond OverheatingAssistanceConfig__list (OverheatingAssistanceConfig__F1 z)).
intro H. unfold OverheatingAssistanceConfig__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistanceConfig__F1F2_cond2 (z : OverheatingAssistanceConfig__Type)
 : OverheatingAssistanceConfig__F2 (OverheatingAssistanceConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistanceConfig__F2F1_cond (y : seq_type OverheatingAssistanceConfig__list)
  : seq_cond OverheatingAssistanceConfig__list y ->
 (OverheatingAssistanceConfig__cond (OverheatingAssistanceConfig__F2 y)) /\  OverheatingAssistanceConfig__F1 (OverheatingAssistanceConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistanceConfig__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistanceConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistanceConfig__Format : T_Format OverheatingAssistanceConfig__Type OverheatingAssistanceConfig__cond :=
        proj2_format  OverheatingAssistanceConfig__cond OverheatingAssistanceConfig__list__Format
    OverheatingAssistanceConfig__F1 OverheatingAssistanceConfig__F2 OverheatingAssistanceConfig__F1F2_cond  OverheatingAssistanceConfig__F1F2_cond2 OverheatingAssistanceConfig__F2F1_cond.
Opaque OverheatingAssistanceConfig__cond OverheatingAssistanceConfig__Format.

