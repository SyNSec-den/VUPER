Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RepFactorAndTimeGap_r17__repetitionFactor_r17__Type : Set :=
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__n2
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__n4
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__n6
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__n8
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__n16
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__n32
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__spare2
 | RepFactorAndTimeGap_r17__repetitionFactor_r17__spare1
.
Definition RepFactorAndTimeGap_r17__repetitionFactor_r17__cond := (fun (_ : RepFactorAndTimeGap_r17__repetitionFactor_r17__Type) => True).
Lemma RepFactorAndTimeGap_r17__repetitionFactor_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RepFactorAndTimeGap_r17__repetitionFactor_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RepFactorAndTimeGap_r17__repetitionFactor_r17__nat__helper.

Definition RepFactorAndTimeGap_r17__repetitionFactor_r17__F1 t :=
  match t with
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__n2 => 0
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__n4 => 1
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__n6 => 2
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__n8 => 3
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__n16 => 4
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__n32 => 5
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__spare2 => 6
  | RepFactorAndTimeGap_r17__repetitionFactor_r17__spare1 => 7
  end.
Definition RepFactorAndTimeGap_r17__repetitionFactor_r17__F2 n :=
  match n with
  | 0 => RepFactorAndTimeGap_r17__repetitionFactor_r17__n2
  | 1 => RepFactorAndTimeGap_r17__repetitionFactor_r17__n4
  | 2 => RepFactorAndTimeGap_r17__repetitionFactor_r17__n6
  | 3 => RepFactorAndTimeGap_r17__repetitionFactor_r17__n8
  | 4 => RepFactorAndTimeGap_r17__repetitionFactor_r17__n16
  | 5 => RepFactorAndTimeGap_r17__repetitionFactor_r17__n32
  | 6 => RepFactorAndTimeGap_r17__repetitionFactor_r17__spare2
  | 7 => RepFactorAndTimeGap_r17__repetitionFactor_r17__spare1
  | _ => RepFactorAndTimeGap_r17__repetitionFactor_r17__n2
  end.
Lemma RepFactorAndTimeGap_r17__repetitionFactor_r17__F1F2 : forall x : RepFactorAndTimeGap_r17__repetitionFactor_r17__Type, (RepFactorAndTimeGap_r17__repetitionFactor_r17__F1 x <= 7) /\ RepFactorAndTimeGap_r17__repetitionFactor_r17__F2 (RepFactorAndTimeGap_r17__repetitionFactor_r17__F1 x) = x. imp_solve. Qed.
Lemma RepFactorAndTimeGap_r17__repetitionFactor_r17__F2F1 : forall (y : nat) (H : y <= 7), RepFactorAndTimeGap_r17__repetitionFactor_r17__F1 (RepFactorAndTimeGap_r17__repetitionFactor_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RepFactorAndTimeGap_r17__timeGap_r17__Type : Set :=
 | RepFactorAndTimeGap_r17__timeGap_r17__s1
 | RepFactorAndTimeGap_r17__timeGap_r17__s2
 | RepFactorAndTimeGap_r17__timeGap_r17__s4
 | RepFactorAndTimeGap_r17__timeGap_r17__s8
 | RepFactorAndTimeGap_r17__timeGap_r17__s16
 | RepFactorAndTimeGap_r17__timeGap_r17__s32
 | RepFactorAndTimeGap_r17__timeGap_r17__spare2
 | RepFactorAndTimeGap_r17__timeGap_r17__spare1
.
Definition RepFactorAndTimeGap_r17__timeGap_r17__cond := (fun (_ : RepFactorAndTimeGap_r17__timeGap_r17__Type) => True).
Lemma RepFactorAndTimeGap_r17__timeGap_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RepFactorAndTimeGap_r17__timeGap_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RepFactorAndTimeGap_r17__timeGap_r17__nat__helper.

Definition RepFactorAndTimeGap_r17__timeGap_r17__F1 t :=
  match t with
  | RepFactorAndTimeGap_r17__timeGap_r17__s1 => 0
  | RepFactorAndTimeGap_r17__timeGap_r17__s2 => 1
  | RepFactorAndTimeGap_r17__timeGap_r17__s4 => 2
  | RepFactorAndTimeGap_r17__timeGap_r17__s8 => 3
  | RepFactorAndTimeGap_r17__timeGap_r17__s16 => 4
  | RepFactorAndTimeGap_r17__timeGap_r17__s32 => 5
  | RepFactorAndTimeGap_r17__timeGap_r17__spare2 => 6
  | RepFactorAndTimeGap_r17__timeGap_r17__spare1 => 7
  end.
Definition RepFactorAndTimeGap_r17__timeGap_r17__F2 n :=
  match n with
  | 0 => RepFactorAndTimeGap_r17__timeGap_r17__s1
  | 1 => RepFactorAndTimeGap_r17__timeGap_r17__s2
  | 2 => RepFactorAndTimeGap_r17__timeGap_r17__s4
  | 3 => RepFactorAndTimeGap_r17__timeGap_r17__s8
  | 4 => RepFactorAndTimeGap_r17__timeGap_r17__s16
  | 5 => RepFactorAndTimeGap_r17__timeGap_r17__s32
  | 6 => RepFactorAndTimeGap_r17__timeGap_r17__spare2
  | 7 => RepFactorAndTimeGap_r17__timeGap_r17__spare1
  | _ => RepFactorAndTimeGap_r17__timeGap_r17__s1
  end.
Lemma RepFactorAndTimeGap_r17__timeGap_r17__F1F2 : forall x : RepFactorAndTimeGap_r17__timeGap_r17__Type, (RepFactorAndTimeGap_r17__timeGap_r17__F1 x <= 7) /\ RepFactorAndTimeGap_r17__timeGap_r17__F2 (RepFactorAndTimeGap_r17__timeGap_r17__F1 x) = x. imp_solve. Qed.
Lemma RepFactorAndTimeGap_r17__timeGap_r17__F2F1 : forall (y : nat) (H : y <= 7), RepFactorAndTimeGap_r17__timeGap_r17__F1 (RepFactorAndTimeGap_r17__timeGap_r17__F2 y) = y. enum_solve H y. Qed.

Record RepFactorAndTimeGap_r17__Type : Set :=
  make__RepFactorAndTimeGap_r17__Type {
    RepFactorAndTimeGap_r17__repetitionFactor_r17 : RepFactorAndTimeGap_r17__repetitionFactor_r17__Type ;
    RepFactorAndTimeGap_r17__timeGap_r17 : RepFactorAndTimeGap_r17__timeGap_r17__Type ;
}.
Definition RepFactorAndTimeGap_r17__list := (
 Nor RepFactorAndTimeGap_r17__repetitionFactor_r17__Type RepFactorAndTimeGap_r17__repetitionFactor_r17__cond ::
 Nor RepFactorAndTimeGap_r17__timeGap_r17__Type RepFactorAndTimeGap_r17__timeGap_r17__cond ::
 nil).
Definition RepFactorAndTimeGap_r17__cond z := 
  RepFactorAndTimeGap_r17__repetitionFactor_r17__cond (RepFactorAndTimeGap_r17__repetitionFactor_r17 z) /\
  RepFactorAndTimeGap_r17__timeGap_r17__cond (RepFactorAndTimeGap_r17__timeGap_r17 z) /\
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
Definition RepFactorAndTimeGap_r17__repetitionFactor_r17__Format : T_Format RepFactorAndTimeGap_r17__repetitionFactor_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RepFactorAndTimeGap_r17__repetitionFactor_r17__nat__Format RepFactorAndTimeGap_r17__repetitionFactor_r17__F1 RepFactorAndTimeGap_r17__repetitionFactor_r17__F2 RepFactorAndTimeGap_r17__repetitionFactor_r17__F1F2 RepFactorAndTimeGap_r17__repetitionFactor_r17__F2F1.

Opaque RepFactorAndTimeGap_r17__repetitionFactor_r17__cond RepFactorAndTimeGap_r17__repetitionFactor_r17__Format.

Definition RepFactorAndTimeGap_r17__timeGap_r17__Format : T_Format RepFactorAndTimeGap_r17__timeGap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RepFactorAndTimeGap_r17__timeGap_r17__nat__Format RepFactorAndTimeGap_r17__timeGap_r17__F1 RepFactorAndTimeGap_r17__timeGap_r17__F2 RepFactorAndTimeGap_r17__timeGap_r17__F1F2 RepFactorAndTimeGap_r17__timeGap_r17__F2F1.

Opaque RepFactorAndTimeGap_r17__timeGap_r17__cond RepFactorAndTimeGap_r17__timeGap_r17__Format.


Definition RepFactorAndTimeGap_r17__Format_Type := Eval cbn in seq_format_prod RepFactorAndTimeGap_r17__list.
Definition RepFactorAndTimeGap_r17__Format_list : RepFactorAndTimeGap_r17__Format_Type :=
  (RepFactorAndTimeGap_r17__repetitionFactor_r17__Format, (RepFactorAndTimeGap_r17__timeGap_r17__Format, unit_format)).
Definition RepFactorAndTimeGap_r17__list__Format := (*Eval compute in *) seq_format RepFactorAndTimeGap_r17__list RepFactorAndTimeGap_r17__Format_list.
Definition RepFactorAndTimeGap_r17__F1 z :=
  (RepFactorAndTimeGap_r17__repetitionFactor_r17 z, (RepFactorAndTimeGap_r17__timeGap_r17 z, tt)).
Definition RepFactorAndTimeGap_r17__F2 (y : seq_type RepFactorAndTimeGap_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RepFactorAndTimeGap_r17__Type i0 i1
  end.
Lemma RepFactorAndTimeGap_r17__F1F2_cond (z : RepFactorAndTimeGap_r17__Type)
  : RepFactorAndTimeGap_r17__cond z ->
  (seq_cond RepFactorAndTimeGap_r17__list (RepFactorAndTimeGap_r17__F1 z)).
intro H. unfold RepFactorAndTimeGap_r17__cond in H. simpl. auto. Qed.
Lemma RepFactorAndTimeGap_r17__F1F2_cond2 (z : RepFactorAndTimeGap_r17__Type)
 : RepFactorAndTimeGap_r17__F2 (RepFactorAndTimeGap_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RepFactorAndTimeGap_r17__F2F1_cond (y : seq_type RepFactorAndTimeGap_r17__list)
  : seq_cond RepFactorAndTimeGap_r17__list y ->
 (RepFactorAndTimeGap_r17__cond (RepFactorAndTimeGap_r17__F2 y)) /\  RepFactorAndTimeGap_r17__F1 (RepFactorAndTimeGap_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RepFactorAndTimeGap_r17__cond. simpl in *. auto.
 - simpl. unfold RepFactorAndTimeGap_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RepFactorAndTimeGap_r17__Format : T_Format RepFactorAndTimeGap_r17__Type RepFactorAndTimeGap_r17__cond :=
        proj2_format  RepFactorAndTimeGap_r17__cond RepFactorAndTimeGap_r17__list__Format
    RepFactorAndTimeGap_r17__F1 RepFactorAndTimeGap_r17__F2 RepFactorAndTimeGap_r17__F1F2_cond  RepFactorAndTimeGap_r17__F1F2_cond2 RepFactorAndTimeGap_r17__F2F1_cond.
Opaque RepFactorAndTimeGap_r17__cond RepFactorAndTimeGap_r17__Format.

