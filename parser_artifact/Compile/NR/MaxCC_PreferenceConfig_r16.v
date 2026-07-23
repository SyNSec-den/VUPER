Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Type : Set :=
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0dot5
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s1
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s2
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s3
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s4
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s5
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s6
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s7
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s8
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s9
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s10
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s20
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s30
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__spare2
 | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__spare1
.
Definition MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__cond := (fun (_ : MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Type) => True).
Lemma MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__nat__helper.

Definition MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1 t :=
  match t with
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0 => 0
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0dot5 => 1
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s1 => 2
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s2 => 3
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s3 => 4
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s4 => 5
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s5 => 6
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s6 => 7
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s7 => 8
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s8 => 9
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s9 => 10
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s10 => 11
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s20 => 12
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s30 => 13
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__spare2 => 14
  | MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__spare1 => 15
  end.
Definition MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F2 n :=
  match n with
  | 0 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0
  | 1 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0dot5
  | 2 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s1
  | 3 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s2
  | 4 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s3
  | 5 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s4
  | 6 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s5
  | 7 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s6
  | 8 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s7
  | 9 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s8
  | 10 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s9
  | 11 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s10
  | 12 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s20
  | 13 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s30
  | 14 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__spare2
  | 15 => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__spare1
  | _ => MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__s0
  end.
Lemma MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1F2 : forall x : MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Type, (MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1 x <= 15) /\ MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F2 (MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F2F1 : forall (y : nat) (H : y <= 15), MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1 (MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F2 y) = y. enum_solve H y. Qed.

Record MaxCC_PreferenceConfig_r16__Type : Set :=
  make__MaxCC_PreferenceConfig_r16__Type {
    MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16 : MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Type ;
}.
Definition MaxCC_PreferenceConfig_r16__list := (
 Nor MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Type MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__cond ::
 nil).
Definition MaxCC_PreferenceConfig_r16__cond z := 
  MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__cond (MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16 z) /\
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
Definition MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Format : T_Format MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__nat__Format MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1 MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F2 MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F1F2 MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__F2F1.

Opaque MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__cond MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Format.


Definition MaxCC_PreferenceConfig_r16__Format_Type := Eval cbn in seq_format_prod MaxCC_PreferenceConfig_r16__list.
Definition MaxCC_PreferenceConfig_r16__Format_list : MaxCC_PreferenceConfig_r16__Format_Type :=
  (MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16__Format, unit_format).
Definition MaxCC_PreferenceConfig_r16__list__Format := (*Eval compute in *) seq_format MaxCC_PreferenceConfig_r16__list MaxCC_PreferenceConfig_r16__Format_list.
Definition MaxCC_PreferenceConfig_r16__F1 z :=
  (MaxCC_PreferenceConfig_r16__maxCC_PreferenceProhibitTimer_r16 z, tt).
Definition MaxCC_PreferenceConfig_r16__F2 (y : seq_type MaxCC_PreferenceConfig_r16__list) :=
  match y with
  | (i0, _)=>
    make__MaxCC_PreferenceConfig_r16__Type i0
  end.
Lemma MaxCC_PreferenceConfig_r16__F1F2_cond (z : MaxCC_PreferenceConfig_r16__Type)
  : MaxCC_PreferenceConfig_r16__cond z ->
  (seq_cond MaxCC_PreferenceConfig_r16__list (MaxCC_PreferenceConfig_r16__F1 z)).
intro H. unfold MaxCC_PreferenceConfig_r16__cond in H. simpl. auto. Qed.
Lemma MaxCC_PreferenceConfig_r16__F1F2_cond2 (z : MaxCC_PreferenceConfig_r16__Type)
 : MaxCC_PreferenceConfig_r16__F2 (MaxCC_PreferenceConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MaxCC_PreferenceConfig_r16__F2F1_cond (y : seq_type MaxCC_PreferenceConfig_r16__list)
  : seq_cond MaxCC_PreferenceConfig_r16__list y ->
 (MaxCC_PreferenceConfig_r16__cond (MaxCC_PreferenceConfig_r16__F2 y)) /\  MaxCC_PreferenceConfig_r16__F1 (MaxCC_PreferenceConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MaxCC_PreferenceConfig_r16__cond. simpl in *. auto.
 - simpl. unfold MaxCC_PreferenceConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MaxCC_PreferenceConfig_r16__Format : T_Format MaxCC_PreferenceConfig_r16__Type MaxCC_PreferenceConfig_r16__cond :=
        proj2_format  MaxCC_PreferenceConfig_r16__cond MaxCC_PreferenceConfig_r16__list__Format
    MaxCC_PreferenceConfig_r16__F1 MaxCC_PreferenceConfig_r16__F2 MaxCC_PreferenceConfig_r16__F1F2_cond  MaxCC_PreferenceConfig_r16__F1F2_cond2 MaxCC_PreferenceConfig_r16__F2F1_cond.
Opaque MaxCC_PreferenceConfig_r16__cond MaxCC_PreferenceConfig_r16__Format.

