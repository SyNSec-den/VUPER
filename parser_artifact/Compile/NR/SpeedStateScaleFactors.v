Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SpeedStateScaleFactors__sf_Medium__Type : Set :=
 | SpeedStateScaleFactors__sf_Medium__oDot25
 | SpeedStateScaleFactors__sf_Medium__oDot5
 | SpeedStateScaleFactors__sf_Medium__oDot75
 | SpeedStateScaleFactors__sf_Medium__lDot0
.
Definition SpeedStateScaleFactors__sf_Medium__cond := (fun (_ : SpeedStateScaleFactors__sf_Medium__Type) => True).
Lemma SpeedStateScaleFactors__sf_Medium__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpeedStateScaleFactors__sf_Medium__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SpeedStateScaleFactors__sf_Medium__nat__helper.

Definition SpeedStateScaleFactors__sf_Medium__F1 t :=
  match t with
  | SpeedStateScaleFactors__sf_Medium__oDot25 => 0
  | SpeedStateScaleFactors__sf_Medium__oDot5 => 1
  | SpeedStateScaleFactors__sf_Medium__oDot75 => 2
  | SpeedStateScaleFactors__sf_Medium__lDot0 => 3
  end.
Definition SpeedStateScaleFactors__sf_Medium__F2 n :=
  match n with
  | 0 => SpeedStateScaleFactors__sf_Medium__oDot25
  | 1 => SpeedStateScaleFactors__sf_Medium__oDot5
  | 2 => SpeedStateScaleFactors__sf_Medium__oDot75
  | 3 => SpeedStateScaleFactors__sf_Medium__lDot0
  | _ => SpeedStateScaleFactors__sf_Medium__oDot25
  end.
Lemma SpeedStateScaleFactors__sf_Medium__F1F2 : forall x : SpeedStateScaleFactors__sf_Medium__Type, (SpeedStateScaleFactors__sf_Medium__F1 x <= 3) /\ SpeedStateScaleFactors__sf_Medium__F2 (SpeedStateScaleFactors__sf_Medium__F1 x) = x. imp_solve. Qed.
Lemma SpeedStateScaleFactors__sf_Medium__F2F1 : forall (y : nat) (H : y <= 3), SpeedStateScaleFactors__sf_Medium__F1 (SpeedStateScaleFactors__sf_Medium__F2 y) = y. enum_solve H y. Qed.

Inductive SpeedStateScaleFactors__sf_High__Type : Set :=
 | SpeedStateScaleFactors__sf_High__oDot25
 | SpeedStateScaleFactors__sf_High__oDot5
 | SpeedStateScaleFactors__sf_High__oDot75
 | SpeedStateScaleFactors__sf_High__lDot0
.
Definition SpeedStateScaleFactors__sf_High__cond := (fun (_ : SpeedStateScaleFactors__sf_High__Type) => True).
Lemma SpeedStateScaleFactors__sf_High__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpeedStateScaleFactors__sf_High__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SpeedStateScaleFactors__sf_High__nat__helper.

Definition SpeedStateScaleFactors__sf_High__F1 t :=
  match t with
  | SpeedStateScaleFactors__sf_High__oDot25 => 0
  | SpeedStateScaleFactors__sf_High__oDot5 => 1
  | SpeedStateScaleFactors__sf_High__oDot75 => 2
  | SpeedStateScaleFactors__sf_High__lDot0 => 3
  end.
Definition SpeedStateScaleFactors__sf_High__F2 n :=
  match n with
  | 0 => SpeedStateScaleFactors__sf_High__oDot25
  | 1 => SpeedStateScaleFactors__sf_High__oDot5
  | 2 => SpeedStateScaleFactors__sf_High__oDot75
  | 3 => SpeedStateScaleFactors__sf_High__lDot0
  | _ => SpeedStateScaleFactors__sf_High__oDot25
  end.
Lemma SpeedStateScaleFactors__sf_High__F1F2 : forall x : SpeedStateScaleFactors__sf_High__Type, (SpeedStateScaleFactors__sf_High__F1 x <= 3) /\ SpeedStateScaleFactors__sf_High__F2 (SpeedStateScaleFactors__sf_High__F1 x) = x. imp_solve. Qed.
Lemma SpeedStateScaleFactors__sf_High__F2F1 : forall (y : nat) (H : y <= 3), SpeedStateScaleFactors__sf_High__F1 (SpeedStateScaleFactors__sf_High__F2 y) = y. enum_solve H y. Qed.

Record SpeedStateScaleFactors__Type : Set :=
  make__SpeedStateScaleFactors__Type {
    SpeedStateScaleFactors__sf_Medium : SpeedStateScaleFactors__sf_Medium__Type ;
    SpeedStateScaleFactors__sf_High : SpeedStateScaleFactors__sf_High__Type ;
}.
Definition SpeedStateScaleFactors__list := (
 Nor SpeedStateScaleFactors__sf_Medium__Type SpeedStateScaleFactors__sf_Medium__cond ::
 Nor SpeedStateScaleFactors__sf_High__Type SpeedStateScaleFactors__sf_High__cond ::
 nil).
Definition SpeedStateScaleFactors__cond z := 
  SpeedStateScaleFactors__sf_Medium__cond (SpeedStateScaleFactors__sf_Medium z) /\
  SpeedStateScaleFactors__sf_High__cond (SpeedStateScaleFactors__sf_High z) /\
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
Definition SpeedStateScaleFactors__sf_Medium__Format : T_Format SpeedStateScaleFactors__sf_Medium__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpeedStateScaleFactors__sf_Medium__nat__Format SpeedStateScaleFactors__sf_Medium__F1 SpeedStateScaleFactors__sf_Medium__F2 SpeedStateScaleFactors__sf_Medium__F1F2 SpeedStateScaleFactors__sf_Medium__F2F1.

Opaque SpeedStateScaleFactors__sf_Medium__cond SpeedStateScaleFactors__sf_Medium__Format.

Definition SpeedStateScaleFactors__sf_High__Format : T_Format SpeedStateScaleFactors__sf_High__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpeedStateScaleFactors__sf_High__nat__Format SpeedStateScaleFactors__sf_High__F1 SpeedStateScaleFactors__sf_High__F2 SpeedStateScaleFactors__sf_High__F1F2 SpeedStateScaleFactors__sf_High__F2F1.

Opaque SpeedStateScaleFactors__sf_High__cond SpeedStateScaleFactors__sf_High__Format.


Definition SpeedStateScaleFactors__Format_Type := Eval cbn in seq_format_prod SpeedStateScaleFactors__list.
Definition SpeedStateScaleFactors__Format_list : SpeedStateScaleFactors__Format_Type :=
  (SpeedStateScaleFactors__sf_Medium__Format, (SpeedStateScaleFactors__sf_High__Format, unit_format)).
Definition SpeedStateScaleFactors__list__Format := (*Eval compute in *) seq_format SpeedStateScaleFactors__list SpeedStateScaleFactors__Format_list.
Definition SpeedStateScaleFactors__F1 z :=
  (SpeedStateScaleFactors__sf_Medium z, (SpeedStateScaleFactors__sf_High z, tt)).
Definition SpeedStateScaleFactors__F2 (y : seq_type SpeedStateScaleFactors__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SpeedStateScaleFactors__Type i0 i1
  end.
Lemma SpeedStateScaleFactors__F1F2_cond (z : SpeedStateScaleFactors__Type)
  : SpeedStateScaleFactors__cond z ->
  (seq_cond SpeedStateScaleFactors__list (SpeedStateScaleFactors__F1 z)).
intro H. unfold SpeedStateScaleFactors__cond in H. simpl. auto. Qed.
Lemma SpeedStateScaleFactors__F1F2_cond2 (z : SpeedStateScaleFactors__Type)
 : SpeedStateScaleFactors__F2 (SpeedStateScaleFactors__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SpeedStateScaleFactors__F2F1_cond (y : seq_type SpeedStateScaleFactors__list)
  : seq_cond SpeedStateScaleFactors__list y ->
 (SpeedStateScaleFactors__cond (SpeedStateScaleFactors__F2 y)) /\  SpeedStateScaleFactors__F1 (SpeedStateScaleFactors__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SpeedStateScaleFactors__cond. simpl in *. auto.
 - simpl. unfold SpeedStateScaleFactors__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SpeedStateScaleFactors__Format : T_Format SpeedStateScaleFactors__Type SpeedStateScaleFactors__cond :=
        proj2_format  SpeedStateScaleFactors__cond SpeedStateScaleFactors__list__Format
    SpeedStateScaleFactors__F1 SpeedStateScaleFactors__F2 SpeedStateScaleFactors__F1F2_cond  SpeedStateScaleFactors__F1F2_cond2 SpeedStateScaleFactors__F2F1_cond.
Opaque SpeedStateScaleFactors__cond SpeedStateScaleFactors__Format.

