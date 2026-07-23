Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MinTimeGapFR2_2_r17__scs_120kHz_r17__Type : Set :=
 | MinTimeGapFR2_2_r17__scs_120kHz_r17__sl2
 | MinTimeGapFR2_2_r17__scs_120kHz_r17__sl24
.
Definition MinTimeGapFR2_2_r17__scs_120kHz_r17__cond := (fun (_ : MinTimeGapFR2_2_r17__scs_120kHz_r17__Type) => True).
Lemma MinTimeGapFR2_2_r17__scs_120kHz_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGapFR2_2_r17__scs_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGapFR2_2_r17__scs_120kHz_r17__nat__helper.

Definition MinTimeGapFR2_2_r17__scs_120kHz_r17__F1 t :=
  match t with
  | MinTimeGapFR2_2_r17__scs_120kHz_r17__sl2 => 0
  | MinTimeGapFR2_2_r17__scs_120kHz_r17__sl24 => 1
  end.
Definition MinTimeGapFR2_2_r17__scs_120kHz_r17__F2 n :=
  match n with
  | 0 => MinTimeGapFR2_2_r17__scs_120kHz_r17__sl2
  | 1 => MinTimeGapFR2_2_r17__scs_120kHz_r17__sl24
  | _ => MinTimeGapFR2_2_r17__scs_120kHz_r17__sl2
  end.
Lemma MinTimeGapFR2_2_r17__scs_120kHz_r17__F1F2 : forall x : MinTimeGapFR2_2_r17__scs_120kHz_r17__Type, (MinTimeGapFR2_2_r17__scs_120kHz_r17__F1 x <= 1) /\ MinTimeGapFR2_2_r17__scs_120kHz_r17__F2 (MinTimeGapFR2_2_r17__scs_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGapFR2_2_r17__scs_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGapFR2_2_r17__scs_120kHz_r17__F1 (MinTimeGapFR2_2_r17__scs_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MinTimeGapFR2_2_r17__scs_480kHz_r17__Type : Set :=
 | MinTimeGapFR2_2_r17__scs_480kHz_r17__sl8
 | MinTimeGapFR2_2_r17__scs_480kHz_r17__sl96
.
Definition MinTimeGapFR2_2_r17__scs_480kHz_r17__cond := (fun (_ : MinTimeGapFR2_2_r17__scs_480kHz_r17__Type) => True).
Lemma MinTimeGapFR2_2_r17__scs_480kHz_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGapFR2_2_r17__scs_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGapFR2_2_r17__scs_480kHz_r17__nat__helper.

Definition MinTimeGapFR2_2_r17__scs_480kHz_r17__F1 t :=
  match t with
  | MinTimeGapFR2_2_r17__scs_480kHz_r17__sl8 => 0
  | MinTimeGapFR2_2_r17__scs_480kHz_r17__sl96 => 1
  end.
Definition MinTimeGapFR2_2_r17__scs_480kHz_r17__F2 n :=
  match n with
  | 0 => MinTimeGapFR2_2_r17__scs_480kHz_r17__sl8
  | 1 => MinTimeGapFR2_2_r17__scs_480kHz_r17__sl96
  | _ => MinTimeGapFR2_2_r17__scs_480kHz_r17__sl8
  end.
Lemma MinTimeGapFR2_2_r17__scs_480kHz_r17__F1F2 : forall x : MinTimeGapFR2_2_r17__scs_480kHz_r17__Type, (MinTimeGapFR2_2_r17__scs_480kHz_r17__F1 x <= 1) /\ MinTimeGapFR2_2_r17__scs_480kHz_r17__F2 (MinTimeGapFR2_2_r17__scs_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGapFR2_2_r17__scs_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGapFR2_2_r17__scs_480kHz_r17__F1 (MinTimeGapFR2_2_r17__scs_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MinTimeGapFR2_2_r17__scs_960kHz_r17__Type : Set :=
 | MinTimeGapFR2_2_r17__scs_960kHz_r17__sl16
 | MinTimeGapFR2_2_r17__scs_960kHz_r17__sl192
.
Definition MinTimeGapFR2_2_r17__scs_960kHz_r17__cond := (fun (_ : MinTimeGapFR2_2_r17__scs_960kHz_r17__Type) => True).
Lemma MinTimeGapFR2_2_r17__scs_960kHz_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGapFR2_2_r17__scs_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGapFR2_2_r17__scs_960kHz_r17__nat__helper.

Definition MinTimeGapFR2_2_r17__scs_960kHz_r17__F1 t :=
  match t with
  | MinTimeGapFR2_2_r17__scs_960kHz_r17__sl16 => 0
  | MinTimeGapFR2_2_r17__scs_960kHz_r17__sl192 => 1
  end.
Definition MinTimeGapFR2_2_r17__scs_960kHz_r17__F2 n :=
  match n with
  | 0 => MinTimeGapFR2_2_r17__scs_960kHz_r17__sl16
  | 1 => MinTimeGapFR2_2_r17__scs_960kHz_r17__sl192
  | _ => MinTimeGapFR2_2_r17__scs_960kHz_r17__sl16
  end.
Lemma MinTimeGapFR2_2_r17__scs_960kHz_r17__F1F2 : forall x : MinTimeGapFR2_2_r17__scs_960kHz_r17__Type, (MinTimeGapFR2_2_r17__scs_960kHz_r17__F1 x <= 1) /\ MinTimeGapFR2_2_r17__scs_960kHz_r17__F2 (MinTimeGapFR2_2_r17__scs_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGapFR2_2_r17__scs_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGapFR2_2_r17__scs_960kHz_r17__F1 (MinTimeGapFR2_2_r17__scs_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Record MinTimeGapFR2_2_r17__Type : Set :=
  make__MinTimeGapFR2_2_r17__Type {
    MinTimeGapFR2_2_r17__scs_120kHz_r17 : option MinTimeGapFR2_2_r17__scs_120kHz_r17__Type ;
    MinTimeGapFR2_2_r17__scs_480kHz_r17 : option MinTimeGapFR2_2_r17__scs_480kHz_r17__Type ;
    MinTimeGapFR2_2_r17__scs_960kHz_r17 : option MinTimeGapFR2_2_r17__scs_960kHz_r17__Type ;
}.
Definition MinTimeGapFR2_2_r17__list := (
 Opt MinTimeGapFR2_2_r17__scs_120kHz_r17__Type MinTimeGapFR2_2_r17__scs_120kHz_r17__cond ::
 Opt MinTimeGapFR2_2_r17__scs_480kHz_r17__Type MinTimeGapFR2_2_r17__scs_480kHz_r17__cond ::
 Opt MinTimeGapFR2_2_r17__scs_960kHz_r17__Type MinTimeGapFR2_2_r17__scs_960kHz_r17__cond ::
 nil).
Definition MinTimeGapFR2_2_r17__cond z := 
  opt_cond MinTimeGapFR2_2_r17__scs_120kHz_r17__cond (MinTimeGapFR2_2_r17__scs_120kHz_r17 z) /\
  opt_cond MinTimeGapFR2_2_r17__scs_480kHz_r17__cond (MinTimeGapFR2_2_r17__scs_480kHz_r17 z) /\
  opt_cond MinTimeGapFR2_2_r17__scs_960kHz_r17__cond (MinTimeGapFR2_2_r17__scs_960kHz_r17 z) /\
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
Definition MinTimeGapFR2_2_r17__scs_120kHz_r17__Format : T_Format MinTimeGapFR2_2_r17__scs_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGapFR2_2_r17__scs_120kHz_r17__nat__Format MinTimeGapFR2_2_r17__scs_120kHz_r17__F1 MinTimeGapFR2_2_r17__scs_120kHz_r17__F2 MinTimeGapFR2_2_r17__scs_120kHz_r17__F1F2 MinTimeGapFR2_2_r17__scs_120kHz_r17__F2F1.

Opaque MinTimeGapFR2_2_r17__scs_120kHz_r17__cond MinTimeGapFR2_2_r17__scs_120kHz_r17__Format.

Definition MinTimeGapFR2_2_r17__scs_480kHz_r17__Format : T_Format MinTimeGapFR2_2_r17__scs_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGapFR2_2_r17__scs_480kHz_r17__nat__Format MinTimeGapFR2_2_r17__scs_480kHz_r17__F1 MinTimeGapFR2_2_r17__scs_480kHz_r17__F2 MinTimeGapFR2_2_r17__scs_480kHz_r17__F1F2 MinTimeGapFR2_2_r17__scs_480kHz_r17__F2F1.

Opaque MinTimeGapFR2_2_r17__scs_480kHz_r17__cond MinTimeGapFR2_2_r17__scs_480kHz_r17__Format.

Definition MinTimeGapFR2_2_r17__scs_960kHz_r17__Format : T_Format MinTimeGapFR2_2_r17__scs_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGapFR2_2_r17__scs_960kHz_r17__nat__Format MinTimeGapFR2_2_r17__scs_960kHz_r17__F1 MinTimeGapFR2_2_r17__scs_960kHz_r17__F2 MinTimeGapFR2_2_r17__scs_960kHz_r17__F1F2 MinTimeGapFR2_2_r17__scs_960kHz_r17__F2F1.

Opaque MinTimeGapFR2_2_r17__scs_960kHz_r17__cond MinTimeGapFR2_2_r17__scs_960kHz_r17__Format.


Definition MinTimeGapFR2_2_r17__Format_Type := Eval cbn in seq_format_prod MinTimeGapFR2_2_r17__list.
Definition MinTimeGapFR2_2_r17__Format_list : MinTimeGapFR2_2_r17__Format_Type :=
  (MinTimeGapFR2_2_r17__scs_120kHz_r17__Format, (MinTimeGapFR2_2_r17__scs_480kHz_r17__Format, (MinTimeGapFR2_2_r17__scs_960kHz_r17__Format, unit_format))).
Definition MinTimeGapFR2_2_r17__list__Format := (*Eval compute in *) seq_format MinTimeGapFR2_2_r17__list MinTimeGapFR2_2_r17__Format_list.
Definition MinTimeGapFR2_2_r17__F1 z :=
  (MinTimeGapFR2_2_r17__scs_120kHz_r17 z, (MinTimeGapFR2_2_r17__scs_480kHz_r17 z, (MinTimeGapFR2_2_r17__scs_960kHz_r17 z, tt))).
Definition MinTimeGapFR2_2_r17__F2 (y : seq_type MinTimeGapFR2_2_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MinTimeGapFR2_2_r17__Type i0 i1 i2
  end.
Lemma MinTimeGapFR2_2_r17__F1F2_cond (z : MinTimeGapFR2_2_r17__Type)
  : MinTimeGapFR2_2_r17__cond z ->
  (seq_cond MinTimeGapFR2_2_r17__list (MinTimeGapFR2_2_r17__F1 z)).
intro H. unfold MinTimeGapFR2_2_r17__cond in H. simpl. auto. Qed.
Lemma MinTimeGapFR2_2_r17__F1F2_cond2 (z : MinTimeGapFR2_2_r17__Type)
 : MinTimeGapFR2_2_r17__F2 (MinTimeGapFR2_2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MinTimeGapFR2_2_r17__F2F1_cond (y : seq_type MinTimeGapFR2_2_r17__list)
  : seq_cond MinTimeGapFR2_2_r17__list y ->
 (MinTimeGapFR2_2_r17__cond (MinTimeGapFR2_2_r17__F2 y)) /\  MinTimeGapFR2_2_r17__F1 (MinTimeGapFR2_2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MinTimeGapFR2_2_r17__cond. simpl in *. auto.
 - simpl. unfold MinTimeGapFR2_2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MinTimeGapFR2_2_r17__Format : T_Format MinTimeGapFR2_2_r17__Type MinTimeGapFR2_2_r17__cond :=
        proj2_format  MinTimeGapFR2_2_r17__cond MinTimeGapFR2_2_r17__list__Format
    MinTimeGapFR2_2_r17__F1 MinTimeGapFR2_2_r17__F2 MinTimeGapFR2_2_r17__F1F2_cond  MinTimeGapFR2_2_r17__F1F2_cond2 MinTimeGapFR2_2_r17__F2F1_cond.
Opaque MinTimeGapFR2_2_r17__cond MinTimeGapFR2_2_r17__Format.

