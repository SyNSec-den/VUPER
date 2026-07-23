Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MinTimeGap_r16__scs_15kHz_r16__Type : Set :=
 | MinTimeGap_r16__scs_15kHz_r16__sl1
 | MinTimeGap_r16__scs_15kHz_r16__sl3
.
Definition MinTimeGap_r16__scs_15kHz_r16__cond := (fun (_ : MinTimeGap_r16__scs_15kHz_r16__Type) => True).
Lemma MinTimeGap_r16__scs_15kHz_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGap_r16__scs_15kHz_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGap_r16__scs_15kHz_r16__nat__helper.

Definition MinTimeGap_r16__scs_15kHz_r16__F1 t :=
  match t with
  | MinTimeGap_r16__scs_15kHz_r16__sl1 => 0
  | MinTimeGap_r16__scs_15kHz_r16__sl3 => 1
  end.
Definition MinTimeGap_r16__scs_15kHz_r16__F2 n :=
  match n with
  | 0 => MinTimeGap_r16__scs_15kHz_r16__sl1
  | 1 => MinTimeGap_r16__scs_15kHz_r16__sl3
  | _ => MinTimeGap_r16__scs_15kHz_r16__sl1
  end.
Lemma MinTimeGap_r16__scs_15kHz_r16__F1F2 : forall x : MinTimeGap_r16__scs_15kHz_r16__Type, (MinTimeGap_r16__scs_15kHz_r16__F1 x <= 1) /\ MinTimeGap_r16__scs_15kHz_r16__F2 (MinTimeGap_r16__scs_15kHz_r16__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGap_r16__scs_15kHz_r16__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGap_r16__scs_15kHz_r16__F1 (MinTimeGap_r16__scs_15kHz_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MinTimeGap_r16__scs_30kHz_r16__Type : Set :=
 | MinTimeGap_r16__scs_30kHz_r16__sl1
 | MinTimeGap_r16__scs_30kHz_r16__sl6
.
Definition MinTimeGap_r16__scs_30kHz_r16__cond := (fun (_ : MinTimeGap_r16__scs_30kHz_r16__Type) => True).
Lemma MinTimeGap_r16__scs_30kHz_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGap_r16__scs_30kHz_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGap_r16__scs_30kHz_r16__nat__helper.

Definition MinTimeGap_r16__scs_30kHz_r16__F1 t :=
  match t with
  | MinTimeGap_r16__scs_30kHz_r16__sl1 => 0
  | MinTimeGap_r16__scs_30kHz_r16__sl6 => 1
  end.
Definition MinTimeGap_r16__scs_30kHz_r16__F2 n :=
  match n with
  | 0 => MinTimeGap_r16__scs_30kHz_r16__sl1
  | 1 => MinTimeGap_r16__scs_30kHz_r16__sl6
  | _ => MinTimeGap_r16__scs_30kHz_r16__sl1
  end.
Lemma MinTimeGap_r16__scs_30kHz_r16__F1F2 : forall x : MinTimeGap_r16__scs_30kHz_r16__Type, (MinTimeGap_r16__scs_30kHz_r16__F1 x <= 1) /\ MinTimeGap_r16__scs_30kHz_r16__F2 (MinTimeGap_r16__scs_30kHz_r16__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGap_r16__scs_30kHz_r16__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGap_r16__scs_30kHz_r16__F1 (MinTimeGap_r16__scs_30kHz_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MinTimeGap_r16__scs_60kHz_r16__Type : Set :=
 | MinTimeGap_r16__scs_60kHz_r16__sl1
 | MinTimeGap_r16__scs_60kHz_r16__sl12
.
Definition MinTimeGap_r16__scs_60kHz_r16__cond := (fun (_ : MinTimeGap_r16__scs_60kHz_r16__Type) => True).
Lemma MinTimeGap_r16__scs_60kHz_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGap_r16__scs_60kHz_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGap_r16__scs_60kHz_r16__nat__helper.

Definition MinTimeGap_r16__scs_60kHz_r16__F1 t :=
  match t with
  | MinTimeGap_r16__scs_60kHz_r16__sl1 => 0
  | MinTimeGap_r16__scs_60kHz_r16__sl12 => 1
  end.
Definition MinTimeGap_r16__scs_60kHz_r16__F2 n :=
  match n with
  | 0 => MinTimeGap_r16__scs_60kHz_r16__sl1
  | 1 => MinTimeGap_r16__scs_60kHz_r16__sl12
  | _ => MinTimeGap_r16__scs_60kHz_r16__sl1
  end.
Lemma MinTimeGap_r16__scs_60kHz_r16__F1F2 : forall x : MinTimeGap_r16__scs_60kHz_r16__Type, (MinTimeGap_r16__scs_60kHz_r16__F1 x <= 1) /\ MinTimeGap_r16__scs_60kHz_r16__F2 (MinTimeGap_r16__scs_60kHz_r16__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGap_r16__scs_60kHz_r16__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGap_r16__scs_60kHz_r16__F1 (MinTimeGap_r16__scs_60kHz_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MinTimeGap_r16__scs_120kHz_r16__Type : Set :=
 | MinTimeGap_r16__scs_120kHz_r16__sl2
 | MinTimeGap_r16__scs_120kHz_r16__sl24
.
Definition MinTimeGap_r16__scs_120kHz_r16__cond := (fun (_ : MinTimeGap_r16__scs_120kHz_r16__Type) => True).
Lemma MinTimeGap_r16__scs_120kHz_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MinTimeGap_r16__scs_120kHz_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MinTimeGap_r16__scs_120kHz_r16__nat__helper.

Definition MinTimeGap_r16__scs_120kHz_r16__F1 t :=
  match t with
  | MinTimeGap_r16__scs_120kHz_r16__sl2 => 0
  | MinTimeGap_r16__scs_120kHz_r16__sl24 => 1
  end.
Definition MinTimeGap_r16__scs_120kHz_r16__F2 n :=
  match n with
  | 0 => MinTimeGap_r16__scs_120kHz_r16__sl2
  | 1 => MinTimeGap_r16__scs_120kHz_r16__sl24
  | _ => MinTimeGap_r16__scs_120kHz_r16__sl2
  end.
Lemma MinTimeGap_r16__scs_120kHz_r16__F1F2 : forall x : MinTimeGap_r16__scs_120kHz_r16__Type, (MinTimeGap_r16__scs_120kHz_r16__F1 x <= 1) /\ MinTimeGap_r16__scs_120kHz_r16__F2 (MinTimeGap_r16__scs_120kHz_r16__F1 x) = x. imp_solve. Qed.
Lemma MinTimeGap_r16__scs_120kHz_r16__F2F1 : forall (y : nat) (H : y <= 1), MinTimeGap_r16__scs_120kHz_r16__F1 (MinTimeGap_r16__scs_120kHz_r16__F2 y) = y. enum_solve H y. Qed.

Record MinTimeGap_r16__Type : Set :=
  make__MinTimeGap_r16__Type {
    MinTimeGap_r16__scs_15kHz_r16 : option MinTimeGap_r16__scs_15kHz_r16__Type ;
    MinTimeGap_r16__scs_30kHz_r16 : option MinTimeGap_r16__scs_30kHz_r16__Type ;
    MinTimeGap_r16__scs_60kHz_r16 : option MinTimeGap_r16__scs_60kHz_r16__Type ;
    MinTimeGap_r16__scs_120kHz_r16 : option MinTimeGap_r16__scs_120kHz_r16__Type ;
}.
Definition MinTimeGap_r16__list := (
 Opt MinTimeGap_r16__scs_15kHz_r16__Type MinTimeGap_r16__scs_15kHz_r16__cond ::
 Opt MinTimeGap_r16__scs_30kHz_r16__Type MinTimeGap_r16__scs_30kHz_r16__cond ::
 Opt MinTimeGap_r16__scs_60kHz_r16__Type MinTimeGap_r16__scs_60kHz_r16__cond ::
 Opt MinTimeGap_r16__scs_120kHz_r16__Type MinTimeGap_r16__scs_120kHz_r16__cond ::
 nil).
Definition MinTimeGap_r16__cond z := 
  opt_cond MinTimeGap_r16__scs_15kHz_r16__cond (MinTimeGap_r16__scs_15kHz_r16 z) /\
  opt_cond MinTimeGap_r16__scs_30kHz_r16__cond (MinTimeGap_r16__scs_30kHz_r16 z) /\
  opt_cond MinTimeGap_r16__scs_60kHz_r16__cond (MinTimeGap_r16__scs_60kHz_r16 z) /\
  opt_cond MinTimeGap_r16__scs_120kHz_r16__cond (MinTimeGap_r16__scs_120kHz_r16 z) /\
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
Definition MinTimeGap_r16__scs_15kHz_r16__Format : T_Format MinTimeGap_r16__scs_15kHz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGap_r16__scs_15kHz_r16__nat__Format MinTimeGap_r16__scs_15kHz_r16__F1 MinTimeGap_r16__scs_15kHz_r16__F2 MinTimeGap_r16__scs_15kHz_r16__F1F2 MinTimeGap_r16__scs_15kHz_r16__F2F1.

Opaque MinTimeGap_r16__scs_15kHz_r16__cond MinTimeGap_r16__scs_15kHz_r16__Format.

Definition MinTimeGap_r16__scs_30kHz_r16__Format : T_Format MinTimeGap_r16__scs_30kHz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGap_r16__scs_30kHz_r16__nat__Format MinTimeGap_r16__scs_30kHz_r16__F1 MinTimeGap_r16__scs_30kHz_r16__F2 MinTimeGap_r16__scs_30kHz_r16__F1F2 MinTimeGap_r16__scs_30kHz_r16__F2F1.

Opaque MinTimeGap_r16__scs_30kHz_r16__cond MinTimeGap_r16__scs_30kHz_r16__Format.

Definition MinTimeGap_r16__scs_60kHz_r16__Format : T_Format MinTimeGap_r16__scs_60kHz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGap_r16__scs_60kHz_r16__nat__Format MinTimeGap_r16__scs_60kHz_r16__F1 MinTimeGap_r16__scs_60kHz_r16__F2 MinTimeGap_r16__scs_60kHz_r16__F1F2 MinTimeGap_r16__scs_60kHz_r16__F2F1.

Opaque MinTimeGap_r16__scs_60kHz_r16__cond MinTimeGap_r16__scs_60kHz_r16__Format.

Definition MinTimeGap_r16__scs_120kHz_r16__Format : T_Format MinTimeGap_r16__scs_120kHz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MinTimeGap_r16__scs_120kHz_r16__nat__Format MinTimeGap_r16__scs_120kHz_r16__F1 MinTimeGap_r16__scs_120kHz_r16__F2 MinTimeGap_r16__scs_120kHz_r16__F1F2 MinTimeGap_r16__scs_120kHz_r16__F2F1.

Opaque MinTimeGap_r16__scs_120kHz_r16__cond MinTimeGap_r16__scs_120kHz_r16__Format.


Definition MinTimeGap_r16__Format_Type := Eval cbn in seq_format_prod MinTimeGap_r16__list.
Definition MinTimeGap_r16__Format_list : MinTimeGap_r16__Format_Type :=
  (MinTimeGap_r16__scs_15kHz_r16__Format, (MinTimeGap_r16__scs_30kHz_r16__Format, (MinTimeGap_r16__scs_60kHz_r16__Format, (MinTimeGap_r16__scs_120kHz_r16__Format, unit_format)))).
Definition MinTimeGap_r16__list__Format := (*Eval compute in *) seq_format MinTimeGap_r16__list MinTimeGap_r16__Format_list.
Definition MinTimeGap_r16__F1 z :=
  (MinTimeGap_r16__scs_15kHz_r16 z, (MinTimeGap_r16__scs_30kHz_r16 z, (MinTimeGap_r16__scs_60kHz_r16 z, (MinTimeGap_r16__scs_120kHz_r16 z, tt)))).
Definition MinTimeGap_r16__F2 (y : seq_type MinTimeGap_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MinTimeGap_r16__Type i0 i1 i2 i3
  end.
Lemma MinTimeGap_r16__F1F2_cond (z : MinTimeGap_r16__Type)
  : MinTimeGap_r16__cond z ->
  (seq_cond MinTimeGap_r16__list (MinTimeGap_r16__F1 z)).
intro H. unfold MinTimeGap_r16__cond in H. simpl. auto. Qed.
Lemma MinTimeGap_r16__F1F2_cond2 (z : MinTimeGap_r16__Type)
 : MinTimeGap_r16__F2 (MinTimeGap_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MinTimeGap_r16__F2F1_cond (y : seq_type MinTimeGap_r16__list)
  : seq_cond MinTimeGap_r16__list y ->
 (MinTimeGap_r16__cond (MinTimeGap_r16__F2 y)) /\  MinTimeGap_r16__F1 (MinTimeGap_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MinTimeGap_r16__cond. simpl in *. auto.
 - simpl. unfold MinTimeGap_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MinTimeGap_r16__Format : T_Format MinTimeGap_r16__Type MinTimeGap_r16__cond :=
        proj2_format  MinTimeGap_r16__cond MinTimeGap_r16__list__Format
    MinTimeGap_r16__F1 MinTimeGap_r16__F2 MinTimeGap_r16__F1F2_cond  MinTimeGap_r16__F1F2_cond2 MinTimeGap_r16__F2F1_cond.
Opaque MinTimeGap_r16__cond MinTimeGap_r16__Format.

