Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SRS_SwitchingTimeNR__switchingTimeDL__Type : Set :=
 | SRS_SwitchingTimeNR__switchingTimeDL__n0us
 | SRS_SwitchingTimeNR__switchingTimeDL__n30us
 | SRS_SwitchingTimeNR__switchingTimeDL__n100us
 | SRS_SwitchingTimeNR__switchingTimeDL__n140us
 | SRS_SwitchingTimeNR__switchingTimeDL__n200us
 | SRS_SwitchingTimeNR__switchingTimeDL__n300us
 | SRS_SwitchingTimeNR__switchingTimeDL__n500us
 | SRS_SwitchingTimeNR__switchingTimeDL__n900us
.
Definition SRS_SwitchingTimeNR__switchingTimeDL__cond := (fun (_ : SRS_SwitchingTimeNR__switchingTimeDL__Type) => True).
Lemma SRS_SwitchingTimeNR__switchingTimeDL__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_SwitchingTimeNR__switchingTimeDL__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SRS_SwitchingTimeNR__switchingTimeDL__nat__helper.

Definition SRS_SwitchingTimeNR__switchingTimeDL__F1 t :=
  match t with
  | SRS_SwitchingTimeNR__switchingTimeDL__n0us => 0
  | SRS_SwitchingTimeNR__switchingTimeDL__n30us => 1
  | SRS_SwitchingTimeNR__switchingTimeDL__n100us => 2
  | SRS_SwitchingTimeNR__switchingTimeDL__n140us => 3
  | SRS_SwitchingTimeNR__switchingTimeDL__n200us => 4
  | SRS_SwitchingTimeNR__switchingTimeDL__n300us => 5
  | SRS_SwitchingTimeNR__switchingTimeDL__n500us => 6
  | SRS_SwitchingTimeNR__switchingTimeDL__n900us => 7
  end.
Definition SRS_SwitchingTimeNR__switchingTimeDL__F2 n :=
  match n with
  | 0 => SRS_SwitchingTimeNR__switchingTimeDL__n0us
  | 1 => SRS_SwitchingTimeNR__switchingTimeDL__n30us
  | 2 => SRS_SwitchingTimeNR__switchingTimeDL__n100us
  | 3 => SRS_SwitchingTimeNR__switchingTimeDL__n140us
  | 4 => SRS_SwitchingTimeNR__switchingTimeDL__n200us
  | 5 => SRS_SwitchingTimeNR__switchingTimeDL__n300us
  | 6 => SRS_SwitchingTimeNR__switchingTimeDL__n500us
  | 7 => SRS_SwitchingTimeNR__switchingTimeDL__n900us
  | _ => SRS_SwitchingTimeNR__switchingTimeDL__n0us
  end.
Lemma SRS_SwitchingTimeNR__switchingTimeDL__F1F2 : forall x : SRS_SwitchingTimeNR__switchingTimeDL__Type, (SRS_SwitchingTimeNR__switchingTimeDL__F1 x <= 7) /\ SRS_SwitchingTimeNR__switchingTimeDL__F2 (SRS_SwitchingTimeNR__switchingTimeDL__F1 x) = x. imp_solve. Qed.
Lemma SRS_SwitchingTimeNR__switchingTimeDL__F2F1 : forall (y : nat) (H : y <= 7), SRS_SwitchingTimeNR__switchingTimeDL__F1 (SRS_SwitchingTimeNR__switchingTimeDL__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_SwitchingTimeNR__switchingTimeUL__Type : Set :=
 | SRS_SwitchingTimeNR__switchingTimeUL__n0us
 | SRS_SwitchingTimeNR__switchingTimeUL__n30us
 | SRS_SwitchingTimeNR__switchingTimeUL__n100us
 | SRS_SwitchingTimeNR__switchingTimeUL__n140us
 | SRS_SwitchingTimeNR__switchingTimeUL__n200us
 | SRS_SwitchingTimeNR__switchingTimeUL__n300us
 | SRS_SwitchingTimeNR__switchingTimeUL__n500us
 | SRS_SwitchingTimeNR__switchingTimeUL__n900us
.
Definition SRS_SwitchingTimeNR__switchingTimeUL__cond := (fun (_ : SRS_SwitchingTimeNR__switchingTimeUL__Type) => True).
Lemma SRS_SwitchingTimeNR__switchingTimeUL__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_SwitchingTimeNR__switchingTimeUL__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SRS_SwitchingTimeNR__switchingTimeUL__nat__helper.

Definition SRS_SwitchingTimeNR__switchingTimeUL__F1 t :=
  match t with
  | SRS_SwitchingTimeNR__switchingTimeUL__n0us => 0
  | SRS_SwitchingTimeNR__switchingTimeUL__n30us => 1
  | SRS_SwitchingTimeNR__switchingTimeUL__n100us => 2
  | SRS_SwitchingTimeNR__switchingTimeUL__n140us => 3
  | SRS_SwitchingTimeNR__switchingTimeUL__n200us => 4
  | SRS_SwitchingTimeNR__switchingTimeUL__n300us => 5
  | SRS_SwitchingTimeNR__switchingTimeUL__n500us => 6
  | SRS_SwitchingTimeNR__switchingTimeUL__n900us => 7
  end.
Definition SRS_SwitchingTimeNR__switchingTimeUL__F2 n :=
  match n with
  | 0 => SRS_SwitchingTimeNR__switchingTimeUL__n0us
  | 1 => SRS_SwitchingTimeNR__switchingTimeUL__n30us
  | 2 => SRS_SwitchingTimeNR__switchingTimeUL__n100us
  | 3 => SRS_SwitchingTimeNR__switchingTimeUL__n140us
  | 4 => SRS_SwitchingTimeNR__switchingTimeUL__n200us
  | 5 => SRS_SwitchingTimeNR__switchingTimeUL__n300us
  | 6 => SRS_SwitchingTimeNR__switchingTimeUL__n500us
  | 7 => SRS_SwitchingTimeNR__switchingTimeUL__n900us
  | _ => SRS_SwitchingTimeNR__switchingTimeUL__n0us
  end.
Lemma SRS_SwitchingTimeNR__switchingTimeUL__F1F2 : forall x : SRS_SwitchingTimeNR__switchingTimeUL__Type, (SRS_SwitchingTimeNR__switchingTimeUL__F1 x <= 7) /\ SRS_SwitchingTimeNR__switchingTimeUL__F2 (SRS_SwitchingTimeNR__switchingTimeUL__F1 x) = x. imp_solve. Qed.
Lemma SRS_SwitchingTimeNR__switchingTimeUL__F2F1 : forall (y : nat) (H : y <= 7), SRS_SwitchingTimeNR__switchingTimeUL__F1 (SRS_SwitchingTimeNR__switchingTimeUL__F2 y) = y. enum_solve H y. Qed.

Record SRS_SwitchingTimeNR__Type : Set :=
  make__SRS_SwitchingTimeNR__Type {
    SRS_SwitchingTimeNR__switchingTimeDL : option SRS_SwitchingTimeNR__switchingTimeDL__Type ;
    SRS_SwitchingTimeNR__switchingTimeUL : option SRS_SwitchingTimeNR__switchingTimeUL__Type ;
}.
Definition SRS_SwitchingTimeNR__list := (
 Opt SRS_SwitchingTimeNR__switchingTimeDL__Type SRS_SwitchingTimeNR__switchingTimeDL__cond ::
 Opt SRS_SwitchingTimeNR__switchingTimeUL__Type SRS_SwitchingTimeNR__switchingTimeUL__cond ::
 nil).
Definition SRS_SwitchingTimeNR__cond z := 
  opt_cond SRS_SwitchingTimeNR__switchingTimeDL__cond (SRS_SwitchingTimeNR__switchingTimeDL z) /\
  opt_cond SRS_SwitchingTimeNR__switchingTimeUL__cond (SRS_SwitchingTimeNR__switchingTimeUL z) /\
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
Definition SRS_SwitchingTimeNR__switchingTimeDL__Format : T_Format SRS_SwitchingTimeNR__switchingTimeDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_SwitchingTimeNR__switchingTimeDL__nat__Format SRS_SwitchingTimeNR__switchingTimeDL__F1 SRS_SwitchingTimeNR__switchingTimeDL__F2 SRS_SwitchingTimeNR__switchingTimeDL__F1F2 SRS_SwitchingTimeNR__switchingTimeDL__F2F1.

Opaque SRS_SwitchingTimeNR__switchingTimeDL__cond SRS_SwitchingTimeNR__switchingTimeDL__Format.

Definition SRS_SwitchingTimeNR__switchingTimeUL__Format : T_Format SRS_SwitchingTimeNR__switchingTimeUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_SwitchingTimeNR__switchingTimeUL__nat__Format SRS_SwitchingTimeNR__switchingTimeUL__F1 SRS_SwitchingTimeNR__switchingTimeUL__F2 SRS_SwitchingTimeNR__switchingTimeUL__F1F2 SRS_SwitchingTimeNR__switchingTimeUL__F2F1.

Opaque SRS_SwitchingTimeNR__switchingTimeUL__cond SRS_SwitchingTimeNR__switchingTimeUL__Format.


Definition SRS_SwitchingTimeNR__Format_Type := Eval cbn in seq_format_prod SRS_SwitchingTimeNR__list.
Definition SRS_SwitchingTimeNR__Format_list : SRS_SwitchingTimeNR__Format_Type :=
  (SRS_SwitchingTimeNR__switchingTimeDL__Format, (SRS_SwitchingTimeNR__switchingTimeUL__Format, unit_format)).
Definition SRS_SwitchingTimeNR__list__Format := (*Eval compute in *) seq_format SRS_SwitchingTimeNR__list SRS_SwitchingTimeNR__Format_list.
Definition SRS_SwitchingTimeNR__F1 z :=
  (SRS_SwitchingTimeNR__switchingTimeDL z, (SRS_SwitchingTimeNR__switchingTimeUL z, tt)).
Definition SRS_SwitchingTimeNR__F2 (y : seq_type SRS_SwitchingTimeNR__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_SwitchingTimeNR__Type i0 i1
  end.
Lemma SRS_SwitchingTimeNR__F1F2_cond (z : SRS_SwitchingTimeNR__Type)
  : SRS_SwitchingTimeNR__cond z ->
  (seq_cond SRS_SwitchingTimeNR__list (SRS_SwitchingTimeNR__F1 z)).
intro H. unfold SRS_SwitchingTimeNR__cond in H. simpl. auto. Qed.
Lemma SRS_SwitchingTimeNR__F1F2_cond2 (z : SRS_SwitchingTimeNR__Type)
 : SRS_SwitchingTimeNR__F2 (SRS_SwitchingTimeNR__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_SwitchingTimeNR__F2F1_cond (y : seq_type SRS_SwitchingTimeNR__list)
  : seq_cond SRS_SwitchingTimeNR__list y ->
 (SRS_SwitchingTimeNR__cond (SRS_SwitchingTimeNR__F2 y)) /\  SRS_SwitchingTimeNR__F1 (SRS_SwitchingTimeNR__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_SwitchingTimeNR__cond. simpl in *. auto.
 - simpl. unfold SRS_SwitchingTimeNR__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_SwitchingTimeNR__Format : T_Format SRS_SwitchingTimeNR__Type SRS_SwitchingTimeNR__cond :=
        proj2_format  SRS_SwitchingTimeNR__cond SRS_SwitchingTimeNR__list__Format
    SRS_SwitchingTimeNR__F1 SRS_SwitchingTimeNR__F2 SRS_SwitchingTimeNR__F1F2_cond  SRS_SwitchingTimeNR__F1F2_cond2 SRS_SwitchingTimeNR__F2F1_cond.
Opaque SRS_SwitchingTimeNR__cond SRS_SwitchingTimeNR__Format.

