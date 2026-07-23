Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SRS_SwitchingTimeEUTRA__switchingTimeDL__Type : Set :=
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n0
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n0dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n1
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n1dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n2
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n2dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n3
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n3dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n4
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n4dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n5dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n6
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n6dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeDL__n7
.
Definition SRS_SwitchingTimeEUTRA__switchingTimeDL__cond := (fun (_ : SRS_SwitchingTimeEUTRA__switchingTimeDL__Type) => True).
Lemma SRS_SwitchingTimeEUTRA__switchingTimeDL__nat__helper : to_bit_sz 14 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_SwitchingTimeEUTRA__switchingTimeDL__nat__Format : T_Format nat (fun z => (z <= 14)) :=
  nat_enum_format 14 SRS_SwitchingTimeEUTRA__switchingTimeDL__nat__helper.

Definition SRS_SwitchingTimeEUTRA__switchingTimeDL__F1 t :=
  match t with
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n0 => 0
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n0dot5 => 1
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n1 => 2
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n1dot5 => 3
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n2 => 4
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n2dot5 => 5
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n3 => 6
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n3dot5 => 7
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n4 => 8
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n4dot5 => 9
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n5 => 10
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n5dot5 => 11
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n6 => 12
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n6dot5 => 13
  | SRS_SwitchingTimeEUTRA__switchingTimeDL__n7 => 14
  end.
Definition SRS_SwitchingTimeEUTRA__switchingTimeDL__F2 n :=
  match n with
  | 0 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n0
  | 1 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n0dot5
  | 2 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n1
  | 3 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n1dot5
  | 4 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n2
  | 5 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n2dot5
  | 6 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n3
  | 7 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n3dot5
  | 8 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n4
  | 9 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n4dot5
  | 10 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n5
  | 11 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n5dot5
  | 12 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n6
  | 13 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n6dot5
  | 14 => SRS_SwitchingTimeEUTRA__switchingTimeDL__n7
  | _ => SRS_SwitchingTimeEUTRA__switchingTimeDL__n0
  end.
Lemma SRS_SwitchingTimeEUTRA__switchingTimeDL__F1F2 : forall x : SRS_SwitchingTimeEUTRA__switchingTimeDL__Type, (SRS_SwitchingTimeEUTRA__switchingTimeDL__F1 x <= 14) /\ SRS_SwitchingTimeEUTRA__switchingTimeDL__F2 (SRS_SwitchingTimeEUTRA__switchingTimeDL__F1 x) = x. imp_solve. Qed.
Lemma SRS_SwitchingTimeEUTRA__switchingTimeDL__F2F1 : forall (y : nat) (H : y <= 14), SRS_SwitchingTimeEUTRA__switchingTimeDL__F1 (SRS_SwitchingTimeEUTRA__switchingTimeDL__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_SwitchingTimeEUTRA__switchingTimeUL__Type : Set :=
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n0
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n0dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n1
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n1dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n2
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n2dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n3
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n3dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n4
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n4dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n5dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n6
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n6dot5
 | SRS_SwitchingTimeEUTRA__switchingTimeUL__n7
.
Definition SRS_SwitchingTimeEUTRA__switchingTimeUL__cond := (fun (_ : SRS_SwitchingTimeEUTRA__switchingTimeUL__Type) => True).
Lemma SRS_SwitchingTimeEUTRA__switchingTimeUL__nat__helper : to_bit_sz 14 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_SwitchingTimeEUTRA__switchingTimeUL__nat__Format : T_Format nat (fun z => (z <= 14)) :=
  nat_enum_format 14 SRS_SwitchingTimeEUTRA__switchingTimeUL__nat__helper.

Definition SRS_SwitchingTimeEUTRA__switchingTimeUL__F1 t :=
  match t with
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n0 => 0
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n0dot5 => 1
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n1 => 2
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n1dot5 => 3
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n2 => 4
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n2dot5 => 5
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n3 => 6
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n3dot5 => 7
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n4 => 8
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n4dot5 => 9
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n5 => 10
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n5dot5 => 11
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n6 => 12
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n6dot5 => 13
  | SRS_SwitchingTimeEUTRA__switchingTimeUL__n7 => 14
  end.
Definition SRS_SwitchingTimeEUTRA__switchingTimeUL__F2 n :=
  match n with
  | 0 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n0
  | 1 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n0dot5
  | 2 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n1
  | 3 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n1dot5
  | 4 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n2
  | 5 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n2dot5
  | 6 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n3
  | 7 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n3dot5
  | 8 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n4
  | 9 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n4dot5
  | 10 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n5
  | 11 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n5dot5
  | 12 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n6
  | 13 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n6dot5
  | 14 => SRS_SwitchingTimeEUTRA__switchingTimeUL__n7
  | _ => SRS_SwitchingTimeEUTRA__switchingTimeUL__n0
  end.
Lemma SRS_SwitchingTimeEUTRA__switchingTimeUL__F1F2 : forall x : SRS_SwitchingTimeEUTRA__switchingTimeUL__Type, (SRS_SwitchingTimeEUTRA__switchingTimeUL__F1 x <= 14) /\ SRS_SwitchingTimeEUTRA__switchingTimeUL__F2 (SRS_SwitchingTimeEUTRA__switchingTimeUL__F1 x) = x. imp_solve. Qed.
Lemma SRS_SwitchingTimeEUTRA__switchingTimeUL__F2F1 : forall (y : nat) (H : y <= 14), SRS_SwitchingTimeEUTRA__switchingTimeUL__F1 (SRS_SwitchingTimeEUTRA__switchingTimeUL__F2 y) = y. enum_solve H y. Qed.

Record SRS_SwitchingTimeEUTRA__Type : Set :=
  make__SRS_SwitchingTimeEUTRA__Type {
    SRS_SwitchingTimeEUTRA__switchingTimeDL : option SRS_SwitchingTimeEUTRA__switchingTimeDL__Type ;
    SRS_SwitchingTimeEUTRA__switchingTimeUL : option SRS_SwitchingTimeEUTRA__switchingTimeUL__Type ;
}.
Definition SRS_SwitchingTimeEUTRA__list := (
 Opt SRS_SwitchingTimeEUTRA__switchingTimeDL__Type SRS_SwitchingTimeEUTRA__switchingTimeDL__cond ::
 Opt SRS_SwitchingTimeEUTRA__switchingTimeUL__Type SRS_SwitchingTimeEUTRA__switchingTimeUL__cond ::
 nil).
Definition SRS_SwitchingTimeEUTRA__cond z := 
  opt_cond SRS_SwitchingTimeEUTRA__switchingTimeDL__cond (SRS_SwitchingTimeEUTRA__switchingTimeDL z) /\
  opt_cond SRS_SwitchingTimeEUTRA__switchingTimeUL__cond (SRS_SwitchingTimeEUTRA__switchingTimeUL z) /\
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
Definition SRS_SwitchingTimeEUTRA__switchingTimeDL__Format : T_Format SRS_SwitchingTimeEUTRA__switchingTimeDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_SwitchingTimeEUTRA__switchingTimeDL__nat__Format SRS_SwitchingTimeEUTRA__switchingTimeDL__F1 SRS_SwitchingTimeEUTRA__switchingTimeDL__F2 SRS_SwitchingTimeEUTRA__switchingTimeDL__F1F2 SRS_SwitchingTimeEUTRA__switchingTimeDL__F2F1.

Opaque SRS_SwitchingTimeEUTRA__switchingTimeDL__cond SRS_SwitchingTimeEUTRA__switchingTimeDL__Format.

Definition SRS_SwitchingTimeEUTRA__switchingTimeUL__Format : T_Format SRS_SwitchingTimeEUTRA__switchingTimeUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_SwitchingTimeEUTRA__switchingTimeUL__nat__Format SRS_SwitchingTimeEUTRA__switchingTimeUL__F1 SRS_SwitchingTimeEUTRA__switchingTimeUL__F2 SRS_SwitchingTimeEUTRA__switchingTimeUL__F1F2 SRS_SwitchingTimeEUTRA__switchingTimeUL__F2F1.

Opaque SRS_SwitchingTimeEUTRA__switchingTimeUL__cond SRS_SwitchingTimeEUTRA__switchingTimeUL__Format.


Definition SRS_SwitchingTimeEUTRA__Format_Type := Eval cbn in seq_format_prod SRS_SwitchingTimeEUTRA__list.
Definition SRS_SwitchingTimeEUTRA__Format_list : SRS_SwitchingTimeEUTRA__Format_Type :=
  (SRS_SwitchingTimeEUTRA__switchingTimeDL__Format, (SRS_SwitchingTimeEUTRA__switchingTimeUL__Format, unit_format)).
Definition SRS_SwitchingTimeEUTRA__list__Format := (*Eval compute in *) seq_format SRS_SwitchingTimeEUTRA__list SRS_SwitchingTimeEUTRA__Format_list.
Definition SRS_SwitchingTimeEUTRA__F1 z :=
  (SRS_SwitchingTimeEUTRA__switchingTimeDL z, (SRS_SwitchingTimeEUTRA__switchingTimeUL z, tt)).
Definition SRS_SwitchingTimeEUTRA__F2 (y : seq_type SRS_SwitchingTimeEUTRA__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_SwitchingTimeEUTRA__Type i0 i1
  end.
Lemma SRS_SwitchingTimeEUTRA__F1F2_cond (z : SRS_SwitchingTimeEUTRA__Type)
  : SRS_SwitchingTimeEUTRA__cond z ->
  (seq_cond SRS_SwitchingTimeEUTRA__list (SRS_SwitchingTimeEUTRA__F1 z)).
intro H. unfold SRS_SwitchingTimeEUTRA__cond in H. simpl. auto. Qed.
Lemma SRS_SwitchingTimeEUTRA__F1F2_cond2 (z : SRS_SwitchingTimeEUTRA__Type)
 : SRS_SwitchingTimeEUTRA__F2 (SRS_SwitchingTimeEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_SwitchingTimeEUTRA__F2F1_cond (y : seq_type SRS_SwitchingTimeEUTRA__list)
  : seq_cond SRS_SwitchingTimeEUTRA__list y ->
 (SRS_SwitchingTimeEUTRA__cond (SRS_SwitchingTimeEUTRA__F2 y)) /\  SRS_SwitchingTimeEUTRA__F1 (SRS_SwitchingTimeEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_SwitchingTimeEUTRA__cond. simpl in *. auto.
 - simpl. unfold SRS_SwitchingTimeEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_SwitchingTimeEUTRA__Format : T_Format SRS_SwitchingTimeEUTRA__Type SRS_SwitchingTimeEUTRA__cond :=
        proj2_format  SRS_SwitchingTimeEUTRA__cond SRS_SwitchingTimeEUTRA__list__Format
    SRS_SwitchingTimeEUTRA__F1 SRS_SwitchingTimeEUTRA__F2 SRS_SwitchingTimeEUTRA__F1F2_cond  SRS_SwitchingTimeEUTRA__F1F2_cond2 SRS_SwitchingTimeEUTRA__F2F1_cond.
Opaque SRS_SwitchingTimeEUTRA__cond SRS_SwitchingTimeEUTRA__Format.

