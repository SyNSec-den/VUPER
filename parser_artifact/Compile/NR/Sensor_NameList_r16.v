Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Sensor_NameList_r16__measUncomBarPre_r16__Type : Set :=
 | Sensor_NameList_r16__measUncomBarPre_r16__true
.
Definition Sensor_NameList_r16__measUncomBarPre_r16__cond := (fun (_ : Sensor_NameList_r16__measUncomBarPre_r16__Type) => True).
Lemma Sensor_NameList_r16__measUncomBarPre_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Sensor_NameList_r16__measUncomBarPre_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Sensor_NameList_r16__measUncomBarPre_r16__nat__helper.

Definition Sensor_NameList_r16__measUncomBarPre_r16__F1 t :=
  match t with
  | Sensor_NameList_r16__measUncomBarPre_r16__true => 0
  end.
Definition Sensor_NameList_r16__measUncomBarPre_r16__F2 n :=
  match n with
  | 0 => Sensor_NameList_r16__measUncomBarPre_r16__true
  | _ => Sensor_NameList_r16__measUncomBarPre_r16__true
  end.
Lemma Sensor_NameList_r16__measUncomBarPre_r16__F1F2 : forall x : Sensor_NameList_r16__measUncomBarPre_r16__Type, (Sensor_NameList_r16__measUncomBarPre_r16__F1 x <= 0) /\ Sensor_NameList_r16__measUncomBarPre_r16__F2 (Sensor_NameList_r16__measUncomBarPre_r16__F1 x) = x. imp_solve. Qed.
Lemma Sensor_NameList_r16__measUncomBarPre_r16__F2F1 : forall (y : nat) (H : y <= 0), Sensor_NameList_r16__measUncomBarPre_r16__F1 (Sensor_NameList_r16__measUncomBarPre_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Sensor_NameList_r16__measUeSpeed__Type : Set :=
 | Sensor_NameList_r16__measUeSpeed__true
.
Definition Sensor_NameList_r16__measUeSpeed__cond := (fun (_ : Sensor_NameList_r16__measUeSpeed__Type) => True).
Lemma Sensor_NameList_r16__measUeSpeed__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Sensor_NameList_r16__measUeSpeed__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Sensor_NameList_r16__measUeSpeed__nat__helper.

Definition Sensor_NameList_r16__measUeSpeed__F1 t :=
  match t with
  | Sensor_NameList_r16__measUeSpeed__true => 0
  end.
Definition Sensor_NameList_r16__measUeSpeed__F2 n :=
  match n with
  | 0 => Sensor_NameList_r16__measUeSpeed__true
  | _ => Sensor_NameList_r16__measUeSpeed__true
  end.
Lemma Sensor_NameList_r16__measUeSpeed__F1F2 : forall x : Sensor_NameList_r16__measUeSpeed__Type, (Sensor_NameList_r16__measUeSpeed__F1 x <= 0) /\ Sensor_NameList_r16__measUeSpeed__F2 (Sensor_NameList_r16__measUeSpeed__F1 x) = x. imp_solve. Qed.
Lemma Sensor_NameList_r16__measUeSpeed__F2F1 : forall (y : nat) (H : y <= 0), Sensor_NameList_r16__measUeSpeed__F1 (Sensor_NameList_r16__measUeSpeed__F2 y) = y. enum_solve H y. Qed.

Inductive Sensor_NameList_r16__measUeOrientation__Type : Set :=
 | Sensor_NameList_r16__measUeOrientation__true
.
Definition Sensor_NameList_r16__measUeOrientation__cond := (fun (_ : Sensor_NameList_r16__measUeOrientation__Type) => True).
Lemma Sensor_NameList_r16__measUeOrientation__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Sensor_NameList_r16__measUeOrientation__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Sensor_NameList_r16__measUeOrientation__nat__helper.

Definition Sensor_NameList_r16__measUeOrientation__F1 t :=
  match t with
  | Sensor_NameList_r16__measUeOrientation__true => 0
  end.
Definition Sensor_NameList_r16__measUeOrientation__F2 n :=
  match n with
  | 0 => Sensor_NameList_r16__measUeOrientation__true
  | _ => Sensor_NameList_r16__measUeOrientation__true
  end.
Lemma Sensor_NameList_r16__measUeOrientation__F1F2 : forall x : Sensor_NameList_r16__measUeOrientation__Type, (Sensor_NameList_r16__measUeOrientation__F1 x <= 0) /\ Sensor_NameList_r16__measUeOrientation__F2 (Sensor_NameList_r16__measUeOrientation__F1 x) = x. imp_solve. Qed.
Lemma Sensor_NameList_r16__measUeOrientation__F2F1 : forall (y : nat) (H : y <= 0), Sensor_NameList_r16__measUeOrientation__F1 (Sensor_NameList_r16__measUeOrientation__F2 y) = y. enum_solve H y. Qed.

Record Sensor_NameList_r16__Type : Set :=
  make__Sensor_NameList_r16__Type {
    Sensor_NameList_r16__measUncomBarPre_r16 : option Sensor_NameList_r16__measUncomBarPre_r16__Type ;
    Sensor_NameList_r16__measUeSpeed : option Sensor_NameList_r16__measUeSpeed__Type ;
    Sensor_NameList_r16__measUeOrientation : option Sensor_NameList_r16__measUeOrientation__Type ;
}.
Definition Sensor_NameList_r16__list := (
 Opt Sensor_NameList_r16__measUncomBarPre_r16__Type Sensor_NameList_r16__measUncomBarPre_r16__cond ::
 Opt Sensor_NameList_r16__measUeSpeed__Type Sensor_NameList_r16__measUeSpeed__cond ::
 Opt Sensor_NameList_r16__measUeOrientation__Type Sensor_NameList_r16__measUeOrientation__cond ::
 nil).
Definition Sensor_NameList_r16__cond z := 
  opt_cond Sensor_NameList_r16__measUncomBarPre_r16__cond (Sensor_NameList_r16__measUncomBarPre_r16 z) /\
  opt_cond Sensor_NameList_r16__measUeSpeed__cond (Sensor_NameList_r16__measUeSpeed z) /\
  opt_cond Sensor_NameList_r16__measUeOrientation__cond (Sensor_NameList_r16__measUeOrientation z) /\
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
Definition Sensor_NameList_r16__measUncomBarPre_r16__Format : T_Format Sensor_NameList_r16__measUncomBarPre_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Sensor_NameList_r16__measUncomBarPre_r16__nat__Format Sensor_NameList_r16__measUncomBarPre_r16__F1 Sensor_NameList_r16__measUncomBarPre_r16__F2 Sensor_NameList_r16__measUncomBarPre_r16__F1F2 Sensor_NameList_r16__measUncomBarPre_r16__F2F1.

Opaque Sensor_NameList_r16__measUncomBarPre_r16__cond Sensor_NameList_r16__measUncomBarPre_r16__Format.

Definition Sensor_NameList_r16__measUeSpeed__Format : T_Format Sensor_NameList_r16__measUeSpeed__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Sensor_NameList_r16__measUeSpeed__nat__Format Sensor_NameList_r16__measUeSpeed__F1 Sensor_NameList_r16__measUeSpeed__F2 Sensor_NameList_r16__measUeSpeed__F1F2 Sensor_NameList_r16__measUeSpeed__F2F1.

Opaque Sensor_NameList_r16__measUeSpeed__cond Sensor_NameList_r16__measUeSpeed__Format.

Definition Sensor_NameList_r16__measUeOrientation__Format : T_Format Sensor_NameList_r16__measUeOrientation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Sensor_NameList_r16__measUeOrientation__nat__Format Sensor_NameList_r16__measUeOrientation__F1 Sensor_NameList_r16__measUeOrientation__F2 Sensor_NameList_r16__measUeOrientation__F1F2 Sensor_NameList_r16__measUeOrientation__F2F1.

Opaque Sensor_NameList_r16__measUeOrientation__cond Sensor_NameList_r16__measUeOrientation__Format.


Definition Sensor_NameList_r16__Format_Type := Eval cbn in seq_format_prod Sensor_NameList_r16__list.
Definition Sensor_NameList_r16__Format_list : Sensor_NameList_r16__Format_Type :=
  (Sensor_NameList_r16__measUncomBarPre_r16__Format, (Sensor_NameList_r16__measUeSpeed__Format, (Sensor_NameList_r16__measUeOrientation__Format, unit_format))).
Definition Sensor_NameList_r16__list__Format := (*Eval compute in *) seq_format Sensor_NameList_r16__list Sensor_NameList_r16__Format_list.
Definition Sensor_NameList_r16__F1 z :=
  (Sensor_NameList_r16__measUncomBarPre_r16 z, (Sensor_NameList_r16__measUeSpeed z, (Sensor_NameList_r16__measUeOrientation z, tt))).
Definition Sensor_NameList_r16__F2 (y : seq_type Sensor_NameList_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Sensor_NameList_r16__Type i0 i1 i2
  end.
Lemma Sensor_NameList_r16__F1F2_cond (z : Sensor_NameList_r16__Type)
  : Sensor_NameList_r16__cond z ->
  (seq_cond Sensor_NameList_r16__list (Sensor_NameList_r16__F1 z)).
intro H. unfold Sensor_NameList_r16__cond in H. simpl. auto. Qed.
Lemma Sensor_NameList_r16__F1F2_cond2 (z : Sensor_NameList_r16__Type)
 : Sensor_NameList_r16__F2 (Sensor_NameList_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Sensor_NameList_r16__F2F1_cond (y : seq_type Sensor_NameList_r16__list)
  : seq_cond Sensor_NameList_r16__list y ->
 (Sensor_NameList_r16__cond (Sensor_NameList_r16__F2 y)) /\  Sensor_NameList_r16__F1 (Sensor_NameList_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Sensor_NameList_r16__cond. simpl in *. auto.
 - simpl. unfold Sensor_NameList_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Sensor_NameList_r16__Format : T_Format Sensor_NameList_r16__Type Sensor_NameList_r16__cond :=
        proj2_format  Sensor_NameList_r16__cond Sensor_NameList_r16__list__Format
    Sensor_NameList_r16__F1 Sensor_NameList_r16__F2 Sensor_NameList_r16__F1F2_cond  Sensor_NameList_r16__F1F2_cond2 Sensor_NameList_r16__F2F1_cond.
Opaque Sensor_NameList_r16__cond Sensor_NameList_r16__Format.

