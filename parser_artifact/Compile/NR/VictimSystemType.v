Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Inductive VictimSystemType__gps__Type : Set :=
 | VictimSystemType__gps__true
.
Definition VictimSystemType__gps__cond := (fun (_ : VictimSystemType__gps__Type) => True).
Lemma VictimSystemType__gps__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VictimSystemType__gps__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VictimSystemType__gps__nat__helper.

Definition VictimSystemType__gps__F1 t :=
  match t with
  | VictimSystemType__gps__true => 0
  end.
Definition VictimSystemType__gps__F2 n :=
  match n with
  | 0 => VictimSystemType__gps__true
  | _ => VictimSystemType__gps__true
  end.
Lemma VictimSystemType__gps__F1F2 : forall x : VictimSystemType__gps__Type, (VictimSystemType__gps__F1 x <= 0) /\ VictimSystemType__gps__F2 (VictimSystemType__gps__F1 x) = x. imp_solve. Qed.
Lemma VictimSystemType__gps__F2F1 : forall (y : nat) (H : y <= 0), VictimSystemType__gps__F1 (VictimSystemType__gps__F2 y) = y. enum_solve H y. Qed.

Inductive VictimSystemType__glonass__Type : Set :=
 | VictimSystemType__glonass__true
.
Definition VictimSystemType__glonass__cond := (fun (_ : VictimSystemType__glonass__Type) => True).
Lemma VictimSystemType__glonass__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VictimSystemType__glonass__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VictimSystemType__glonass__nat__helper.

Definition VictimSystemType__glonass__F1 t :=
  match t with
  | VictimSystemType__glonass__true => 0
  end.
Definition VictimSystemType__glonass__F2 n :=
  match n with
  | 0 => VictimSystemType__glonass__true
  | _ => VictimSystemType__glonass__true
  end.
Lemma VictimSystemType__glonass__F1F2 : forall x : VictimSystemType__glonass__Type, (VictimSystemType__glonass__F1 x <= 0) /\ VictimSystemType__glonass__F2 (VictimSystemType__glonass__F1 x) = x. imp_solve. Qed.
Lemma VictimSystemType__glonass__F2F1 : forall (y : nat) (H : y <= 0), VictimSystemType__glonass__F1 (VictimSystemType__glonass__F2 y) = y. enum_solve H y. Qed.

Inductive VictimSystemType__bds__Type : Set :=
 | VictimSystemType__bds__true
.
Definition VictimSystemType__bds__cond := (fun (_ : VictimSystemType__bds__Type) => True).
Lemma VictimSystemType__bds__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VictimSystemType__bds__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VictimSystemType__bds__nat__helper.

Definition VictimSystemType__bds__F1 t :=
  match t with
  | VictimSystemType__bds__true => 0
  end.
Definition VictimSystemType__bds__F2 n :=
  match n with
  | 0 => VictimSystemType__bds__true
  | _ => VictimSystemType__bds__true
  end.
Lemma VictimSystemType__bds__F1F2 : forall x : VictimSystemType__bds__Type, (VictimSystemType__bds__F1 x <= 0) /\ VictimSystemType__bds__F2 (VictimSystemType__bds__F1 x) = x. imp_solve. Qed.
Lemma VictimSystemType__bds__F2F1 : forall (y : nat) (H : y <= 0), VictimSystemType__bds__F1 (VictimSystemType__bds__F2 y) = y. enum_solve H y. Qed.

Inductive VictimSystemType__galileo__Type : Set :=
 | VictimSystemType__galileo__true
.
Definition VictimSystemType__galileo__cond := (fun (_ : VictimSystemType__galileo__Type) => True).
Lemma VictimSystemType__galileo__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VictimSystemType__galileo__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VictimSystemType__galileo__nat__helper.

Definition VictimSystemType__galileo__F1 t :=
  match t with
  | VictimSystemType__galileo__true => 0
  end.
Definition VictimSystemType__galileo__F2 n :=
  match n with
  | 0 => VictimSystemType__galileo__true
  | _ => VictimSystemType__galileo__true
  end.
Lemma VictimSystemType__galileo__F1F2 : forall x : VictimSystemType__galileo__Type, (VictimSystemType__galileo__F1 x <= 0) /\ VictimSystemType__galileo__F2 (VictimSystemType__galileo__F1 x) = x. imp_solve. Qed.
Lemma VictimSystemType__galileo__F2F1 : forall (y : nat) (H : y <= 0), VictimSystemType__galileo__F1 (VictimSystemType__galileo__F2 y) = y. enum_solve H y. Qed.

Inductive VictimSystemType__wlan__Type : Set :=
 | VictimSystemType__wlan__true
.
Definition VictimSystemType__wlan__cond := (fun (_ : VictimSystemType__wlan__Type) => True).
Lemma VictimSystemType__wlan__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VictimSystemType__wlan__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VictimSystemType__wlan__nat__helper.

Definition VictimSystemType__wlan__F1 t :=
  match t with
  | VictimSystemType__wlan__true => 0
  end.
Definition VictimSystemType__wlan__F2 n :=
  match n with
  | 0 => VictimSystemType__wlan__true
  | _ => VictimSystemType__wlan__true
  end.
Lemma VictimSystemType__wlan__F1F2 : forall x : VictimSystemType__wlan__Type, (VictimSystemType__wlan__F1 x <= 0) /\ VictimSystemType__wlan__F2 (VictimSystemType__wlan__F1 x) = x. imp_solve. Qed.
Lemma VictimSystemType__wlan__F2F1 : forall (y : nat) (H : y <= 0), VictimSystemType__wlan__F1 (VictimSystemType__wlan__F2 y) = y. enum_solve H y. Qed.

Inductive VictimSystemType__bluetooth__Type : Set :=
 | VictimSystemType__bluetooth__true
.
Definition VictimSystemType__bluetooth__cond := (fun (_ : VictimSystemType__bluetooth__Type) => True).
Lemma VictimSystemType__bluetooth__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VictimSystemType__bluetooth__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VictimSystemType__bluetooth__nat__helper.

Definition VictimSystemType__bluetooth__F1 t :=
  match t with
  | VictimSystemType__bluetooth__true => 0
  end.
Definition VictimSystemType__bluetooth__F2 n :=
  match n with
  | 0 => VictimSystemType__bluetooth__true
  | _ => VictimSystemType__bluetooth__true
  end.
Lemma VictimSystemType__bluetooth__F1F2 : forall x : VictimSystemType__bluetooth__Type, (VictimSystemType__bluetooth__F1 x <= 0) /\ VictimSystemType__bluetooth__F2 (VictimSystemType__bluetooth__F1 x) = x. imp_solve. Qed.
Lemma VictimSystemType__bluetooth__F2F1 : forall (y : nat) (H : y <= 0), VictimSystemType__bluetooth__F1 (VictimSystemType__bluetooth__F2 y) = y. enum_solve H y. Qed.

Record VictimSystemType__Type : Set :=
  make__VictimSystemType__Type {
    VictimSystemType__gps : option VictimSystemType__gps__Type ;
    VictimSystemType__glonass : option VictimSystemType__glonass__Type ;
    VictimSystemType__bds : option VictimSystemType__bds__Type ;
    VictimSystemType__galileo : option VictimSystemType__galileo__Type ;
    VictimSystemType__wlan : option VictimSystemType__wlan__Type ;
    VictimSystemType__bluetooth : option VictimSystemType__bluetooth__Type ;
}.
Definition VictimSystemType__list := (
 Opt VictimSystemType__gps__Type VictimSystemType__gps__cond ::
 Opt VictimSystemType__glonass__Type VictimSystemType__glonass__cond ::
 Opt VictimSystemType__bds__Type VictimSystemType__bds__cond ::
 Opt VictimSystemType__galileo__Type VictimSystemType__galileo__cond ::
 Opt VictimSystemType__wlan__Type VictimSystemType__wlan__cond ::
 Opt VictimSystemType__bluetooth__Type VictimSystemType__bluetooth__cond ::
 nil).
Definition VictimSystemType__cond z := 
  opt_cond VictimSystemType__gps__cond (VictimSystemType__gps z) /\
  opt_cond VictimSystemType__glonass__cond (VictimSystemType__glonass z) /\
  opt_cond VictimSystemType__bds__cond (VictimSystemType__bds z) /\
  opt_cond VictimSystemType__galileo__cond (VictimSystemType__galileo z) /\
  opt_cond VictimSystemType__wlan__cond (VictimSystemType__wlan z) /\
  opt_cond VictimSystemType__bluetooth__cond (VictimSystemType__bluetooth z) /\
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
Definition VictimSystemType__gps__Format : T_Format VictimSystemType__gps__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VictimSystemType__gps__nat__Format VictimSystemType__gps__F1 VictimSystemType__gps__F2 VictimSystemType__gps__F1F2 VictimSystemType__gps__F2F1.

Opaque VictimSystemType__gps__cond VictimSystemType__gps__Format.

Definition VictimSystemType__glonass__Format : T_Format VictimSystemType__glonass__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VictimSystemType__glonass__nat__Format VictimSystemType__glonass__F1 VictimSystemType__glonass__F2 VictimSystemType__glonass__F1F2 VictimSystemType__glonass__F2F1.

Opaque VictimSystemType__glonass__cond VictimSystemType__glonass__Format.

Definition VictimSystemType__bds__Format : T_Format VictimSystemType__bds__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VictimSystemType__bds__nat__Format VictimSystemType__bds__F1 VictimSystemType__bds__F2 VictimSystemType__bds__F1F2 VictimSystemType__bds__F2F1.

Opaque VictimSystemType__bds__cond VictimSystemType__bds__Format.

Definition VictimSystemType__galileo__Format : T_Format VictimSystemType__galileo__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VictimSystemType__galileo__nat__Format VictimSystemType__galileo__F1 VictimSystemType__galileo__F2 VictimSystemType__galileo__F1F2 VictimSystemType__galileo__F2F1.

Opaque VictimSystemType__galileo__cond VictimSystemType__galileo__Format.

Definition VictimSystemType__wlan__Format : T_Format VictimSystemType__wlan__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VictimSystemType__wlan__nat__Format VictimSystemType__wlan__F1 VictimSystemType__wlan__F2 VictimSystemType__wlan__F1F2 VictimSystemType__wlan__F2F1.

Opaque VictimSystemType__wlan__cond VictimSystemType__wlan__Format.

Definition VictimSystemType__bluetooth__Format : T_Format VictimSystemType__bluetooth__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VictimSystemType__bluetooth__nat__Format VictimSystemType__bluetooth__F1 VictimSystemType__bluetooth__F2 VictimSystemType__bluetooth__F1F2 VictimSystemType__bluetooth__F2F1.

Opaque VictimSystemType__bluetooth__cond VictimSystemType__bluetooth__Format.


Definition VictimSystemType__Format_Type := Eval cbn in seq_format_prod VictimSystemType__list.
Definition VictimSystemType__Format_list : VictimSystemType__Format_Type :=
  (VictimSystemType__gps__Format, (VictimSystemType__glonass__Format, (VictimSystemType__bds__Format, (VictimSystemType__galileo__Format, (VictimSystemType__wlan__Format, (VictimSystemType__bluetooth__Format, unit_format)))))).
Definition VictimSystemType__list__Format := (*Eval compute in *) seq_format VictimSystemType__list VictimSystemType__Format_list.
Definition VictimSystemType__F1 z :=
  (VictimSystemType__gps z, (VictimSystemType__glonass z, (VictimSystemType__bds z, (VictimSystemType__galileo z, (VictimSystemType__wlan z, (VictimSystemType__bluetooth z, tt)))))).
Definition VictimSystemType__F2 (y : seq_type VictimSystemType__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__VictimSystemType__Type i0 i1 i2 i3 i4 i5
  end.
Lemma VictimSystemType__F1F2_cond (z : VictimSystemType__Type)
  : VictimSystemType__cond z ->
  (seq_cond VictimSystemType__list (VictimSystemType__F1 z)).
intro H. unfold VictimSystemType__cond in H. simpl. auto. Qed.
Lemma VictimSystemType__F1F2_cond2 (z : VictimSystemType__Type)
 : VictimSystemType__F2 (VictimSystemType__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VictimSystemType__F2F1_cond (y : seq_type VictimSystemType__list)
  : seq_cond VictimSystemType__list y ->
 (VictimSystemType__cond (VictimSystemType__F2 y)) /\  VictimSystemType__F1 (VictimSystemType__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VictimSystemType__cond. simpl in *. auto.
 - simpl. unfold VictimSystemType__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VictimSystemType__Format : T_Format VictimSystemType__Type VictimSystemType__cond :=
        proj2_format  VictimSystemType__cond VictimSystemType__list__Format
    VictimSystemType__F1 VictimSystemType__F2 VictimSystemType__F1F2_cond  VictimSystemType__F1F2_cond2 VictimSystemType__F2F1_cond.
Opaque VictimSystemType__cond VictimSystemType__Format.

