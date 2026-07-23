Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UE_TimersAndConstants__t300__Type : Set :=
 | UE_TimersAndConstants__t300__ms100
 | UE_TimersAndConstants__t300__ms200
 | UE_TimersAndConstants__t300__ms300
 | UE_TimersAndConstants__t300__ms400
 | UE_TimersAndConstants__t300__ms600
 | UE_TimersAndConstants__t300__ms1000
 | UE_TimersAndConstants__t300__ms1500
 | UE_TimersAndConstants__t300__ms2000
.
Definition UE_TimersAndConstants__t300__cond := (fun (_ : UE_TimersAndConstants__t300__Type) => True).
Lemma UE_TimersAndConstants__t300__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__t300__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UE_TimersAndConstants__t300__nat__helper.

Definition UE_TimersAndConstants__t300__F1 t :=
  match t with
  | UE_TimersAndConstants__t300__ms100 => 0
  | UE_TimersAndConstants__t300__ms200 => 1
  | UE_TimersAndConstants__t300__ms300 => 2
  | UE_TimersAndConstants__t300__ms400 => 3
  | UE_TimersAndConstants__t300__ms600 => 4
  | UE_TimersAndConstants__t300__ms1000 => 5
  | UE_TimersAndConstants__t300__ms1500 => 6
  | UE_TimersAndConstants__t300__ms2000 => 7
  end.
Definition UE_TimersAndConstants__t300__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__t300__ms100
  | 1 => UE_TimersAndConstants__t300__ms200
  | 2 => UE_TimersAndConstants__t300__ms300
  | 3 => UE_TimersAndConstants__t300__ms400
  | 4 => UE_TimersAndConstants__t300__ms600
  | 5 => UE_TimersAndConstants__t300__ms1000
  | 6 => UE_TimersAndConstants__t300__ms1500
  | 7 => UE_TimersAndConstants__t300__ms2000
  | _ => UE_TimersAndConstants__t300__ms100
  end.
Lemma UE_TimersAndConstants__t300__F1F2 : forall x : UE_TimersAndConstants__t300__Type, (UE_TimersAndConstants__t300__F1 x <= 7) /\ UE_TimersAndConstants__t300__F2 (UE_TimersAndConstants__t300__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__t300__F2F1 : forall (y : nat) (H : y <= 7), UE_TimersAndConstants__t300__F1 (UE_TimersAndConstants__t300__F2 y) = y. enum_solve H y. Qed.

Inductive UE_TimersAndConstants__t301__Type : Set :=
 | UE_TimersAndConstants__t301__ms100
 | UE_TimersAndConstants__t301__ms200
 | UE_TimersAndConstants__t301__ms300
 | UE_TimersAndConstants__t301__ms400
 | UE_TimersAndConstants__t301__ms600
 | UE_TimersAndConstants__t301__ms1000
 | UE_TimersAndConstants__t301__ms1500
 | UE_TimersAndConstants__t301__ms2000
.
Definition UE_TimersAndConstants__t301__cond := (fun (_ : UE_TimersAndConstants__t301__Type) => True).
Lemma UE_TimersAndConstants__t301__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__t301__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UE_TimersAndConstants__t301__nat__helper.

Definition UE_TimersAndConstants__t301__F1 t :=
  match t with
  | UE_TimersAndConstants__t301__ms100 => 0
  | UE_TimersAndConstants__t301__ms200 => 1
  | UE_TimersAndConstants__t301__ms300 => 2
  | UE_TimersAndConstants__t301__ms400 => 3
  | UE_TimersAndConstants__t301__ms600 => 4
  | UE_TimersAndConstants__t301__ms1000 => 5
  | UE_TimersAndConstants__t301__ms1500 => 6
  | UE_TimersAndConstants__t301__ms2000 => 7
  end.
Definition UE_TimersAndConstants__t301__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__t301__ms100
  | 1 => UE_TimersAndConstants__t301__ms200
  | 2 => UE_TimersAndConstants__t301__ms300
  | 3 => UE_TimersAndConstants__t301__ms400
  | 4 => UE_TimersAndConstants__t301__ms600
  | 5 => UE_TimersAndConstants__t301__ms1000
  | 6 => UE_TimersAndConstants__t301__ms1500
  | 7 => UE_TimersAndConstants__t301__ms2000
  | _ => UE_TimersAndConstants__t301__ms100
  end.
Lemma UE_TimersAndConstants__t301__F1F2 : forall x : UE_TimersAndConstants__t301__Type, (UE_TimersAndConstants__t301__F1 x <= 7) /\ UE_TimersAndConstants__t301__F2 (UE_TimersAndConstants__t301__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__t301__F2F1 : forall (y : nat) (H : y <= 7), UE_TimersAndConstants__t301__F1 (UE_TimersAndConstants__t301__F2 y) = y. enum_solve H y. Qed.

Inductive UE_TimersAndConstants__t310__Type : Set :=
 | UE_TimersAndConstants__t310__ms0
 | UE_TimersAndConstants__t310__ms50
 | UE_TimersAndConstants__t310__ms100
 | UE_TimersAndConstants__t310__ms200
 | UE_TimersAndConstants__t310__ms500
 | UE_TimersAndConstants__t310__ms1000
 | UE_TimersAndConstants__t310__ms2000
.
Definition UE_TimersAndConstants__t310__cond := (fun (_ : UE_TimersAndConstants__t310__Type) => True).
Lemma UE_TimersAndConstants__t310__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__t310__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 UE_TimersAndConstants__t310__nat__helper.

Definition UE_TimersAndConstants__t310__F1 t :=
  match t with
  | UE_TimersAndConstants__t310__ms0 => 0
  | UE_TimersAndConstants__t310__ms50 => 1
  | UE_TimersAndConstants__t310__ms100 => 2
  | UE_TimersAndConstants__t310__ms200 => 3
  | UE_TimersAndConstants__t310__ms500 => 4
  | UE_TimersAndConstants__t310__ms1000 => 5
  | UE_TimersAndConstants__t310__ms2000 => 6
  end.
Definition UE_TimersAndConstants__t310__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__t310__ms0
  | 1 => UE_TimersAndConstants__t310__ms50
  | 2 => UE_TimersAndConstants__t310__ms100
  | 3 => UE_TimersAndConstants__t310__ms200
  | 4 => UE_TimersAndConstants__t310__ms500
  | 5 => UE_TimersAndConstants__t310__ms1000
  | 6 => UE_TimersAndConstants__t310__ms2000
  | _ => UE_TimersAndConstants__t310__ms0
  end.
Lemma UE_TimersAndConstants__t310__F1F2 : forall x : UE_TimersAndConstants__t310__Type, (UE_TimersAndConstants__t310__F1 x <= 6) /\ UE_TimersAndConstants__t310__F2 (UE_TimersAndConstants__t310__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__t310__F2F1 : forall (y : nat) (H : y <= 6), UE_TimersAndConstants__t310__F1 (UE_TimersAndConstants__t310__F2 y) = y. enum_solve H y. Qed.

Inductive UE_TimersAndConstants__n310__Type : Set :=
 | UE_TimersAndConstants__n310__n1
 | UE_TimersAndConstants__n310__n2
 | UE_TimersAndConstants__n310__n3
 | UE_TimersAndConstants__n310__n4
 | UE_TimersAndConstants__n310__n6
 | UE_TimersAndConstants__n310__n8
 | UE_TimersAndConstants__n310__n10
 | UE_TimersAndConstants__n310__n20
.
Definition UE_TimersAndConstants__n310__cond := (fun (_ : UE_TimersAndConstants__n310__Type) => True).
Lemma UE_TimersAndConstants__n310__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__n310__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UE_TimersAndConstants__n310__nat__helper.

Definition UE_TimersAndConstants__n310__F1 t :=
  match t with
  | UE_TimersAndConstants__n310__n1 => 0
  | UE_TimersAndConstants__n310__n2 => 1
  | UE_TimersAndConstants__n310__n3 => 2
  | UE_TimersAndConstants__n310__n4 => 3
  | UE_TimersAndConstants__n310__n6 => 4
  | UE_TimersAndConstants__n310__n8 => 5
  | UE_TimersAndConstants__n310__n10 => 6
  | UE_TimersAndConstants__n310__n20 => 7
  end.
Definition UE_TimersAndConstants__n310__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__n310__n1
  | 1 => UE_TimersAndConstants__n310__n2
  | 2 => UE_TimersAndConstants__n310__n3
  | 3 => UE_TimersAndConstants__n310__n4
  | 4 => UE_TimersAndConstants__n310__n6
  | 5 => UE_TimersAndConstants__n310__n8
  | 6 => UE_TimersAndConstants__n310__n10
  | 7 => UE_TimersAndConstants__n310__n20
  | _ => UE_TimersAndConstants__n310__n1
  end.
Lemma UE_TimersAndConstants__n310__F1F2 : forall x : UE_TimersAndConstants__n310__Type, (UE_TimersAndConstants__n310__F1 x <= 7) /\ UE_TimersAndConstants__n310__F2 (UE_TimersAndConstants__n310__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__n310__F2F1 : forall (y : nat) (H : y <= 7), UE_TimersAndConstants__n310__F1 (UE_TimersAndConstants__n310__F2 y) = y. enum_solve H y. Qed.

Inductive UE_TimersAndConstants__t311__Type : Set :=
 | UE_TimersAndConstants__t311__ms1000
 | UE_TimersAndConstants__t311__ms3000
 | UE_TimersAndConstants__t311__ms5000
 | UE_TimersAndConstants__t311__ms10000
 | UE_TimersAndConstants__t311__ms15000
 | UE_TimersAndConstants__t311__ms20000
 | UE_TimersAndConstants__t311__ms30000
.
Definition UE_TimersAndConstants__t311__cond := (fun (_ : UE_TimersAndConstants__t311__Type) => True).
Lemma UE_TimersAndConstants__t311__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__t311__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 UE_TimersAndConstants__t311__nat__helper.

Definition UE_TimersAndConstants__t311__F1 t :=
  match t with
  | UE_TimersAndConstants__t311__ms1000 => 0
  | UE_TimersAndConstants__t311__ms3000 => 1
  | UE_TimersAndConstants__t311__ms5000 => 2
  | UE_TimersAndConstants__t311__ms10000 => 3
  | UE_TimersAndConstants__t311__ms15000 => 4
  | UE_TimersAndConstants__t311__ms20000 => 5
  | UE_TimersAndConstants__t311__ms30000 => 6
  end.
Definition UE_TimersAndConstants__t311__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__t311__ms1000
  | 1 => UE_TimersAndConstants__t311__ms3000
  | 2 => UE_TimersAndConstants__t311__ms5000
  | 3 => UE_TimersAndConstants__t311__ms10000
  | 4 => UE_TimersAndConstants__t311__ms15000
  | 5 => UE_TimersAndConstants__t311__ms20000
  | 6 => UE_TimersAndConstants__t311__ms30000
  | _ => UE_TimersAndConstants__t311__ms1000
  end.
Lemma UE_TimersAndConstants__t311__F1F2 : forall x : UE_TimersAndConstants__t311__Type, (UE_TimersAndConstants__t311__F1 x <= 6) /\ UE_TimersAndConstants__t311__F2 (UE_TimersAndConstants__t311__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__t311__F2F1 : forall (y : nat) (H : y <= 6), UE_TimersAndConstants__t311__F1 (UE_TimersAndConstants__t311__F2 y) = y. enum_solve H y. Qed.

Inductive UE_TimersAndConstants__n311__Type : Set :=
 | UE_TimersAndConstants__n311__n1
 | UE_TimersAndConstants__n311__n2
 | UE_TimersAndConstants__n311__n3
 | UE_TimersAndConstants__n311__n4
 | UE_TimersAndConstants__n311__n5
 | UE_TimersAndConstants__n311__n6
 | UE_TimersAndConstants__n311__n8
 | UE_TimersAndConstants__n311__n10
.
Definition UE_TimersAndConstants__n311__cond := (fun (_ : UE_TimersAndConstants__n311__Type) => True).
Lemma UE_TimersAndConstants__n311__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__n311__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UE_TimersAndConstants__n311__nat__helper.

Definition UE_TimersAndConstants__n311__F1 t :=
  match t with
  | UE_TimersAndConstants__n311__n1 => 0
  | UE_TimersAndConstants__n311__n2 => 1
  | UE_TimersAndConstants__n311__n3 => 2
  | UE_TimersAndConstants__n311__n4 => 3
  | UE_TimersAndConstants__n311__n5 => 4
  | UE_TimersAndConstants__n311__n6 => 5
  | UE_TimersAndConstants__n311__n8 => 6
  | UE_TimersAndConstants__n311__n10 => 7
  end.
Definition UE_TimersAndConstants__n311__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__n311__n1
  | 1 => UE_TimersAndConstants__n311__n2
  | 2 => UE_TimersAndConstants__n311__n3
  | 3 => UE_TimersAndConstants__n311__n4
  | 4 => UE_TimersAndConstants__n311__n5
  | 5 => UE_TimersAndConstants__n311__n6
  | 6 => UE_TimersAndConstants__n311__n8
  | 7 => UE_TimersAndConstants__n311__n10
  | _ => UE_TimersAndConstants__n311__n1
  end.
Lemma UE_TimersAndConstants__n311__F1F2 : forall x : UE_TimersAndConstants__n311__Type, (UE_TimersAndConstants__n311__F1 x <= 7) /\ UE_TimersAndConstants__n311__F2 (UE_TimersAndConstants__n311__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__n311__F2F1 : forall (y : nat) (H : y <= 7), UE_TimersAndConstants__n311__F1 (UE_TimersAndConstants__n311__F2 y) = y. enum_solve H y. Qed.

Inductive UE_TimersAndConstants__t319__Type : Set :=
 | UE_TimersAndConstants__t319__ms100
 | UE_TimersAndConstants__t319__ms200
 | UE_TimersAndConstants__t319__ms300
 | UE_TimersAndConstants__t319__ms400
 | UE_TimersAndConstants__t319__ms600
 | UE_TimersAndConstants__t319__ms1000
 | UE_TimersAndConstants__t319__ms1500
 | UE_TimersAndConstants__t319__ms2000
.
Definition UE_TimersAndConstants__t319__cond := (fun (_ : UE_TimersAndConstants__t319__Type) => True).
Lemma UE_TimersAndConstants__t319__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TimersAndConstants__t319__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UE_TimersAndConstants__t319__nat__helper.

Definition UE_TimersAndConstants__t319__F1 t :=
  match t with
  | UE_TimersAndConstants__t319__ms100 => 0
  | UE_TimersAndConstants__t319__ms200 => 1
  | UE_TimersAndConstants__t319__ms300 => 2
  | UE_TimersAndConstants__t319__ms400 => 3
  | UE_TimersAndConstants__t319__ms600 => 4
  | UE_TimersAndConstants__t319__ms1000 => 5
  | UE_TimersAndConstants__t319__ms1500 => 6
  | UE_TimersAndConstants__t319__ms2000 => 7
  end.
Definition UE_TimersAndConstants__t319__F2 n :=
  match n with
  | 0 => UE_TimersAndConstants__t319__ms100
  | 1 => UE_TimersAndConstants__t319__ms200
  | 2 => UE_TimersAndConstants__t319__ms300
  | 3 => UE_TimersAndConstants__t319__ms400
  | 4 => UE_TimersAndConstants__t319__ms600
  | 5 => UE_TimersAndConstants__t319__ms1000
  | 6 => UE_TimersAndConstants__t319__ms1500
  | 7 => UE_TimersAndConstants__t319__ms2000
  | _ => UE_TimersAndConstants__t319__ms100
  end.
Lemma UE_TimersAndConstants__t319__F1F2 : forall x : UE_TimersAndConstants__t319__Type, (UE_TimersAndConstants__t319__F1 x <= 7) /\ UE_TimersAndConstants__t319__F2 (UE_TimersAndConstants__t319__F1 x) = x. imp_solve. Qed.
Lemma UE_TimersAndConstants__t319__F2F1 : forall (y : nat) (H : y <= 7), UE_TimersAndConstants__t319__F1 (UE_TimersAndConstants__t319__F2 y) = y. enum_solve H y. Qed.

Record UE_TimersAndConstants__Type : Set :=
  make__UE_TimersAndConstants__Type {
    UE_TimersAndConstants__t300 : UE_TimersAndConstants__t300__Type ;
    UE_TimersAndConstants__t301 : UE_TimersAndConstants__t301__Type ;
    UE_TimersAndConstants__t310 : UE_TimersAndConstants__t310__Type ;
    UE_TimersAndConstants__n310 : UE_TimersAndConstants__n310__Type ;
    UE_TimersAndConstants__t311 : UE_TimersAndConstants__t311__Type ;
    UE_TimersAndConstants__n311 : UE_TimersAndConstants__n311__Type ;
    UE_TimersAndConstants__t319 : UE_TimersAndConstants__t319__Type ;
}.
Definition UE_TimersAndConstants__root_list : list seq_elem := (
 Nor UE_TimersAndConstants__t300__Type UE_TimersAndConstants__t300__cond ::
 Nor UE_TimersAndConstants__t301__Type UE_TimersAndConstants__t301__cond ::
 Nor UE_TimersAndConstants__t310__Type UE_TimersAndConstants__t310__cond ::
 Nor UE_TimersAndConstants__n310__Type UE_TimersAndConstants__n310__cond ::
 Nor UE_TimersAndConstants__t311__Type UE_TimersAndConstants__t311__cond ::
 Nor UE_TimersAndConstants__n311__Type UE_TimersAndConstants__n311__cond ::
 Nor UE_TimersAndConstants__t319__Type UE_TimersAndConstants__t319__cond ::
 nil).
Definition UE_TimersAndConstants__ext_list : list typ := (
  nil).
Definition UE_TimersAndConstants__cond (z : UE_TimersAndConstants__Type) := 
(  UE_TimersAndConstants__t300__cond (UE_TimersAndConstants__t300 z) /\
  UE_TimersAndConstants__t301__cond (UE_TimersAndConstants__t301 z) /\
  UE_TimersAndConstants__t310__cond (UE_TimersAndConstants__t310 z) /\
  UE_TimersAndConstants__n310__cond (UE_TimersAndConstants__n310 z) /\
  UE_TimersAndConstants__t311__cond (UE_TimersAndConstants__t311 z) /\
  UE_TimersAndConstants__n311__cond (UE_TimersAndConstants__n311 z) /\
  UE_TimersAndConstants__t319__cond (UE_TimersAndConstants__t319 z) /\
  True) /\ 
(  True).


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
Definition UE_TimersAndConstants__t300__Format : T_Format UE_TimersAndConstants__t300__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__t300__nat__Format UE_TimersAndConstants__t300__F1 UE_TimersAndConstants__t300__F2 UE_TimersAndConstants__t300__F1F2 UE_TimersAndConstants__t300__F2F1.

Opaque UE_TimersAndConstants__t300__cond UE_TimersAndConstants__t300__Format.

Definition UE_TimersAndConstants__t301__Format : T_Format UE_TimersAndConstants__t301__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__t301__nat__Format UE_TimersAndConstants__t301__F1 UE_TimersAndConstants__t301__F2 UE_TimersAndConstants__t301__F1F2 UE_TimersAndConstants__t301__F2F1.

Opaque UE_TimersAndConstants__t301__cond UE_TimersAndConstants__t301__Format.

Definition UE_TimersAndConstants__t310__Format : T_Format UE_TimersAndConstants__t310__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__t310__nat__Format UE_TimersAndConstants__t310__F1 UE_TimersAndConstants__t310__F2 UE_TimersAndConstants__t310__F1F2 UE_TimersAndConstants__t310__F2F1.

Opaque UE_TimersAndConstants__t310__cond UE_TimersAndConstants__t310__Format.

Definition UE_TimersAndConstants__n310__Format : T_Format UE_TimersAndConstants__n310__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__n310__nat__Format UE_TimersAndConstants__n310__F1 UE_TimersAndConstants__n310__F2 UE_TimersAndConstants__n310__F1F2 UE_TimersAndConstants__n310__F2F1.

Opaque UE_TimersAndConstants__n310__cond UE_TimersAndConstants__n310__Format.

Definition UE_TimersAndConstants__t311__Format : T_Format UE_TimersAndConstants__t311__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__t311__nat__Format UE_TimersAndConstants__t311__F1 UE_TimersAndConstants__t311__F2 UE_TimersAndConstants__t311__F1F2 UE_TimersAndConstants__t311__F2F1.

Opaque UE_TimersAndConstants__t311__cond UE_TimersAndConstants__t311__Format.

Definition UE_TimersAndConstants__n311__Format : T_Format UE_TimersAndConstants__n311__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__n311__nat__Format UE_TimersAndConstants__n311__F1 UE_TimersAndConstants__n311__F2 UE_TimersAndConstants__n311__F1F2 UE_TimersAndConstants__n311__F2F1.

Opaque UE_TimersAndConstants__n311__cond UE_TimersAndConstants__n311__Format.

Definition UE_TimersAndConstants__t319__Format : T_Format UE_TimersAndConstants__t319__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TimersAndConstants__t319__nat__Format UE_TimersAndConstants__t319__F1 UE_TimersAndConstants__t319__F2 UE_TimersAndConstants__t319__F1F2 UE_TimersAndConstants__t319__F2F1.

Opaque UE_TimersAndConstants__t319__cond UE_TimersAndConstants__t319__Format.


Definition UE_TimersAndConstants__root_Format_Type := Eval cbn in seq_format_prod UE_TimersAndConstants__root_list.
Definition UE_TimersAndConstants__root_Format_list : UE_TimersAndConstants__root_Format_Type :=
  (UE_TimersAndConstants__t300__Format, (UE_TimersAndConstants__t301__Format, (UE_TimersAndConstants__t310__Format, (UE_TimersAndConstants__n310__Format, (UE_TimersAndConstants__t311__Format, (UE_TimersAndConstants__n311__Format, (UE_TimersAndConstants__t319__Format, unit_format))))))).

Definition UE_TimersAndConstants__ext_Format_Type := Eval cbn in get_formats UE_TimersAndConstants__ext_list.
Definition UE_TimersAndConstants__ext_Format_list : UE_TimersAndConstants__ext_Format_Type :=
  unit__Format.

Definition UE_TimersAndConstants__list_type : Set := (seq_type UE_TimersAndConstants__root_list) * (seq_ext_type UE_TimersAndConstants__ext_list).
Definition UE_TimersAndConstants__list_cond (z : UE_TimersAndConstants__list_type) : Prop :=
        (seq_cond UE_TimersAndConstants__root_list (fst z)) /\ (seq_ext_cond UE_TimersAndConstants__ext_list (snd z)).
Definition UE_TimersAndConstants__list_format : T_Format UE_TimersAndConstants__list_type UE_TimersAndConstants__list_cond :=
 (* Eval compute in *) seq_ext_format UE_TimersAndConstants__root_list UE_TimersAndConstants__root_Format_list UE_TimersAndConstants__ext_list UE_TimersAndConstants__ext_Format_list.

Opaque UE_TimersAndConstants__list_format.
Definition UE_TimersAndConstants__F1 (z : UE_TimersAndConstants__Type) : UE_TimersAndConstants__list_type :=
  (((UE_TimersAndConstants__t300 z, (UE_TimersAndConstants__t301 z, (UE_TimersAndConstants__t310 z, (UE_TimersAndConstants__n310 z, (UE_TimersAndConstants__t311 z, (UE_TimersAndConstants__n311 z, (UE_TimersAndConstants__t319 z, tt)))))))), (
tt)).
Definition UE_TimersAndConstants__F2 (y : UE_TimersAndConstants__list_type) : UE_TimersAndConstants__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), _)=>
    make__UE_TimersAndConstants__Type j0 j1 j2 j3 j4 j5 j6
  end.
Definition UE_TimersAndConstants__helper1 : (forall a : UE_TimersAndConstants__Type, UE_TimersAndConstants__cond a -> UE_TimersAndConstants__list_cond (UE_TimersAndConstants__F1 a)).
                     intros. destruct a. auto. Qed.
Definition UE_TimersAndConstants__helper2 : (forall a : UE_TimersAndConstants__Type, UE_TimersAndConstants__F2 (UE_TimersAndConstants__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition UE_TimersAndConstants__helper3 : (forall b : UE_TimersAndConstants__list_type, UE_TimersAndConstants__list_cond b -> UE_TimersAndConstants__cond (UE_TimersAndConstants__F2 b) /\ UE_TimersAndConstants__F1 (UE_TimersAndConstants__F2 b) = b).
                     intros. destruct b as [y y1]. unfold UE_TimersAndConstants__cond, UE_TimersAndConstants__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition UE_TimersAndConstants__Format : T_Format UE_TimersAndConstants__Type UE_TimersAndConstants__cond :=
 proj2_format UE_TimersAndConstants__cond UE_TimersAndConstants__list_format  UE_TimersAndConstants__F1 UE_TimersAndConstants__F2 UE_TimersAndConstants__helper1 UE_TimersAndConstants__helper2 UE_TimersAndConstants__helper3.

Opaque UE_TimersAndConstants__cond UE_TimersAndConstants__Format.

