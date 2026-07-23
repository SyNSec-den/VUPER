Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Type : Set :=
 | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n0
 | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n8
 | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n16
 | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n32
 | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n64
.
Definition BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__cond := (fun (_ : BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Type) => True).
Lemma BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__nat__helper.

Definition BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1 t :=
  match t with
  | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n0 => 0
  | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n8 => 1
  | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n16 => 2
  | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n32 => 3
  | BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n64 => 4
  end.
Definition BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F2 n :=
  match n with
  | 0 => BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n0
  | 1 => BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n8
  | 2 => BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n16
  | 3 => BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n32
  | 4 => BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n64
  | _ => BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__n0
  end.
Lemma BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1F2 : forall x : BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Type, (BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1 x <= 4) /\ BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F2 (BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1 x) = x. imp_solve. Qed.
Lemma BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F2F1 : forall (y : nat) (H : y <= 4), BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1 (BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F2 y) = y. enum_solve H y. Qed.

Inductive BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Type : Set :=
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n0
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n4
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n8
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n16
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n32
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n64
.
Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__cond := (fun (_ : BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Type) => True).
Lemma BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__nat__helper.

Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1 t :=
  match t with
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n0 => 0
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n4 => 1
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n8 => 2
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n16 => 3
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n32 => 4
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n64 => 5
  end.
Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F2 n :=
  match n with
  | 0 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n0
  | 1 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n4
  | 2 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n8
  | 3 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n16
  | 4 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n32
  | 5 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n64
  | _ => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__n0
  end.
Lemma BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1F2 : forall x : BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Type, (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1 x <= 5) /\ BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F2 (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1 x) = x. imp_solve. Qed.
Lemma BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F2F1 : forall (y : nat) (H : y <= 5), BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1 (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F2 y) = y. enum_solve H y. Qed.

Inductive BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Type : Set :=
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n0
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n4
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n8
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n16
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n32
 | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n64
.
Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__cond := (fun (_ : BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Type) => True).
Lemma BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__nat__helper.

Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1 t :=
  match t with
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n0 => 0
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n4 => 1
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n8 => 2
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n16 => 3
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n32 => 4
  | BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n64 => 5
  end.
Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F2 n :=
  match n with
  | 0 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n0
  | 1 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n4
  | 2 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n8
  | 3 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n16
  | 4 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n32
  | 5 => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n64
  | _ => BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__n0
  end.
Lemma BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1F2 : forall x : BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Type, (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1 x <= 5) /\ BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F2 (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1 x) = x. imp_solve. Qed.
Lemma BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F2F1 : forall (y : nat) (H : y <= 5), BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1 (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F2 y) = y. enum_solve H y. Qed.

Inductive BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Type : Set :=
 | BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__one
 | BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__three
 | BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__oneAndThree
.
Definition BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__cond := (fun (_ : BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Type) => True).
Lemma BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__nat__helper.

Definition BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1 t :=
  match t with
  | BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__one => 0
  | BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__three => 1
  | BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__oneAndThree => 2
  end.
Definition BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F2 n :=
  match n with
  | 0 => BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__one
  | 1 => BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__three
  | 2 => BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__oneAndThree
  | _ => BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__one
  end.
Lemma BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1F2 : forall x : BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Type, (BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1 x <= 2) /\ BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F2 (BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1 x) = x. imp_solve. Qed.
Lemma BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F2F1 : forall (y : nat) (H : y <= 2), BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1 (BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F2 y) = y. enum_solve H y. Qed.

Inductive BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Type : Set :=
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n0
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n1
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n4
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n8
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n16
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n32
 | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n64
.
Definition BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__cond := (fun (_ : BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Type) => True).
Lemma BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__nat__helper.

Definition BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1 t :=
  match t with
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n0 => 0
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n1 => 1
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n4 => 2
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n8 => 3
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n16 => 4
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n32 => 5
  | BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n64 => 6
  end.
Definition BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F2 n :=
  match n with
  | 0 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n0
  | 1 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n1
  | 2 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n4
  | 3 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n8
  | 4 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n16
  | 5 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n32
  | 6 => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n64
  | _ => BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__n0
  end.
Lemma BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1F2 : forall x : BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Type, (BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1 x <= 6) /\ BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F2 (BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1 x) = x. imp_solve. Qed.
Lemma BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F2F1 : forall (y : nat) (H : y <= 6), BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1 (BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F2 y) = y. enum_solve H y. Qed.

Record BeamManagementSSB_CSI_RS__Type : Set :=
  make__BeamManagementSSB_CSI_RS__Type {
    BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx : BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Type ;
    BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource : BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Type ;
    BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx : BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Type ;
    BeamManagementSSB_CSI_RS__supportedCSI_RS_Density : option BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Type ;
    BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource : BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Type ;
}.
Definition BeamManagementSSB_CSI_RS__list := (
 Nor BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Type BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__cond ::
 Nor BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Type BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__cond ::
 Nor BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Type BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__cond ::
 Opt BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Type BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__cond ::
 Nor BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Type BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__cond ::
 nil).
Definition BeamManagementSSB_CSI_RS__cond z := 
  BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__cond (BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx z) /\
  BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__cond (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource z) /\
  BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__cond (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx z) /\
  opt_cond BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__cond (BeamManagementSSB_CSI_RS__supportedCSI_RS_Density z) /\
  BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__cond (BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource z) /\
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
Definition BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Format : T_Format BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__nat__Format BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1 BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F2 BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F1F2 BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__F2F1.

Opaque BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__cond BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Format.

Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Format : T_Format BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__nat__Format BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F2 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F1F2 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__F2F1.

Opaque BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__cond BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Format.

Definition BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Format : T_Format BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__nat__Format BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F2 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F1F2 BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__F2F1.

Opaque BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__cond BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Format.

Definition BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Format : T_Format BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__nat__Format BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1 BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F2 BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F1F2 BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__F2F1.

Opaque BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__cond BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Format.

Definition BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Format : T_Format BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__nat__Format BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1 BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F2 BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F1F2 BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__F2F1.

Opaque BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__cond BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Format.


Definition BeamManagementSSB_CSI_RS__Format_Type := Eval cbn in seq_format_prod BeamManagementSSB_CSI_RS__list.
Definition BeamManagementSSB_CSI_RS__Format_list : BeamManagementSSB_CSI_RS__Format_Type :=
  (BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx__Format, (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource__Format, (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx__Format, (BeamManagementSSB_CSI_RS__supportedCSI_RS_Density__Format, (BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource__Format, unit_format))))).
Definition BeamManagementSSB_CSI_RS__list__Format := (*Eval compute in *) seq_format BeamManagementSSB_CSI_RS__list BeamManagementSSB_CSI_RS__Format_list.
Definition BeamManagementSSB_CSI_RS__F1 z :=
  (BeamManagementSSB_CSI_RS__maxNumberSSB_CSI_RS_ResourceOneTx z, (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_Resource z, (BeamManagementSSB_CSI_RS__maxNumberCSI_RS_ResourceTwoTx z, (BeamManagementSSB_CSI_RS__supportedCSI_RS_Density z, (BeamManagementSSB_CSI_RS__maxNumberAperiodicCSI_RS_Resource z, tt))))).
Definition BeamManagementSSB_CSI_RS__F2 (y : seq_type BeamManagementSSB_CSI_RS__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__BeamManagementSSB_CSI_RS__Type i0 i1 i2 i3 i4
  end.
Lemma BeamManagementSSB_CSI_RS__F1F2_cond (z : BeamManagementSSB_CSI_RS__Type)
  : BeamManagementSSB_CSI_RS__cond z ->
  (seq_cond BeamManagementSSB_CSI_RS__list (BeamManagementSSB_CSI_RS__F1 z)).
intro H. unfold BeamManagementSSB_CSI_RS__cond in H. simpl. auto. Qed.
Lemma BeamManagementSSB_CSI_RS__F1F2_cond2 (z : BeamManagementSSB_CSI_RS__Type)
 : BeamManagementSSB_CSI_RS__F2 (BeamManagementSSB_CSI_RS__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BeamManagementSSB_CSI_RS__F2F1_cond (y : seq_type BeamManagementSSB_CSI_RS__list)
  : seq_cond BeamManagementSSB_CSI_RS__list y ->
 (BeamManagementSSB_CSI_RS__cond (BeamManagementSSB_CSI_RS__F2 y)) /\  BeamManagementSSB_CSI_RS__F1 (BeamManagementSSB_CSI_RS__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BeamManagementSSB_CSI_RS__cond. simpl in *. auto.
 - simpl. unfold BeamManagementSSB_CSI_RS__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BeamManagementSSB_CSI_RS__Format : T_Format BeamManagementSSB_CSI_RS__Type BeamManagementSSB_CSI_RS__cond :=
        proj2_format  BeamManagementSSB_CSI_RS__cond BeamManagementSSB_CSI_RS__list__Format
    BeamManagementSSB_CSI_RS__F1 BeamManagementSSB_CSI_RS__F2 BeamManagementSSB_CSI_RS__F1F2_cond  BeamManagementSSB_CSI_RS__F1F2_cond2 BeamManagementSSB_CSI_RS__F2F1_cond.
Opaque BeamManagementSSB_CSI_RS__cond BeamManagementSSB_CSI_RS__Format.

