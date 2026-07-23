Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Type : Set :=
 | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n8
 | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n16
 | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n32
 | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n64
.
Definition DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__cond := (fun (_ : DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Type) => True).
Lemma DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__nat__helper.

Definition DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1 t :=
  match t with
  | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n8 => 0
  | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n16 => 1
  | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n32 => 2
  | DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n64 => 3
  end.
Definition DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F2 n :=
  match n with
  | 0 => DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n8
  | 1 => DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n16
  | 2 => DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n32
  | 3 => DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n64
  | _ => DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__n8
  end.
Lemma DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1F2 : forall x : DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Type, (DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1 x <= 3) /\ DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F2 (DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1 x) = x. imp_solve. Qed.
Lemma DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F2F1 : forall (y : nat) (H : y <= 3), DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1 (DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F2 y) = y. enum_solve H y. Qed.

Inductive DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Type : Set :=
 | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n0
 | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n4
 | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n8
 | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n16
 | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n32
 | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n64
.
Definition DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__cond := (fun (_ : DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Type) => True).
Lemma DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__nat__helper.

Definition DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1 t :=
  match t with
  | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n0 => 0
  | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n4 => 1
  | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n8 => 2
  | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n16 => 3
  | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n32 => 4
  | DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n64 => 5
  end.
Definition DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F2 n :=
  match n with
  | 0 => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n0
  | 1 => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n4
  | 2 => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n8
  | 3 => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n16
  | 4 => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n32
  | 5 => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n64
  | _ => DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__n0
  end.
Lemma DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1F2 : forall x : DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Type, (DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1 x <= 5) /\ DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F2 (DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1 x) = x. imp_solve. Qed.
Lemma DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F2F1 : forall (y : nat) (H : y <= 5), DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1 (DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F2 y) = y. enum_solve H y. Qed.

Inductive DummyG__supportedCSI_RS_Density__Type : Set :=
 | DummyG__supportedCSI_RS_Density__one
 | DummyG__supportedCSI_RS_Density__three
 | DummyG__supportedCSI_RS_Density__oneAndThree
.
Definition DummyG__supportedCSI_RS_Density__cond := (fun (_ : DummyG__supportedCSI_RS_Density__Type) => True).
Lemma DummyG__supportedCSI_RS_Density__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyG__supportedCSI_RS_Density__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DummyG__supportedCSI_RS_Density__nat__helper.

Definition DummyG__supportedCSI_RS_Density__F1 t :=
  match t with
  | DummyG__supportedCSI_RS_Density__one => 0
  | DummyG__supportedCSI_RS_Density__three => 1
  | DummyG__supportedCSI_RS_Density__oneAndThree => 2
  end.
Definition DummyG__supportedCSI_RS_Density__F2 n :=
  match n with
  | 0 => DummyG__supportedCSI_RS_Density__one
  | 1 => DummyG__supportedCSI_RS_Density__three
  | 2 => DummyG__supportedCSI_RS_Density__oneAndThree
  | _ => DummyG__supportedCSI_RS_Density__one
  end.
Lemma DummyG__supportedCSI_RS_Density__F1F2 : forall x : DummyG__supportedCSI_RS_Density__Type, (DummyG__supportedCSI_RS_Density__F1 x <= 2) /\ DummyG__supportedCSI_RS_Density__F2 (DummyG__supportedCSI_RS_Density__F1 x) = x. imp_solve. Qed.
Lemma DummyG__supportedCSI_RS_Density__F2F1 : forall (y : nat) (H : y <= 2), DummyG__supportedCSI_RS_Density__F1 (DummyG__supportedCSI_RS_Density__F2 y) = y. enum_solve H y. Qed.

Record DummyG__Type : Set :=
  make__DummyG__Type {
    DummyG__maxNumberSSB_CSI_RS_ResourceOneTx : DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Type ;
    DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx : DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Type ;
    DummyG__supportedCSI_RS_Density : DummyG__supportedCSI_RS_Density__Type ;
}.
Definition DummyG__list := (
 Nor DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Type DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__cond ::
 Nor DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Type DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__cond ::
 Nor DummyG__supportedCSI_RS_Density__Type DummyG__supportedCSI_RS_Density__cond ::
 nil).
Definition DummyG__cond z := 
  DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__cond (DummyG__maxNumberSSB_CSI_RS_ResourceOneTx z) /\
  DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__cond (DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx z) /\
  DummyG__supportedCSI_RS_Density__cond (DummyG__supportedCSI_RS_Density z) /\
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
Definition DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Format : T_Format DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__nat__Format DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1 DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F2 DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F1F2 DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__F2F1.

Opaque DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__cond DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Format.

Definition DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Format : T_Format DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__nat__Format DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1 DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F2 DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F1F2 DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__F2F1.

Opaque DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__cond DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Format.

Definition DummyG__supportedCSI_RS_Density__Format : T_Format DummyG__supportedCSI_RS_Density__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyG__supportedCSI_RS_Density__nat__Format DummyG__supportedCSI_RS_Density__F1 DummyG__supportedCSI_RS_Density__F2 DummyG__supportedCSI_RS_Density__F1F2 DummyG__supportedCSI_RS_Density__F2F1.

Opaque DummyG__supportedCSI_RS_Density__cond DummyG__supportedCSI_RS_Density__Format.


Definition DummyG__Format_Type := Eval cbn in seq_format_prod DummyG__list.
Definition DummyG__Format_list : DummyG__Format_Type :=
  (DummyG__maxNumberSSB_CSI_RS_ResourceOneTx__Format, (DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx__Format, (DummyG__supportedCSI_RS_Density__Format, unit_format))).
Definition DummyG__list__Format := (*Eval compute in *) seq_format DummyG__list DummyG__Format_list.
Definition DummyG__F1 z :=
  (DummyG__maxNumberSSB_CSI_RS_ResourceOneTx z, (DummyG__maxNumberSSB_CSI_RS_ResourceTwoTx z, (DummyG__supportedCSI_RS_Density z, tt))).
Definition DummyG__F2 (y : seq_type DummyG__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__DummyG__Type i0 i1 i2
  end.
Lemma DummyG__F1F2_cond (z : DummyG__Type)
  : DummyG__cond z ->
  (seq_cond DummyG__list (DummyG__F1 z)).
intro H. unfold DummyG__cond in H. simpl. auto. Qed.
Lemma DummyG__F1F2_cond2 (z : DummyG__Type)
 : DummyG__F2 (DummyG__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyG__F2F1_cond (y : seq_type DummyG__list)
  : seq_cond DummyG__list y ->
 (DummyG__cond (DummyG__F2 y)) /\  DummyG__F1 (DummyG__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyG__cond. simpl in *. auto.
 - simpl. unfold DummyG__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyG__Format : T_Format DummyG__Type DummyG__cond :=
        proj2_format  DummyG__cond DummyG__list__Format
    DummyG__F1 DummyG__F2 DummyG__F1F2_cond  DummyG__F1F2_cond2 DummyG__F2F1_cond.
Opaque DummyG__cond DummyG__Format.

