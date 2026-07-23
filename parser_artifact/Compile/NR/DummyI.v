Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DummyI__supportedSRS_TxPortSwitch__Type : Set :=
 | DummyI__supportedSRS_TxPortSwitch__t1r2
 | DummyI__supportedSRS_TxPortSwitch__t1r4
 | DummyI__supportedSRS_TxPortSwitch__t2r4
 | DummyI__supportedSRS_TxPortSwitch__t1r4_t2r4
 | DummyI__supportedSRS_TxPortSwitch__tr_equal
.
Definition DummyI__supportedSRS_TxPortSwitch__cond := (fun (_ : DummyI__supportedSRS_TxPortSwitch__Type) => True).
Lemma DummyI__supportedSRS_TxPortSwitch__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyI__supportedSRS_TxPortSwitch__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 DummyI__supportedSRS_TxPortSwitch__nat__helper.

Definition DummyI__supportedSRS_TxPortSwitch__F1 t :=
  match t with
  | DummyI__supportedSRS_TxPortSwitch__t1r2 => 0
  | DummyI__supportedSRS_TxPortSwitch__t1r4 => 1
  | DummyI__supportedSRS_TxPortSwitch__t2r4 => 2
  | DummyI__supportedSRS_TxPortSwitch__t1r4_t2r4 => 3
  | DummyI__supportedSRS_TxPortSwitch__tr_equal => 4
  end.
Definition DummyI__supportedSRS_TxPortSwitch__F2 n :=
  match n with
  | 0 => DummyI__supportedSRS_TxPortSwitch__t1r2
  | 1 => DummyI__supportedSRS_TxPortSwitch__t1r4
  | 2 => DummyI__supportedSRS_TxPortSwitch__t2r4
  | 3 => DummyI__supportedSRS_TxPortSwitch__t1r4_t2r4
  | 4 => DummyI__supportedSRS_TxPortSwitch__tr_equal
  | _ => DummyI__supportedSRS_TxPortSwitch__t1r2
  end.
Lemma DummyI__supportedSRS_TxPortSwitch__F1F2 : forall x : DummyI__supportedSRS_TxPortSwitch__Type, (DummyI__supportedSRS_TxPortSwitch__F1 x <= 4) /\ DummyI__supportedSRS_TxPortSwitch__F2 (DummyI__supportedSRS_TxPortSwitch__F1 x) = x. imp_solve. Qed.
Lemma DummyI__supportedSRS_TxPortSwitch__F2F1 : forall (y : nat) (H : y <= 4), DummyI__supportedSRS_TxPortSwitch__F1 (DummyI__supportedSRS_TxPortSwitch__F2 y) = y. enum_solve H y. Qed.

Inductive DummyI__txSwitchImpactToRx__Type : Set :=
 | DummyI__txSwitchImpactToRx__true
.
Definition DummyI__txSwitchImpactToRx__cond := (fun (_ : DummyI__txSwitchImpactToRx__Type) => True).
Lemma DummyI__txSwitchImpactToRx__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyI__txSwitchImpactToRx__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DummyI__txSwitchImpactToRx__nat__helper.

Definition DummyI__txSwitchImpactToRx__F1 t :=
  match t with
  | DummyI__txSwitchImpactToRx__true => 0
  end.
Definition DummyI__txSwitchImpactToRx__F2 n :=
  match n with
  | 0 => DummyI__txSwitchImpactToRx__true
  | _ => DummyI__txSwitchImpactToRx__true
  end.
Lemma DummyI__txSwitchImpactToRx__F1F2 : forall x : DummyI__txSwitchImpactToRx__Type, (DummyI__txSwitchImpactToRx__F1 x <= 0) /\ DummyI__txSwitchImpactToRx__F2 (DummyI__txSwitchImpactToRx__F1 x) = x. imp_solve. Qed.
Lemma DummyI__txSwitchImpactToRx__F2F1 : forall (y : nat) (H : y <= 0), DummyI__txSwitchImpactToRx__F1 (DummyI__txSwitchImpactToRx__F2 y) = y. enum_solve H y. Qed.

Record DummyI__Type : Set :=
  make__DummyI__Type {
    DummyI__supportedSRS_TxPortSwitch : DummyI__supportedSRS_TxPortSwitch__Type ;
    DummyI__txSwitchImpactToRx : option DummyI__txSwitchImpactToRx__Type ;
}.
Definition DummyI__list := (
 Nor DummyI__supportedSRS_TxPortSwitch__Type DummyI__supportedSRS_TxPortSwitch__cond ::
 Opt DummyI__txSwitchImpactToRx__Type DummyI__txSwitchImpactToRx__cond ::
 nil).
Definition DummyI__cond z := 
  DummyI__supportedSRS_TxPortSwitch__cond (DummyI__supportedSRS_TxPortSwitch z) /\
  opt_cond DummyI__txSwitchImpactToRx__cond (DummyI__txSwitchImpactToRx z) /\
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
Definition DummyI__supportedSRS_TxPortSwitch__Format : T_Format DummyI__supportedSRS_TxPortSwitch__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyI__supportedSRS_TxPortSwitch__nat__Format DummyI__supportedSRS_TxPortSwitch__F1 DummyI__supportedSRS_TxPortSwitch__F2 DummyI__supportedSRS_TxPortSwitch__F1F2 DummyI__supportedSRS_TxPortSwitch__F2F1.

Opaque DummyI__supportedSRS_TxPortSwitch__cond DummyI__supportedSRS_TxPortSwitch__Format.

Definition DummyI__txSwitchImpactToRx__Format : T_Format DummyI__txSwitchImpactToRx__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyI__txSwitchImpactToRx__nat__Format DummyI__txSwitchImpactToRx__F1 DummyI__txSwitchImpactToRx__F2 DummyI__txSwitchImpactToRx__F1F2 DummyI__txSwitchImpactToRx__F2F1.

Opaque DummyI__txSwitchImpactToRx__cond DummyI__txSwitchImpactToRx__Format.


Definition DummyI__Format_Type := Eval cbn in seq_format_prod DummyI__list.
Definition DummyI__Format_list : DummyI__Format_Type :=
  (DummyI__supportedSRS_TxPortSwitch__Format, (DummyI__txSwitchImpactToRx__Format, unit_format)).
Definition DummyI__list__Format := (*Eval compute in *) seq_format DummyI__list DummyI__Format_list.
Definition DummyI__F1 z :=
  (DummyI__supportedSRS_TxPortSwitch z, (DummyI__txSwitchImpactToRx z, tt)).
Definition DummyI__F2 (y : seq_type DummyI__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DummyI__Type i0 i1
  end.
Lemma DummyI__F1F2_cond (z : DummyI__Type)
  : DummyI__cond z ->
  (seq_cond DummyI__list (DummyI__F1 z)).
intro H. unfold DummyI__cond in H. simpl. auto. Qed.
Lemma DummyI__F1F2_cond2 (z : DummyI__Type)
 : DummyI__F2 (DummyI__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyI__F2F1_cond (y : seq_type DummyI__list)
  : seq_cond DummyI__list y ->
 (DummyI__cond (DummyI__F2 y)) /\  DummyI__F1 (DummyI__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyI__cond. simpl in *. auto.
 - simpl. unfold DummyI__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyI__Format : T_Format DummyI__Type DummyI__cond :=
        proj2_format  DummyI__cond DummyI__list__Format
    DummyI__F1 DummyI__F2 DummyI__F1F2_cond  DummyI__F1F2_cond2 DummyI__F2F1_cond.
Opaque DummyI__cond DummyI__Format.

