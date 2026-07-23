Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Type : Set :=
 | ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n35us
 | ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n140us
 | ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n210us
.
Definition ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__cond := (fun (_ : ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Type) => True).
Lemma ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__nat__helper.

Definition ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1 t :=
  match t with
  | ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n35us => 0
  | ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n140us => 1
  | ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n210us => 2
  end.
Definition ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F2 n :=
  match n with
  | 0 => ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n35us
  | 1 => ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n140us
  | 2 => ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n210us
  | _ => ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__n35us
  end.
Lemma ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1F2 : forall x : ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Type, (ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1 x <= 2) /\ ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F2 (ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1 x) = x. imp_solve. Qed.
Lemma ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F2F1 : forall (y : nat) (H : y <= 2), ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1 (ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F2 y) = y. enum_solve H y. Qed.

Record ULTxSwitchingBandPair_v1700__Type : Set :=
  make__ULTxSwitchingBandPair_v1700__Type {
    ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17 : option ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Type ;
}.
Definition ULTxSwitchingBandPair_v1700__list := (
 Opt ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Type ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__cond ::
 nil).
Definition ULTxSwitchingBandPair_v1700__cond z := 
  opt_cond ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__cond (ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17 z) /\
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
Definition ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Format : T_Format ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__nat__Format ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1 ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F2 ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F1F2 ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__F2F1.

Opaque ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__cond ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Format.


Definition ULTxSwitchingBandPair_v1700__Format_Type := Eval cbn in seq_format_prod ULTxSwitchingBandPair_v1700__list.
Definition ULTxSwitchingBandPair_v1700__Format_list : ULTxSwitchingBandPair_v1700__Format_Type :=
  (ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17__Format, unit_format).
Definition ULTxSwitchingBandPair_v1700__list__Format := (*Eval compute in *) seq_format ULTxSwitchingBandPair_v1700__list ULTxSwitchingBandPair_v1700__Format_list.
Definition ULTxSwitchingBandPair_v1700__F1 z :=
  (ULTxSwitchingBandPair_v1700__uplinkTxSwitchingPeriod2T2T_r17 z, tt).
Definition ULTxSwitchingBandPair_v1700__F2 (y : seq_type ULTxSwitchingBandPair_v1700__list) :=
  match y with
  | (i0, _)=>
    make__ULTxSwitchingBandPair_v1700__Type i0
  end.
Lemma ULTxSwitchingBandPair_v1700__F1F2_cond (z : ULTxSwitchingBandPair_v1700__Type)
  : ULTxSwitchingBandPair_v1700__cond z ->
  (seq_cond ULTxSwitchingBandPair_v1700__list (ULTxSwitchingBandPair_v1700__F1 z)).
intro H. unfold ULTxSwitchingBandPair_v1700__cond in H. simpl. auto. Qed.
Lemma ULTxSwitchingBandPair_v1700__F1F2_cond2 (z : ULTxSwitchingBandPair_v1700__Type)
 : ULTxSwitchingBandPair_v1700__F2 (ULTxSwitchingBandPair_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ULTxSwitchingBandPair_v1700__F2F1_cond (y : seq_type ULTxSwitchingBandPair_v1700__list)
  : seq_cond ULTxSwitchingBandPair_v1700__list y ->
 (ULTxSwitchingBandPair_v1700__cond (ULTxSwitchingBandPair_v1700__F2 y)) /\  ULTxSwitchingBandPair_v1700__F1 (ULTxSwitchingBandPair_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ULTxSwitchingBandPair_v1700__cond. simpl in *. auto.
 - simpl. unfold ULTxSwitchingBandPair_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ULTxSwitchingBandPair_v1700__Format : T_Format ULTxSwitchingBandPair_v1700__Type ULTxSwitchingBandPair_v1700__cond :=
        proj2_format  ULTxSwitchingBandPair_v1700__cond ULTxSwitchingBandPair_v1700__list__Format
    ULTxSwitchingBandPair_v1700__F1 ULTxSwitchingBandPair_v1700__F2 ULTxSwitchingBandPair_v1700__F1F2_cond  ULTxSwitchingBandPair_v1700__F1F2_cond2 ULTxSwitchingBandPair_v1700__F2F1_cond.
Opaque ULTxSwitchingBandPair_v1700__cond ULTxSwitchingBandPair_v1700__Format.

