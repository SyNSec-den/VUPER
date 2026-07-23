Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma ULTxSwitchingBandPair_r16__bandIndexUL1_r16__helper1 : (1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma ULTxSwitchingBandPair_r16__bandIndexUL1_r16__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ULTxSwitchingBandPair_r16__bandIndexUL1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ULTxSwitchingBandPair_r16__bandIndexUL1_r16__Type := Z.
Definition ULTxSwitchingBandPair_r16__bandIndexUL1_r16__cond := (fun z => (1 <= z <= maxSimultaneousBands)%Z).
Lemma ULTxSwitchingBandPair_r16__bandIndexUL2_r16__helper1 : (1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma ULTxSwitchingBandPair_r16__bandIndexUL2_r16__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ULTxSwitchingBandPair_r16__bandIndexUL2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ULTxSwitchingBandPair_r16__bandIndexUL2_r16__Type := Z.
Definition ULTxSwitchingBandPair_r16__bandIndexUL2_r16__cond := (fun z => (1 <= z <= maxSimultaneousBands)%Z).
Inductive ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Type : Set :=
 | ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n35us
 | ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n140us
 | ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n210us
.
Definition ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__cond := (fun (_ : ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Type) => True).
Lemma ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__nat__helper.

Definition ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1 t :=
  match t with
  | ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n35us => 0
  | ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n140us => 1
  | ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n210us => 2
  end.
Definition ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F2 n :=
  match n with
  | 0 => ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n35us
  | 1 => ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n140us
  | 2 => ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n210us
  | _ => ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__n35us
  end.
Lemma ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1F2 : forall x : ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Type, (ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1 x <= 2) /\ ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F2 (ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1 x) = x. imp_solve. Qed.
Lemma ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F2F1 : forall (y : nat) (H : y <= 2), ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1 (ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F2 y) = y. enum_solve H y. Qed.

Lemma ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Type := bit_string.
Definition ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= maxSimultaneousBands)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record ULTxSwitchingBandPair_r16__Type : Set :=
  make__ULTxSwitchingBandPair_r16__Type {
    ULTxSwitchingBandPair_r16__bandIndexUL1_r16 : Z ;
    ULTxSwitchingBandPair_r16__bandIndexUL2_r16 : Z ;
    ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16 : ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Type ;
    ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16 : option ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Type ;
}.
Definition ULTxSwitchingBandPair_r16__list := (
 Nor Z ULTxSwitchingBandPair_r16__bandIndexUL1_r16__cond ::
 Nor Z ULTxSwitchingBandPair_r16__bandIndexUL2_r16__cond ::
 Nor ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Type ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__cond ::
 Opt ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Type ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__cond ::
 nil).
Definition ULTxSwitchingBandPair_r16__cond z := 
  ULTxSwitchingBandPair_r16__bandIndexUL1_r16__cond (ULTxSwitchingBandPair_r16__bandIndexUL1_r16 z) /\
  ULTxSwitchingBandPair_r16__bandIndexUL2_r16__cond (ULTxSwitchingBandPair_r16__bandIndexUL2_r16 z) /\
  ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__cond (ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16 z) /\
  opt_cond ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__cond (ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16 z) /\
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
Definition ULTxSwitchingBandPair_r16__bandIndexUL1_r16__Format : T_Format Z ULTxSwitchingBandPair_r16__bandIndexUL1_r16__cond :=
 ranged_int_format (1) (maxSimultaneousBands) ULTxSwitchingBandPair_r16__bandIndexUL1_r16__helper1 ULTxSwitchingBandPair_r16__bandIndexUL1_r16__helper2.

Opaque ULTxSwitchingBandPair_r16__bandIndexUL1_r16__cond ULTxSwitchingBandPair_r16__bandIndexUL1_r16__Format.

Definition ULTxSwitchingBandPair_r16__bandIndexUL2_r16__Format : T_Format Z ULTxSwitchingBandPair_r16__bandIndexUL2_r16__cond :=
 ranged_int_format (1) (maxSimultaneousBands) ULTxSwitchingBandPair_r16__bandIndexUL2_r16__helper1 ULTxSwitchingBandPair_r16__bandIndexUL2_r16__helper2.

Opaque ULTxSwitchingBandPair_r16__bandIndexUL2_r16__cond ULTxSwitchingBandPair_r16__bandIndexUL2_r16__Format.

Definition ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Format : T_Format ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__nat__Format ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1 ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F2 ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F1F2 ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__F2F1.

Opaque ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__cond ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Format.

Definition ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Format : T_Format ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Type ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__cond := (* Eval compute in *) bit_string_ranged_format 1 maxSimultaneousBands ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__helper1 ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__helper2.
Opaque ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__cond ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Format.


Definition ULTxSwitchingBandPair_r16__Format_Type := Eval cbn in seq_format_prod ULTxSwitchingBandPair_r16__list.
Definition ULTxSwitchingBandPair_r16__Format_list : ULTxSwitchingBandPair_r16__Format_Type :=
  (ULTxSwitchingBandPair_r16__bandIndexUL1_r16__Format, (ULTxSwitchingBandPair_r16__bandIndexUL2_r16__Format, (ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16__Format, (ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16__Format, unit_format)))).
Definition ULTxSwitchingBandPair_r16__list__Format := (*Eval compute in *) seq_format ULTxSwitchingBandPair_r16__list ULTxSwitchingBandPair_r16__Format_list.
Definition ULTxSwitchingBandPair_r16__F1 z :=
  (ULTxSwitchingBandPair_r16__bandIndexUL1_r16 z, (ULTxSwitchingBandPair_r16__bandIndexUL2_r16 z, (ULTxSwitchingBandPair_r16__uplinkTxSwitchingPeriod_r16 z, (ULTxSwitchingBandPair_r16__uplinkTxSwitching_DL_Interruption_r16 z, tt)))).
Definition ULTxSwitchingBandPair_r16__F2 (y : seq_type ULTxSwitchingBandPair_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ULTxSwitchingBandPair_r16__Type i0 i1 i2 i3
  end.
Lemma ULTxSwitchingBandPair_r16__F1F2_cond (z : ULTxSwitchingBandPair_r16__Type)
  : ULTxSwitchingBandPair_r16__cond z ->
  (seq_cond ULTxSwitchingBandPair_r16__list (ULTxSwitchingBandPair_r16__F1 z)).
intro H. unfold ULTxSwitchingBandPair_r16__cond in H. simpl. auto. Qed.
Lemma ULTxSwitchingBandPair_r16__F1F2_cond2 (z : ULTxSwitchingBandPair_r16__Type)
 : ULTxSwitchingBandPair_r16__F2 (ULTxSwitchingBandPair_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ULTxSwitchingBandPair_r16__F2F1_cond (y : seq_type ULTxSwitchingBandPair_r16__list)
  : seq_cond ULTxSwitchingBandPair_r16__list y ->
 (ULTxSwitchingBandPair_r16__cond (ULTxSwitchingBandPair_r16__F2 y)) /\  ULTxSwitchingBandPair_r16__F1 (ULTxSwitchingBandPair_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ULTxSwitchingBandPair_r16__cond. simpl in *. auto.
 - simpl. unfold ULTxSwitchingBandPair_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ULTxSwitchingBandPair_r16__Format : T_Format ULTxSwitchingBandPair_r16__Type ULTxSwitchingBandPair_r16__cond :=
        proj2_format  ULTxSwitchingBandPair_r16__cond ULTxSwitchingBandPair_r16__list__Format
    ULTxSwitchingBandPair_r16__F1 ULTxSwitchingBandPair_r16__F2 ULTxSwitchingBandPair_r16__F1F2_cond  ULTxSwitchingBandPair_r16__F1F2_cond2 ULTxSwitchingBandPair_r16__F2F1_cond.
Opaque ULTxSwitchingBandPair_r16__cond ULTxSwitchingBandPair_r16__Format.

