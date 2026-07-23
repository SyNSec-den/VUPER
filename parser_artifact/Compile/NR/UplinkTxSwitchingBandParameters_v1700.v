Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__helper1 : (1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__Type := Z.
Definition UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__cond := (fun z => (1 <= z <= maxSimultaneousBands)%Z).
Inductive UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Type : Set :=
 | UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nonCoherent
 | UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__fullCoherent
.
Definition UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__cond := (fun (_ : UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Type) => True).
Lemma UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nat__helper.

Definition UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1 t :=
  match t with
  | UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nonCoherent => 0
  | UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__fullCoherent => 1
  end.
Definition UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F2 n :=
  match n with
  | 0 => UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nonCoherent
  | 1 => UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__fullCoherent
  | _ => UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nonCoherent
  end.
Lemma UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1F2 : forall x : UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Type, (UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1 x <= 1) /\ UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F2 (UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1 x) = x. imp_solve. Qed.
Lemma UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F2F1 : forall (y : nat) (H : y <= 1), UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1 (UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F2 y) = y. enum_solve H y. Qed.

Record UplinkTxSwitchingBandParameters_v1700__Type : Set :=
  make__UplinkTxSwitchingBandParameters_v1700__Type {
    UplinkTxSwitchingBandParameters_v1700__bandIndex_r17 : Z ;
    UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17 : option UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Type ;
}.
Definition UplinkTxSwitchingBandParameters_v1700__list := (
 Nor Z UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__cond ::
 Opt UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Type UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__cond ::
 nil).
Definition UplinkTxSwitchingBandParameters_v1700__cond z := 
  UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__cond (UplinkTxSwitchingBandParameters_v1700__bandIndex_r17 z) /\
  opt_cond UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__cond (UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17 z) /\
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
Definition UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__Format : T_Format Z UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__cond :=
 ranged_int_format (1) (maxSimultaneousBands) UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__helper1 UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__helper2.

Opaque UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__cond UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__Format.

Definition UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Format : T_Format UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__nat__Format UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1 UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F2 UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F1F2 UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__F2F1.

Opaque UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__cond UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Format.


Definition UplinkTxSwitchingBandParameters_v1700__Format_Type := Eval cbn in seq_format_prod UplinkTxSwitchingBandParameters_v1700__list.
Definition UplinkTxSwitchingBandParameters_v1700__Format_list : UplinkTxSwitchingBandParameters_v1700__Format_Type :=
  (UplinkTxSwitchingBandParameters_v1700__bandIndex_r17__Format, (UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17__Format, unit_format)).
Definition UplinkTxSwitchingBandParameters_v1700__list__Format := (*Eval compute in *) seq_format UplinkTxSwitchingBandParameters_v1700__list UplinkTxSwitchingBandParameters_v1700__Format_list.
Definition UplinkTxSwitchingBandParameters_v1700__F1 z :=
  (UplinkTxSwitchingBandParameters_v1700__bandIndex_r17 z, (UplinkTxSwitchingBandParameters_v1700__uplinkTxSwitching2T2T_PUSCH_TransCoherence_r17 z, tt)).
Definition UplinkTxSwitchingBandParameters_v1700__F2 (y : seq_type UplinkTxSwitchingBandParameters_v1700__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UplinkTxSwitchingBandParameters_v1700__Type i0 i1
  end.
Lemma UplinkTxSwitchingBandParameters_v1700__F1F2_cond (z : UplinkTxSwitchingBandParameters_v1700__Type)
  : UplinkTxSwitchingBandParameters_v1700__cond z ->
  (seq_cond UplinkTxSwitchingBandParameters_v1700__list (UplinkTxSwitchingBandParameters_v1700__F1 z)).
intro H. unfold UplinkTxSwitchingBandParameters_v1700__cond in H. simpl. auto. Qed.
Lemma UplinkTxSwitchingBandParameters_v1700__F1F2_cond2 (z : UplinkTxSwitchingBandParameters_v1700__Type)
 : UplinkTxSwitchingBandParameters_v1700__F2 (UplinkTxSwitchingBandParameters_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkTxSwitchingBandParameters_v1700__F2F1_cond (y : seq_type UplinkTxSwitchingBandParameters_v1700__list)
  : seq_cond UplinkTxSwitchingBandParameters_v1700__list y ->
 (UplinkTxSwitchingBandParameters_v1700__cond (UplinkTxSwitchingBandParameters_v1700__F2 y)) /\  UplinkTxSwitchingBandParameters_v1700__F1 (UplinkTxSwitchingBandParameters_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkTxSwitchingBandParameters_v1700__cond. simpl in *. auto.
 - simpl. unfold UplinkTxSwitchingBandParameters_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkTxSwitchingBandParameters_v1700__Format : T_Format UplinkTxSwitchingBandParameters_v1700__Type UplinkTxSwitchingBandParameters_v1700__cond :=
        proj2_format  UplinkTxSwitchingBandParameters_v1700__cond UplinkTxSwitchingBandParameters_v1700__list__Format
    UplinkTxSwitchingBandParameters_v1700__F1 UplinkTxSwitchingBandParameters_v1700__F2 UplinkTxSwitchingBandParameters_v1700__F1F2_cond  UplinkTxSwitchingBandParameters_v1700__F1F2_cond2 UplinkTxSwitchingBandParameters_v1700__F2F1_cond.
Opaque UplinkTxSwitchingBandParameters_v1700__cond UplinkTxSwitchingBandParameters_v1700__Format.

