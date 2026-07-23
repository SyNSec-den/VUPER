Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MultiFrequencyBandListNR_SIB.

Opaque MultiFrequencyBandListNR_SIB__cond MultiFrequencyBandListNR_SIB__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition FrequencyInfoUL_SIB__scs_SpecificCarrierList__Type := list SCS_SpecificCarrier__Type.

Lemma FrequencyInfoUL_SIB__scs_SpecificCarrierList__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma FrequencyInfoUL_SIB__scs_SpecificCarrierList__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FrequencyInfoUL_SIB__scs_SpecificCarrierList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FrequencyInfoUL_SIB__scs_SpecificCarrierList__cond (z : FrequencyInfoUL_SIB__scs_SpecificCarrierList__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Inductive FrequencyInfoUL_SIB__frequencyShift7p5khz__Type : Set :=
 | FrequencyInfoUL_SIB__frequencyShift7p5khz__true
.
Definition FrequencyInfoUL_SIB__frequencyShift7p5khz__cond := (fun (_ : FrequencyInfoUL_SIB__frequencyShift7p5khz__Type) => True).
Lemma FrequencyInfoUL_SIB__frequencyShift7p5khz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FrequencyInfoUL_SIB__frequencyShift7p5khz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FrequencyInfoUL_SIB__frequencyShift7p5khz__nat__helper.

Definition FrequencyInfoUL_SIB__frequencyShift7p5khz__F1 t :=
  match t with
  | FrequencyInfoUL_SIB__frequencyShift7p5khz__true => 0
  end.
Definition FrequencyInfoUL_SIB__frequencyShift7p5khz__F2 n :=
  match n with
  | 0 => FrequencyInfoUL_SIB__frequencyShift7p5khz__true
  | _ => FrequencyInfoUL_SIB__frequencyShift7p5khz__true
  end.
Lemma FrequencyInfoUL_SIB__frequencyShift7p5khz__F1F2 : forall x : FrequencyInfoUL_SIB__frequencyShift7p5khz__Type, (FrequencyInfoUL_SIB__frequencyShift7p5khz__F1 x <= 0) /\ FrequencyInfoUL_SIB__frequencyShift7p5khz__F2 (FrequencyInfoUL_SIB__frequencyShift7p5khz__F1 x) = x. imp_solve. Qed.
Lemma FrequencyInfoUL_SIB__frequencyShift7p5khz__F2F1 : forall (y : nat) (H : y <= 0), FrequencyInfoUL_SIB__frequencyShift7p5khz__F1 (FrequencyInfoUL_SIB__frequencyShift7p5khz__F2 y) = y. enum_solve H y. Qed.

Record FrequencyInfoUL_SIB__Type : Set :=
  make__FrequencyInfoUL_SIB__Type {
    FrequencyInfoUL_SIB__frequencyBandList : option MultiFrequencyBandListNR_SIB__Type ;
    FrequencyInfoUL_SIB__absoluteFrequencyPointA : option ARFCN_ValueNR__Type ;
    FrequencyInfoUL_SIB__scs_SpecificCarrierList : FrequencyInfoUL_SIB__scs_SpecificCarrierList__Type ;
    FrequencyInfoUL_SIB__p_Max : option P_Max__Type ;
    FrequencyInfoUL_SIB__frequencyShift7p5khz : option FrequencyInfoUL_SIB__frequencyShift7p5khz__Type ;
}.
Definition FrequencyInfoUL_SIB__root_list : list seq_elem := (
 Opt MultiFrequencyBandListNR_SIB__Type MultiFrequencyBandListNR_SIB__cond ::
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor FrequencyInfoUL_SIB__scs_SpecificCarrierList__Type FrequencyInfoUL_SIB__scs_SpecificCarrierList__cond ::
 Opt P_Max__Type P_Max__cond ::
 Opt FrequencyInfoUL_SIB__frequencyShift7p5khz__Type FrequencyInfoUL_SIB__frequencyShift7p5khz__cond ::
 nil).
Definition FrequencyInfoUL_SIB__ext_list : list typ := (
  nil).
Definition FrequencyInfoUL_SIB__cond (z : FrequencyInfoUL_SIB__Type) := 
(  opt_cond MultiFrequencyBandListNR_SIB__cond (FrequencyInfoUL_SIB__frequencyBandList z) /\
  opt_cond ARFCN_ValueNR__cond (FrequencyInfoUL_SIB__absoluteFrequencyPointA z) /\
  FrequencyInfoUL_SIB__scs_SpecificCarrierList__cond (FrequencyInfoUL_SIB__scs_SpecificCarrierList z) /\
  opt_cond P_Max__cond (FrequencyInfoUL_SIB__p_Max z) /\
  opt_cond FrequencyInfoUL_SIB__frequencyShift7p5khz__cond (FrequencyInfoUL_SIB__frequencyShift7p5khz z) /\
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
Definition FrequencyInfoUL_SIB__scs_SpecificCarrierList__Format : T_Format FrequencyInfoUL_SIB__scs_SpecificCarrierList__Type FrequencyInfoUL_SIB__scs_SpecificCarrierList__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs FrequencyInfoUL_SIB__scs_SpecificCarrierList__helper1 FrequencyInfoUL_SIB__scs_SpecificCarrierList__helper2.

Opaque FrequencyInfoUL_SIB__scs_SpecificCarrierList__cond FrequencyInfoUL_SIB__scs_SpecificCarrierList__Format.

Definition FrequencyInfoUL_SIB__frequencyShift7p5khz__Format : T_Format FrequencyInfoUL_SIB__frequencyShift7p5khz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FrequencyInfoUL_SIB__frequencyShift7p5khz__nat__Format FrequencyInfoUL_SIB__frequencyShift7p5khz__F1 FrequencyInfoUL_SIB__frequencyShift7p5khz__F2 FrequencyInfoUL_SIB__frequencyShift7p5khz__F1F2 FrequencyInfoUL_SIB__frequencyShift7p5khz__F2F1.

Opaque FrequencyInfoUL_SIB__frequencyShift7p5khz__cond FrequencyInfoUL_SIB__frequencyShift7p5khz__Format.


Definition FrequencyInfoUL_SIB__root_Format_Type := Eval cbn in seq_format_prod FrequencyInfoUL_SIB__root_list.
Definition FrequencyInfoUL_SIB__root_Format_list : FrequencyInfoUL_SIB__root_Format_Type :=
  (MultiFrequencyBandListNR_SIB__Format, (ARFCN_ValueNR__Format, (FrequencyInfoUL_SIB__scs_SpecificCarrierList__Format, (P_Max__Format, (FrequencyInfoUL_SIB__frequencyShift7p5khz__Format, unit_format))))).

Definition FrequencyInfoUL_SIB__ext_Format_Type := Eval cbn in get_formats FrequencyInfoUL_SIB__ext_list.
Definition FrequencyInfoUL_SIB__ext_Format_list : FrequencyInfoUL_SIB__ext_Format_Type :=
  unit__Format.

Definition FrequencyInfoUL_SIB__list_type : Set := (seq_type FrequencyInfoUL_SIB__root_list) * (seq_ext_type FrequencyInfoUL_SIB__ext_list).
Definition FrequencyInfoUL_SIB__list_cond (z : FrequencyInfoUL_SIB__list_type) : Prop :=
        (seq_cond FrequencyInfoUL_SIB__root_list (fst z)) /\ (seq_ext_cond FrequencyInfoUL_SIB__ext_list (snd z)).
Definition FrequencyInfoUL_SIB__list_format : T_Format FrequencyInfoUL_SIB__list_type FrequencyInfoUL_SIB__list_cond :=
 (* Eval compute in *) seq_ext_format FrequencyInfoUL_SIB__root_list FrequencyInfoUL_SIB__root_Format_list FrequencyInfoUL_SIB__ext_list FrequencyInfoUL_SIB__ext_Format_list.

Opaque FrequencyInfoUL_SIB__list_format.
Definition FrequencyInfoUL_SIB__F1 (z : FrequencyInfoUL_SIB__Type) : FrequencyInfoUL_SIB__list_type :=
  (((FrequencyInfoUL_SIB__frequencyBandList z, (FrequencyInfoUL_SIB__absoluteFrequencyPointA z, (FrequencyInfoUL_SIB__scs_SpecificCarrierList z, (FrequencyInfoUL_SIB__p_Max z, (FrequencyInfoUL_SIB__frequencyShift7p5khz z, tt)))))), (
tt)).
Definition FrequencyInfoUL_SIB__F2 (y : FrequencyInfoUL_SIB__list_type) : FrequencyInfoUL_SIB__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__FrequencyInfoUL_SIB__Type j0 j1 j2 j3 j4
  end.
Definition FrequencyInfoUL_SIB__helper1 : (forall a : FrequencyInfoUL_SIB__Type, FrequencyInfoUL_SIB__cond a -> FrequencyInfoUL_SIB__list_cond (FrequencyInfoUL_SIB__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FrequencyInfoUL_SIB__helper2 : (forall a : FrequencyInfoUL_SIB__Type, FrequencyInfoUL_SIB__F2 (FrequencyInfoUL_SIB__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FrequencyInfoUL_SIB__helper3 : (forall b : FrequencyInfoUL_SIB__list_type, FrequencyInfoUL_SIB__list_cond b -> FrequencyInfoUL_SIB__cond (FrequencyInfoUL_SIB__F2 b) /\ FrequencyInfoUL_SIB__F1 (FrequencyInfoUL_SIB__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FrequencyInfoUL_SIB__cond, FrequencyInfoUL_SIB__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FrequencyInfoUL_SIB__Format : T_Format FrequencyInfoUL_SIB__Type FrequencyInfoUL_SIB__cond :=
 proj2_format FrequencyInfoUL_SIB__cond FrequencyInfoUL_SIB__list_format  FrequencyInfoUL_SIB__F1 FrequencyInfoUL_SIB__F2 FrequencyInfoUL_SIB__helper1 FrequencyInfoUL_SIB__helper2 FrequencyInfoUL_SIB__helper3.

Opaque FrequencyInfoUL_SIB__cond FrequencyInfoUL_SIB__Format.

