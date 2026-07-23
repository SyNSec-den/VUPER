Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRQ_Range.

Opaque RSRQ_Range__cond RSRQ_Range__Format.

Require Import NR.ResultsPerSSB_IndexList_r16.

Opaque ResultsPerSSB_IndexList_r16__cond ResultsPerSSB_IndexList_r16__Format.

Record MeasResultIdleNR_r16__measResultServingCell_r16__Type : Set :=
  make__MeasResultIdleNR_r16__measResultServingCell_r16__Type {
    MeasResultIdleNR_r16__measResultServingCell_r16__rsrp_Result_r16 : option RSRP_Range__Type ;
    MeasResultIdleNR_r16__measResultServingCell_r16__rsrq_Result_r16 : option RSRQ_Range__Type ;
    MeasResultIdleNR_r16__measResultServingCell_r16__resultsSSB_Indexes_r16 : option ResultsPerSSB_IndexList_r16__Type ;
}.
Definition MeasResultIdleNR_r16__measResultServingCell_r16__list := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRQ_Range__Type RSRQ_Range__cond ::
 Opt ResultsPerSSB_IndexList_r16__Type ResultsPerSSB_IndexList_r16__cond ::
 nil).
Definition MeasResultIdleNR_r16__measResultServingCell_r16__cond z := 
  opt_cond RSRP_Range__cond (MeasResultIdleNR_r16__measResultServingCell_r16__rsrp_Result_r16 z) /\
  opt_cond RSRQ_Range__cond (MeasResultIdleNR_r16__measResultServingCell_r16__rsrq_Result_r16 z) /\
  opt_cond ResultsPerSSB_IndexList_r16__cond (MeasResultIdleNR_r16__measResultServingCell_r16__resultsSSB_Indexes_r16 z) /\
  True.

Require Import NR.MeasResultsPerCarrierIdleNR_r16.

Opaque MeasResultsPerCarrierIdleNR_r16__cond MeasResultsPerCarrierIdleNR_r16__Format.

Definition MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type := list MeasResultsPerCarrierIdleNR_r16__Type.

Lemma MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__helper1 : (0 <= 1 <= maxFreqIdle_r16)%Z. unfold maxFreqIdle_r16.
 lia. Qed.
Lemma MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__helper2 : to_bit_sz (Z.to_nat (maxFreqIdle_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFreqIdle_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__cond (z : MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxFreqIdle_r16)%Z /\ (list_and MeasResultsPerCarrierIdleNR_r16__cond z) .

Record MeasResultIdleNR_r16__Type : Set :=
  make__MeasResultIdleNR_r16__Type {
    MeasResultIdleNR_r16__measResultServingCell_r16 : MeasResultIdleNR_r16__measResultServingCell_r16__Type ;
    MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16 : option MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type ;
}.
Definition MeasResultIdleNR_r16__root_list : list seq_elem := (
 Nor MeasResultIdleNR_r16__measResultServingCell_r16__Type MeasResultIdleNR_r16__measResultServingCell_r16__cond ::
 Opt MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__cond ::
 nil).
Definition MeasResultIdleNR_r16__ext_list : list typ := (
  nil).
Definition MeasResultIdleNR_r16__cond (z : MeasResultIdleNR_r16__Type) := 
(  MeasResultIdleNR_r16__measResultServingCell_r16__cond (MeasResultIdleNR_r16__measResultServingCell_r16 z) /\
  opt_cond MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__cond (MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16 z) /\
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

Definition MeasResultIdleNR_r16__measResultServingCell_r16__Format_Type := Eval cbn in seq_format_prod MeasResultIdleNR_r16__measResultServingCell_r16__list.
Definition MeasResultIdleNR_r16__measResultServingCell_r16__Format_list : MeasResultIdleNR_r16__measResultServingCell_r16__Format_Type :=
  (RSRP_Range__Format, (RSRQ_Range__Format, (ResultsPerSSB_IndexList_r16__Format, unit_format))).
Definition MeasResultIdleNR_r16__measResultServingCell_r16__list__Format := (*Eval compute in *) seq_format MeasResultIdleNR_r16__measResultServingCell_r16__list MeasResultIdleNR_r16__measResultServingCell_r16__Format_list.
Definition MeasResultIdleNR_r16__measResultServingCell_r16__F1 z :=
  (MeasResultIdleNR_r16__measResultServingCell_r16__rsrp_Result_r16 z, (MeasResultIdleNR_r16__measResultServingCell_r16__rsrq_Result_r16 z, (MeasResultIdleNR_r16__measResultServingCell_r16__resultsSSB_Indexes_r16 z, tt))).
Definition MeasResultIdleNR_r16__measResultServingCell_r16__F2 (y : seq_type MeasResultIdleNR_r16__measResultServingCell_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasResultIdleNR_r16__measResultServingCell_r16__Type i0 i1 i2
  end.
Lemma MeasResultIdleNR_r16__measResultServingCell_r16__F1F2_cond (z : MeasResultIdleNR_r16__measResultServingCell_r16__Type)
  : MeasResultIdleNR_r16__measResultServingCell_r16__cond z ->
  (seq_cond MeasResultIdleNR_r16__measResultServingCell_r16__list (MeasResultIdleNR_r16__measResultServingCell_r16__F1 z)).
intro H. unfold MeasResultIdleNR_r16__measResultServingCell_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultIdleNR_r16__measResultServingCell_r16__F1F2_cond2 (z : MeasResultIdleNR_r16__measResultServingCell_r16__Type)
 : MeasResultIdleNR_r16__measResultServingCell_r16__F2 (MeasResultIdleNR_r16__measResultServingCell_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultIdleNR_r16__measResultServingCell_r16__F2F1_cond (y : seq_type MeasResultIdleNR_r16__measResultServingCell_r16__list)
  : seq_cond MeasResultIdleNR_r16__measResultServingCell_r16__list y ->
 (MeasResultIdleNR_r16__measResultServingCell_r16__cond (MeasResultIdleNR_r16__measResultServingCell_r16__F2 y)) /\  MeasResultIdleNR_r16__measResultServingCell_r16__F1 (MeasResultIdleNR_r16__measResultServingCell_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultIdleNR_r16__measResultServingCell_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultIdleNR_r16__measResultServingCell_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultIdleNR_r16__measResultServingCell_r16__Format : T_Format MeasResultIdleNR_r16__measResultServingCell_r16__Type MeasResultIdleNR_r16__measResultServingCell_r16__cond :=
        proj2_format  MeasResultIdleNR_r16__measResultServingCell_r16__cond MeasResultIdleNR_r16__measResultServingCell_r16__list__Format
    MeasResultIdleNR_r16__measResultServingCell_r16__F1 MeasResultIdleNR_r16__measResultServingCell_r16__F2 MeasResultIdleNR_r16__measResultServingCell_r16__F1F2_cond  MeasResultIdleNR_r16__measResultServingCell_r16__F1F2_cond2 MeasResultIdleNR_r16__measResultServingCell_r16__F2F1_cond.
Opaque MeasResultIdleNR_r16__measResultServingCell_r16__cond MeasResultIdleNR_r16__measResultServingCell_r16__Format.

Definition MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Format : T_Format MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__cond := seq_of_format MeasResultsPerCarrierIdleNR_r16__Format 1 maxFreqIdle_r16 MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__helper1 MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__helper2.

Opaque MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__cond MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Format.


Definition MeasResultIdleNR_r16__root_Format_Type := Eval cbn in seq_format_prod MeasResultIdleNR_r16__root_list.
Definition MeasResultIdleNR_r16__root_Format_list : MeasResultIdleNR_r16__root_Format_Type :=
  (MeasResultIdleNR_r16__measResultServingCell_r16__Format, (MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Format, unit_format)).

Definition MeasResultIdleNR_r16__ext_Format_Type := Eval cbn in get_formats MeasResultIdleNR_r16__ext_list.
Definition MeasResultIdleNR_r16__ext_Format_list : MeasResultIdleNR_r16__ext_Format_Type :=
  unit__Format.

Definition MeasResultIdleNR_r16__list_type : Set := (seq_type MeasResultIdleNR_r16__root_list) * (seq_ext_type MeasResultIdleNR_r16__ext_list).
Definition MeasResultIdleNR_r16__list_cond (z : MeasResultIdleNR_r16__list_type) : Prop :=
        (seq_cond MeasResultIdleNR_r16__root_list (fst z)) /\ (seq_ext_cond MeasResultIdleNR_r16__ext_list (snd z)).
Definition MeasResultIdleNR_r16__list_format : T_Format MeasResultIdleNR_r16__list_type MeasResultIdleNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultIdleNR_r16__root_list MeasResultIdleNR_r16__root_Format_list MeasResultIdleNR_r16__ext_list MeasResultIdleNR_r16__ext_Format_list.

Opaque MeasResultIdleNR_r16__list_format.
Definition MeasResultIdleNR_r16__F1 (z : MeasResultIdleNR_r16__Type) : MeasResultIdleNR_r16__list_type :=
  (((MeasResultIdleNR_r16__measResultServingCell_r16 z, (MeasResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16 z, tt))), (
tt)).
Definition MeasResultIdleNR_r16__F2 (y : MeasResultIdleNR_r16__list_type) : MeasResultIdleNR_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__MeasResultIdleNR_r16__Type j0 j1
  end.
Definition MeasResultIdleNR_r16__helper1 : (forall a : MeasResultIdleNR_r16__Type, MeasResultIdleNR_r16__cond a -> MeasResultIdleNR_r16__list_cond (MeasResultIdleNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultIdleNR_r16__helper2 : (forall a : MeasResultIdleNR_r16__Type, MeasResultIdleNR_r16__F2 (MeasResultIdleNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultIdleNR_r16__helper3 : (forall b : MeasResultIdleNR_r16__list_type, MeasResultIdleNR_r16__list_cond b -> MeasResultIdleNR_r16__cond (MeasResultIdleNR_r16__F2 b) /\ MeasResultIdleNR_r16__F1 (MeasResultIdleNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultIdleNR_r16__cond, MeasResultIdleNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultIdleNR_r16__Format : T_Format MeasResultIdleNR_r16__Type MeasResultIdleNR_r16__cond :=
 proj2_format MeasResultIdleNR_r16__cond MeasResultIdleNR_r16__list_format  MeasResultIdleNR_r16__F1 MeasResultIdleNR_r16__F2 MeasResultIdleNR_r16__helper1 MeasResultIdleNR_r16__helper2 MeasResultIdleNR_r16__helper3.

Opaque MeasResultIdleNR_r16__cond MeasResultIdleNR_r16__Format.

