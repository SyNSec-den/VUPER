Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.AffectedCarrierFreqCombInfoMRDC.

Opaque AffectedCarrierFreqCombInfoMRDC__cond AffectedCarrierFreqCombInfoMRDC__Format.

Definition MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Type := list AffectedCarrierFreqCombInfoMRDC__Type.

Lemma MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__helper1 : (0 <= 1 <= maxNrofCombIDC)%Z. unfold maxNrofCombIDC.
 lia. Qed.
Lemma MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__helper2 : to_bit_sz (Z.to_nat (maxNrofCombIDC - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCombIDC - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__cond (z : MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCombIDC)%Z /\ (list_and AffectedCarrierFreqCombInfoMRDC__cond z) .

Record MRDC_AssistanceInfo__ext0O__Type : Set :=
  make__MRDC_AssistanceInfo__ext0O__Type {
    MRDC_AssistanceInfo__ext0O__overheatingAssistanceSCG_r16 : option octet_string ;
}.
Definition MRDC_AssistanceInfo__ext0O__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition MRDC_AssistanceInfo__ext0O__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MRDC_AssistanceInfo__ext0O__overheatingAssistanceSCG_r16 z) /\
  True.

Definition MRDC_AssistanceInfo__ext0__Type := MRDC_AssistanceInfo__ext0O__Type.
Definition MRDC_AssistanceInfo__ext0__cond := MRDC_AssistanceInfo__ext0O__cond.

Record MRDC_AssistanceInfo__ext1O__Type : Set :=
  make__MRDC_AssistanceInfo__ext1O__Type {
    MRDC_AssistanceInfo__ext1O__overheatingAssistanceSCG_FR2_2_r17 : option octet_string ;
}.
Definition MRDC_AssistanceInfo__ext1O__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition MRDC_AssistanceInfo__ext1O__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MRDC_AssistanceInfo__ext1O__overheatingAssistanceSCG_FR2_2_r17 z) /\
  True.

Definition MRDC_AssistanceInfo__ext1__Type := MRDC_AssistanceInfo__ext1O__Type.
Definition MRDC_AssistanceInfo__ext1__cond := MRDC_AssistanceInfo__ext1O__cond.

Record MRDC_AssistanceInfo__Type : Set :=
  make__MRDC_AssistanceInfo__Type {
    MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC : MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Type ;
    MRDC_AssistanceInfo__ext0 : option MRDC_AssistanceInfo__ext0__Type ;
    MRDC_AssistanceInfo__ext1 : option MRDC_AssistanceInfo__ext1__Type ;
}.
Definition MRDC_AssistanceInfo__root_list : list seq_elem := (
 Nor MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Type MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__cond ::
 nil).
Definition MRDC_AssistanceInfo__ext_list : list typ := (
  typ_cons MRDC_AssistanceInfo__ext0__Type MRDC_AssistanceInfo__ext0__cond ::
  typ_cons MRDC_AssistanceInfo__ext1__Type MRDC_AssistanceInfo__ext1__cond ::
  nil).
Definition MRDC_AssistanceInfo__cond (z : MRDC_AssistanceInfo__Type) := 
(  MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__cond (MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC z) /\
  True) /\ 
(  opt_cond MRDC_AssistanceInfo__ext0__cond (MRDC_AssistanceInfo__ext0 z) /\
  opt_cond MRDC_AssistanceInfo__ext1__cond (MRDC_AssistanceInfo__ext1 z) /\
  True).


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
Definition MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Format : T_Format MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Type MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__cond := seq_of_format AffectedCarrierFreqCombInfoMRDC__Format 1 maxNrofCombIDC MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__helper1 MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__helper2.

Opaque MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__cond MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Format.


Definition MRDC_AssistanceInfo__ext0O__Format_Type := Eval cbn in seq_format_prod MRDC_AssistanceInfo__ext0O__list.
Definition MRDC_AssistanceInfo__ext0O__Format_list : MRDC_AssistanceInfo__ext0O__Format_Type :=
  (octet_string_nc__Format, unit_format).
Definition MRDC_AssistanceInfo__ext0O__list__Format := (*Eval compute in *) seq_format MRDC_AssistanceInfo__ext0O__list MRDC_AssistanceInfo__ext0O__Format_list.
Definition MRDC_AssistanceInfo__ext0O__F1 z :=
  (MRDC_AssistanceInfo__ext0O__overheatingAssistanceSCG_r16 z, tt).
Definition MRDC_AssistanceInfo__ext0O__F2 (y : seq_type MRDC_AssistanceInfo__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MRDC_AssistanceInfo__ext0O__Type i0
  end.
Lemma MRDC_AssistanceInfo__ext0O__F1F2_cond (z : MRDC_AssistanceInfo__ext0O__Type)
  : MRDC_AssistanceInfo__ext0O__cond z ->
  (seq_cond MRDC_AssistanceInfo__ext0O__list (MRDC_AssistanceInfo__ext0O__F1 z)).
intro H. unfold MRDC_AssistanceInfo__ext0O__cond in H. simpl. auto. Qed.
Lemma MRDC_AssistanceInfo__ext0O__F1F2_cond2 (z : MRDC_AssistanceInfo__ext0O__Type)
 : MRDC_AssistanceInfo__ext0O__F2 (MRDC_AssistanceInfo__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRDC_AssistanceInfo__ext0O__F2F1_cond (y : seq_type MRDC_AssistanceInfo__ext0O__list)
  : seq_cond MRDC_AssistanceInfo__ext0O__list y ->
 (MRDC_AssistanceInfo__ext0O__cond (MRDC_AssistanceInfo__ext0O__F2 y)) /\  MRDC_AssistanceInfo__ext0O__F1 (MRDC_AssistanceInfo__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRDC_AssistanceInfo__ext0O__cond. simpl in *. auto.
 - simpl. unfold MRDC_AssistanceInfo__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRDC_AssistanceInfo__ext0O__Format : T_Format MRDC_AssistanceInfo__ext0O__Type MRDC_AssistanceInfo__ext0O__cond :=
        proj2_format  MRDC_AssistanceInfo__ext0O__cond MRDC_AssistanceInfo__ext0O__list__Format
    MRDC_AssistanceInfo__ext0O__F1 MRDC_AssistanceInfo__ext0O__F2 MRDC_AssistanceInfo__ext0O__F1F2_cond  MRDC_AssistanceInfo__ext0O__F1F2_cond2 MRDC_AssistanceInfo__ext0O__F2F1_cond.
Opaque MRDC_AssistanceInfo__ext0O__cond MRDC_AssistanceInfo__ext0O__Format.

Definition MRDC_AssistanceInfo__ext0__check_all_none (b : MRDC_AssistanceInfo__ext0O__Type) : bool :=
match b with 
  | make__MRDC_AssistanceInfo__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MRDC_AssistanceInfo__ext0__Format : T_Format MRDC_AssistanceInfo__ext0__Type MRDC_AssistanceInfo__ext0__cond :=
  restrict_add_format MRDC_AssistanceInfo__ext0__check_all_none MRDC_AssistanceInfo__ext0O__Format.

Opaque MRDC_AssistanceInfo__ext0__cond MRDC_AssistanceInfo__ext0__Format.


Definition MRDC_AssistanceInfo__ext1O__Format_Type := Eval cbn in seq_format_prod MRDC_AssistanceInfo__ext1O__list.
Definition MRDC_AssistanceInfo__ext1O__Format_list : MRDC_AssistanceInfo__ext1O__Format_Type :=
  (octet_string_nc__Format, unit_format).
Definition MRDC_AssistanceInfo__ext1O__list__Format := (*Eval compute in *) seq_format MRDC_AssistanceInfo__ext1O__list MRDC_AssistanceInfo__ext1O__Format_list.
Definition MRDC_AssistanceInfo__ext1O__F1 z :=
  (MRDC_AssistanceInfo__ext1O__overheatingAssistanceSCG_FR2_2_r17 z, tt).
Definition MRDC_AssistanceInfo__ext1O__F2 (y : seq_type MRDC_AssistanceInfo__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__MRDC_AssistanceInfo__ext1O__Type i0
  end.
Lemma MRDC_AssistanceInfo__ext1O__F1F2_cond (z : MRDC_AssistanceInfo__ext1O__Type)
  : MRDC_AssistanceInfo__ext1O__cond z ->
  (seq_cond MRDC_AssistanceInfo__ext1O__list (MRDC_AssistanceInfo__ext1O__F1 z)).
intro H. unfold MRDC_AssistanceInfo__ext1O__cond in H. simpl. auto. Qed.
Lemma MRDC_AssistanceInfo__ext1O__F1F2_cond2 (z : MRDC_AssistanceInfo__ext1O__Type)
 : MRDC_AssistanceInfo__ext1O__F2 (MRDC_AssistanceInfo__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRDC_AssistanceInfo__ext1O__F2F1_cond (y : seq_type MRDC_AssistanceInfo__ext1O__list)
  : seq_cond MRDC_AssistanceInfo__ext1O__list y ->
 (MRDC_AssistanceInfo__ext1O__cond (MRDC_AssistanceInfo__ext1O__F2 y)) /\  MRDC_AssistanceInfo__ext1O__F1 (MRDC_AssistanceInfo__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRDC_AssistanceInfo__ext1O__cond. simpl in *. auto.
 - simpl. unfold MRDC_AssistanceInfo__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRDC_AssistanceInfo__ext1O__Format : T_Format MRDC_AssistanceInfo__ext1O__Type MRDC_AssistanceInfo__ext1O__cond :=
        proj2_format  MRDC_AssistanceInfo__ext1O__cond MRDC_AssistanceInfo__ext1O__list__Format
    MRDC_AssistanceInfo__ext1O__F1 MRDC_AssistanceInfo__ext1O__F2 MRDC_AssistanceInfo__ext1O__F1F2_cond  MRDC_AssistanceInfo__ext1O__F1F2_cond2 MRDC_AssistanceInfo__ext1O__F2F1_cond.
Opaque MRDC_AssistanceInfo__ext1O__cond MRDC_AssistanceInfo__ext1O__Format.

Definition MRDC_AssistanceInfo__ext1__check_all_none (b : MRDC_AssistanceInfo__ext1O__Type) : bool :=
match b with 
  | make__MRDC_AssistanceInfo__ext1O__Type None  => false 
  | _ => true 
 end.
Definition MRDC_AssistanceInfo__ext1__Format : T_Format MRDC_AssistanceInfo__ext1__Type MRDC_AssistanceInfo__ext1__cond :=
  restrict_add_format MRDC_AssistanceInfo__ext1__check_all_none MRDC_AssistanceInfo__ext1O__Format.

Opaque MRDC_AssistanceInfo__ext1__cond MRDC_AssistanceInfo__ext1__Format.


Definition MRDC_AssistanceInfo__root_Format_Type := Eval cbn in seq_format_prod MRDC_AssistanceInfo__root_list.
Definition MRDC_AssistanceInfo__root_Format_list : MRDC_AssistanceInfo__root_Format_Type :=
  (MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC__Format, unit_format).

Definition MRDC_AssistanceInfo__ext_Format_Type := Eval cbn in get_formats MRDC_AssistanceInfo__ext_list.
Definition MRDC_AssistanceInfo__ext_Format_list : MRDC_AssistanceInfo__ext_Format_Type :=
  (MRDC_AssistanceInfo__ext0__Format, (MRDC_AssistanceInfo__ext1__Format, unit__Format)).

Definition MRDC_AssistanceInfo__list_type : Set := (seq_type MRDC_AssistanceInfo__root_list) * (seq_ext_type MRDC_AssistanceInfo__ext_list).
Definition MRDC_AssistanceInfo__list_cond (z : MRDC_AssistanceInfo__list_type) : Prop :=
        (seq_cond MRDC_AssistanceInfo__root_list (fst z)) /\ (seq_ext_cond MRDC_AssistanceInfo__ext_list (snd z)).
Definition MRDC_AssistanceInfo__list_format : T_Format MRDC_AssistanceInfo__list_type MRDC_AssistanceInfo__list_cond :=
 (* Eval compute in *) seq_ext_format MRDC_AssistanceInfo__root_list MRDC_AssistanceInfo__root_Format_list MRDC_AssistanceInfo__ext_list MRDC_AssistanceInfo__ext_Format_list.

Opaque MRDC_AssistanceInfo__list_format.
Definition MRDC_AssistanceInfo__F1 (z : MRDC_AssistanceInfo__Type) : MRDC_AssistanceInfo__list_type :=
  (((MRDC_AssistanceInfo__affectedCarrierFreqCombInfoListMRDC z, tt)), (
(MRDC_AssistanceInfo__ext0 z, (MRDC_AssistanceInfo__ext1 z, tt)))).
Definition MRDC_AssistanceInfo__F2 (y : MRDC_AssistanceInfo__list_type) : MRDC_AssistanceInfo__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__MRDC_AssistanceInfo__Type j0 i0 i1
  end.
Definition MRDC_AssistanceInfo__helper1 : (forall a : MRDC_AssistanceInfo__Type, MRDC_AssistanceInfo__cond a -> MRDC_AssistanceInfo__list_cond (MRDC_AssistanceInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MRDC_AssistanceInfo__helper2 : (forall a : MRDC_AssistanceInfo__Type, MRDC_AssistanceInfo__F2 (MRDC_AssistanceInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MRDC_AssistanceInfo__helper3 : (forall b : MRDC_AssistanceInfo__list_type, MRDC_AssistanceInfo__list_cond b -> MRDC_AssistanceInfo__cond (MRDC_AssistanceInfo__F2 b) /\ MRDC_AssistanceInfo__F1 (MRDC_AssistanceInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MRDC_AssistanceInfo__cond, MRDC_AssistanceInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MRDC_AssistanceInfo__Format : T_Format MRDC_AssistanceInfo__Type MRDC_AssistanceInfo__cond :=
 proj2_format MRDC_AssistanceInfo__cond MRDC_AssistanceInfo__list_format  MRDC_AssistanceInfo__F1 MRDC_AssistanceInfo__F2 MRDC_AssistanceInfo__helper1 MRDC_AssistanceInfo__helper2 MRDC_AssistanceInfo__helper3.

Opaque MRDC_AssistanceInfo__cond MRDC_AssistanceInfo__Format.

