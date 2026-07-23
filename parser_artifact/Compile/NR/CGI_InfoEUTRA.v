Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CellAccessRelatedInfo_EUTRA_EPC.

Opaque CellAccessRelatedInfo_EUTRA_EPC__cond CellAccessRelatedInfo_EUTRA_EPC__Format.

Require Import NR.CellAccessRelatedInfo_EUTRA_EPC.

Opaque CellAccessRelatedInfo_EUTRA_EPC__cond CellAccessRelatedInfo_EUTRA_EPC__Format.

Definition CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type := list CellAccessRelatedInfo_EUTRA_EPC__Type.

Lemma CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__helper1 : (0 <= 1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__cond (z : CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type) :=  (1 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and CellAccessRelatedInfo_EUTRA_EPC__cond z) .

Record CGI_InfoEUTRA__cgi_info_EPC__Type : Set :=
  make__CGI_InfoEUTRA__cgi_info_EPC__Type {
    CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_legacy : CellAccessRelatedInfo_EUTRA_EPC__Type ;
    CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list : option CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type ;
}.
Definition CGI_InfoEUTRA__cgi_info_EPC__list := (
 Nor CellAccessRelatedInfo_EUTRA_EPC__Type CellAccessRelatedInfo_EUTRA_EPC__cond ::
 Opt CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__cond ::
 nil).
Definition CGI_InfoEUTRA__cgi_info_EPC__cond z := 
  CellAccessRelatedInfo_EUTRA_EPC__cond (CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_legacy z) /\
  opt_cond CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__cond (CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list z) /\
  True.

Require Import NR.CellAccessRelatedInfo_EUTRA_5GC.

Opaque CellAccessRelatedInfo_EUTRA_5GC__cond CellAccessRelatedInfo_EUTRA_5GC__Format.

Definition CGI_InfoEUTRA__cgi_info_5GC__Type := list CellAccessRelatedInfo_EUTRA_5GC__Type.

Lemma CGI_InfoEUTRA__cgi_info_5GC__helper1 : (0 <= 1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma CGI_InfoEUTRA__cgi_info_5GC__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CGI_InfoEUTRA__cgi_info_5GC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CGI_InfoEUTRA__cgi_info_5GC__cond (z : CGI_InfoEUTRA__cgi_info_5GC__Type) :=  (1 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and CellAccessRelatedInfo_EUTRA_5GC__cond z) .

Require Import NR.FreqBandIndicatorEUTRA.

Opaque FreqBandIndicatorEUTRA__cond FreqBandIndicatorEUTRA__Format.

Require Import NR.MultiBandInfoListEUTRA.

Opaque MultiBandInfoListEUTRA__cond MultiBandInfoListEUTRA__Format.

Inductive CGI_InfoEUTRA__freqBandIndicatorPriority__Type : Set :=
 | CGI_InfoEUTRA__freqBandIndicatorPriority__true
.
Definition CGI_InfoEUTRA__freqBandIndicatorPriority__cond := (fun (_ : CGI_InfoEUTRA__freqBandIndicatorPriority__Type) => True).
Lemma CGI_InfoEUTRA__freqBandIndicatorPriority__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CGI_InfoEUTRA__freqBandIndicatorPriority__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CGI_InfoEUTRA__freqBandIndicatorPriority__nat__helper.

Definition CGI_InfoEUTRA__freqBandIndicatorPriority__F1 t :=
  match t with
  | CGI_InfoEUTRA__freqBandIndicatorPriority__true => 0
  end.
Definition CGI_InfoEUTRA__freqBandIndicatorPriority__F2 n :=
  match n with
  | 0 => CGI_InfoEUTRA__freqBandIndicatorPriority__true
  | _ => CGI_InfoEUTRA__freqBandIndicatorPriority__true
  end.
Lemma CGI_InfoEUTRA__freqBandIndicatorPriority__F1F2 : forall x : CGI_InfoEUTRA__freqBandIndicatorPriority__Type, (CGI_InfoEUTRA__freqBandIndicatorPriority__F1 x <= 0) /\ CGI_InfoEUTRA__freqBandIndicatorPriority__F2 (CGI_InfoEUTRA__freqBandIndicatorPriority__F1 x) = x. imp_solve. Qed.
Lemma CGI_InfoEUTRA__freqBandIndicatorPriority__F2F1 : forall (y : nat) (H : y <= 0), CGI_InfoEUTRA__freqBandIndicatorPriority__F1 (CGI_InfoEUTRA__freqBandIndicatorPriority__F2 y) = y. enum_solve H y. Qed.

Record CGI_InfoEUTRA__Type : Set :=
  make__CGI_InfoEUTRA__Type {
    CGI_InfoEUTRA__cgi_info_EPC : option CGI_InfoEUTRA__cgi_info_EPC__Type ;
    CGI_InfoEUTRA__cgi_info_5GC : option CGI_InfoEUTRA__cgi_info_5GC__Type ;
    CGI_InfoEUTRA__freqBandIndicator : FreqBandIndicatorEUTRA__Type ;
    CGI_InfoEUTRA__multiBandInfoList : option MultiBandInfoListEUTRA__Type ;
    CGI_InfoEUTRA__freqBandIndicatorPriority : option CGI_InfoEUTRA__freqBandIndicatorPriority__Type ;
}.
Definition CGI_InfoEUTRA__list := (
 Opt CGI_InfoEUTRA__cgi_info_EPC__Type CGI_InfoEUTRA__cgi_info_EPC__cond ::
 Opt CGI_InfoEUTRA__cgi_info_5GC__Type CGI_InfoEUTRA__cgi_info_5GC__cond ::
 Nor FreqBandIndicatorEUTRA__Type FreqBandIndicatorEUTRA__cond ::
 Opt MultiBandInfoListEUTRA__Type MultiBandInfoListEUTRA__cond ::
 Opt CGI_InfoEUTRA__freqBandIndicatorPriority__Type CGI_InfoEUTRA__freqBandIndicatorPriority__cond ::
 nil).
Definition CGI_InfoEUTRA__cond z := 
  opt_cond CGI_InfoEUTRA__cgi_info_EPC__cond (CGI_InfoEUTRA__cgi_info_EPC z) /\
  opt_cond CGI_InfoEUTRA__cgi_info_5GC__cond (CGI_InfoEUTRA__cgi_info_5GC z) /\
  FreqBandIndicatorEUTRA__cond (CGI_InfoEUTRA__freqBandIndicator z) /\
  opt_cond MultiBandInfoListEUTRA__cond (CGI_InfoEUTRA__multiBandInfoList z) /\
  opt_cond CGI_InfoEUTRA__freqBandIndicatorPriority__cond (CGI_InfoEUTRA__freqBandIndicatorPriority z) /\
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
Definition CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Format : T_Format CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__cond := seq_of_format CellAccessRelatedInfo_EUTRA_EPC__Format 1 maxPLMN CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__helper1 CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__helper2.

Opaque CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__cond CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Format.


Definition CGI_InfoEUTRA__cgi_info_EPC__Format_Type := Eval cbn in seq_format_prod CGI_InfoEUTRA__cgi_info_EPC__list.
Definition CGI_InfoEUTRA__cgi_info_EPC__Format_list : CGI_InfoEUTRA__cgi_info_EPC__Format_Type :=
  (CellAccessRelatedInfo_EUTRA_EPC__Format, (CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Format, unit_format)).
Definition CGI_InfoEUTRA__cgi_info_EPC__list__Format := (*Eval compute in *) seq_format CGI_InfoEUTRA__cgi_info_EPC__list CGI_InfoEUTRA__cgi_info_EPC__Format_list.
Definition CGI_InfoEUTRA__cgi_info_EPC__F1 z :=
  (CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_legacy z, (CGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list z, tt)).
Definition CGI_InfoEUTRA__cgi_info_EPC__F2 (y : seq_type CGI_InfoEUTRA__cgi_info_EPC__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CGI_InfoEUTRA__cgi_info_EPC__Type i0 i1
  end.
Lemma CGI_InfoEUTRA__cgi_info_EPC__F1F2_cond (z : CGI_InfoEUTRA__cgi_info_EPC__Type)
  : CGI_InfoEUTRA__cgi_info_EPC__cond z ->
  (seq_cond CGI_InfoEUTRA__cgi_info_EPC__list (CGI_InfoEUTRA__cgi_info_EPC__F1 z)).
intro H. unfold CGI_InfoEUTRA__cgi_info_EPC__cond in H. simpl. auto. Qed.
Lemma CGI_InfoEUTRA__cgi_info_EPC__F1F2_cond2 (z : CGI_InfoEUTRA__cgi_info_EPC__Type)
 : CGI_InfoEUTRA__cgi_info_EPC__F2 (CGI_InfoEUTRA__cgi_info_EPC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_InfoEUTRA__cgi_info_EPC__F2F1_cond (y : seq_type CGI_InfoEUTRA__cgi_info_EPC__list)
  : seq_cond CGI_InfoEUTRA__cgi_info_EPC__list y ->
 (CGI_InfoEUTRA__cgi_info_EPC__cond (CGI_InfoEUTRA__cgi_info_EPC__F2 y)) /\  CGI_InfoEUTRA__cgi_info_EPC__F1 (CGI_InfoEUTRA__cgi_info_EPC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_InfoEUTRA__cgi_info_EPC__cond. simpl in *. auto.
 - simpl. unfold CGI_InfoEUTRA__cgi_info_EPC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_InfoEUTRA__cgi_info_EPC__Format : T_Format CGI_InfoEUTRA__cgi_info_EPC__Type CGI_InfoEUTRA__cgi_info_EPC__cond :=
        proj2_format  CGI_InfoEUTRA__cgi_info_EPC__cond CGI_InfoEUTRA__cgi_info_EPC__list__Format
    CGI_InfoEUTRA__cgi_info_EPC__F1 CGI_InfoEUTRA__cgi_info_EPC__F2 CGI_InfoEUTRA__cgi_info_EPC__F1F2_cond  CGI_InfoEUTRA__cgi_info_EPC__F1F2_cond2 CGI_InfoEUTRA__cgi_info_EPC__F2F1_cond.
Opaque CGI_InfoEUTRA__cgi_info_EPC__cond CGI_InfoEUTRA__cgi_info_EPC__Format.

Definition CGI_InfoEUTRA__cgi_info_5GC__Format : T_Format CGI_InfoEUTRA__cgi_info_5GC__Type CGI_InfoEUTRA__cgi_info_5GC__cond := seq_of_format CellAccessRelatedInfo_EUTRA_5GC__Format 1 maxPLMN CGI_InfoEUTRA__cgi_info_5GC__helper1 CGI_InfoEUTRA__cgi_info_5GC__helper2.

Opaque CGI_InfoEUTRA__cgi_info_5GC__cond CGI_InfoEUTRA__cgi_info_5GC__Format.

Definition CGI_InfoEUTRA__freqBandIndicatorPriority__Format : T_Format CGI_InfoEUTRA__freqBandIndicatorPriority__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CGI_InfoEUTRA__freqBandIndicatorPriority__nat__Format CGI_InfoEUTRA__freqBandIndicatorPriority__F1 CGI_InfoEUTRA__freqBandIndicatorPriority__F2 CGI_InfoEUTRA__freqBandIndicatorPriority__F1F2 CGI_InfoEUTRA__freqBandIndicatorPriority__F2F1.

Opaque CGI_InfoEUTRA__freqBandIndicatorPriority__cond CGI_InfoEUTRA__freqBandIndicatorPriority__Format.


Definition CGI_InfoEUTRA__Format_Type := Eval cbn in seq_format_prod CGI_InfoEUTRA__list.
Definition CGI_InfoEUTRA__Format_list : CGI_InfoEUTRA__Format_Type :=
  (CGI_InfoEUTRA__cgi_info_EPC__Format, (CGI_InfoEUTRA__cgi_info_5GC__Format, (FreqBandIndicatorEUTRA__Format, (MultiBandInfoListEUTRA__Format, (CGI_InfoEUTRA__freqBandIndicatorPriority__Format, unit_format))))).
Definition CGI_InfoEUTRA__list__Format := (*Eval compute in *) seq_format CGI_InfoEUTRA__list CGI_InfoEUTRA__Format_list.
Definition CGI_InfoEUTRA__F1 z :=
  (CGI_InfoEUTRA__cgi_info_EPC z, (CGI_InfoEUTRA__cgi_info_5GC z, (CGI_InfoEUTRA__freqBandIndicator z, (CGI_InfoEUTRA__multiBandInfoList z, (CGI_InfoEUTRA__freqBandIndicatorPriority z, tt))))).
Definition CGI_InfoEUTRA__F2 (y : seq_type CGI_InfoEUTRA__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__CGI_InfoEUTRA__Type i0 i1 i2 i3 i4
  end.
Lemma CGI_InfoEUTRA__F1F2_cond (z : CGI_InfoEUTRA__Type)
  : CGI_InfoEUTRA__cond z ->
  (seq_cond CGI_InfoEUTRA__list (CGI_InfoEUTRA__F1 z)).
intro H. unfold CGI_InfoEUTRA__cond in H. simpl. auto. Qed.
Lemma CGI_InfoEUTRA__F1F2_cond2 (z : CGI_InfoEUTRA__Type)
 : CGI_InfoEUTRA__F2 (CGI_InfoEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_InfoEUTRA__F2F1_cond (y : seq_type CGI_InfoEUTRA__list)
  : seq_cond CGI_InfoEUTRA__list y ->
 (CGI_InfoEUTRA__cond (CGI_InfoEUTRA__F2 y)) /\  CGI_InfoEUTRA__F1 (CGI_InfoEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_InfoEUTRA__cond. simpl in *. auto.
 - simpl. unfold CGI_InfoEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_InfoEUTRA__Format : T_Format CGI_InfoEUTRA__Type CGI_InfoEUTRA__cond :=
        proj2_format  CGI_InfoEUTRA__cond CGI_InfoEUTRA__list__Format
    CGI_InfoEUTRA__F1 CGI_InfoEUTRA__F2 CGI_InfoEUTRA__F1F2_cond  CGI_InfoEUTRA__F1F2_cond2 CGI_InfoEUTRA__F2F1_cond.
Opaque CGI_InfoEUTRA__cond CGI_InfoEUTRA__Format.

