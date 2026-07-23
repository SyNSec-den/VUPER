Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_SpatialRelationInfoId.

Opaque PUCCH_SpatialRelationInfoId__cond PUCCH_SpatialRelationInfoId__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Require Import NR.PUCCH_SRS.

Opaque PUCCH_SRS__cond PUCCH_SRS__Format.


Inductive PUCCH_SpatialRelationInfo__referenceSignal__Type : Set :=
  | PUCCH_SpatialRelationInfo__referenceSignal__ssb_Index : SSB_Index__Type -> PUCCH_SpatialRelationInfo__referenceSignal__Type
  | PUCCH_SpatialRelationInfo__referenceSignal__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> PUCCH_SpatialRelationInfo__referenceSignal__Type
  | PUCCH_SpatialRelationInfo__referenceSignal__srs : PUCCH_SRS__Type -> PUCCH_SpatialRelationInfo__referenceSignal__Type
.
Definition PUCCH_SpatialRelationInfo__referenceSignal__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
typ_cons PUCCH_SRS__Type PUCCH_SRS__cond ::
 nil).
Definition PUCCH_SpatialRelationInfo__referenceSignal__cond (c : PUCCH_SpatialRelationInfo__referenceSignal__Type) := 
  match c with
  | PUCCH_SpatialRelationInfo__referenceSignal__ssb_Index t => SSB_Index__cond t 
  | PUCCH_SpatialRelationInfo__referenceSignal__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  | PUCCH_SpatialRelationInfo__referenceSignal__srs t => PUCCH_SRS__cond t 
  end.

Lemma PUCCH_SpatialRelationInfo__referenceSignal__len_helper1 : to_bit_sz (length PUCCH_SpatialRelationInfo__referenceSignal__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUCCH_SpatialRelationInfo__referenceSignal__len_helper2 : 2 <= length2 PUCCH_SpatialRelationInfo__referenceSignal__list.
 simpl. lia. Qed.
Require Import NR.PUCCH_PathlossReferenceRS_Id.

Opaque PUCCH_PathlossReferenceRS_Id__cond PUCCH_PathlossReferenceRS_Id__Format.

Require Import NR.P0_PUCCH_Id.

Opaque P0_PUCCH_Id__cond P0_PUCCH_Id__Format.

Inductive PUCCH_SpatialRelationInfo__closedLoopIndex__Type : Set :=
 | PUCCH_SpatialRelationInfo__closedLoopIndex__i0
 | PUCCH_SpatialRelationInfo__closedLoopIndex__i1
.
Definition PUCCH_SpatialRelationInfo__closedLoopIndex__cond := (fun (_ : PUCCH_SpatialRelationInfo__closedLoopIndex__Type) => True).
Lemma PUCCH_SpatialRelationInfo__closedLoopIndex__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_SpatialRelationInfo__closedLoopIndex__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_SpatialRelationInfo__closedLoopIndex__nat__helper.

Definition PUCCH_SpatialRelationInfo__closedLoopIndex__F1 t :=
  match t with
  | PUCCH_SpatialRelationInfo__closedLoopIndex__i0 => 0
  | PUCCH_SpatialRelationInfo__closedLoopIndex__i1 => 1
  end.
Definition PUCCH_SpatialRelationInfo__closedLoopIndex__F2 n :=
  match n with
  | 0 => PUCCH_SpatialRelationInfo__closedLoopIndex__i0
  | 1 => PUCCH_SpatialRelationInfo__closedLoopIndex__i1
  | _ => PUCCH_SpatialRelationInfo__closedLoopIndex__i0
  end.
Lemma PUCCH_SpatialRelationInfo__closedLoopIndex__F1F2 : forall x : PUCCH_SpatialRelationInfo__closedLoopIndex__Type, (PUCCH_SpatialRelationInfo__closedLoopIndex__F1 x <= 1) /\ PUCCH_SpatialRelationInfo__closedLoopIndex__F2 (PUCCH_SpatialRelationInfo__closedLoopIndex__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_SpatialRelationInfo__closedLoopIndex__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_SpatialRelationInfo__closedLoopIndex__F1 (PUCCH_SpatialRelationInfo__closedLoopIndex__F2 y) = y. enum_solve H y. Qed.

Record PUCCH_SpatialRelationInfo__Type : Set :=
  make__PUCCH_SpatialRelationInfo__Type {
    PUCCH_SpatialRelationInfo__pucch_SpatialRelationInfoId : PUCCH_SpatialRelationInfoId__Type ;
    PUCCH_SpatialRelationInfo__servingCellId : option ServCellIndex__Type ;
    PUCCH_SpatialRelationInfo__referenceSignal : PUCCH_SpatialRelationInfo__referenceSignal__Type ;
    PUCCH_SpatialRelationInfo__pucch_PathlossReferenceRS_Id : PUCCH_PathlossReferenceRS_Id__Type ;
    PUCCH_SpatialRelationInfo__p0_PUCCH_Id : P0_PUCCH_Id__Type ;
    PUCCH_SpatialRelationInfo__closedLoopIndex : PUCCH_SpatialRelationInfo__closedLoopIndex__Type ;
}.
Definition PUCCH_SpatialRelationInfo__list := (
 Nor PUCCH_SpatialRelationInfoId__Type PUCCH_SpatialRelationInfoId__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Nor PUCCH_SpatialRelationInfo__referenceSignal__Type PUCCH_SpatialRelationInfo__referenceSignal__cond ::
 Nor PUCCH_PathlossReferenceRS_Id__Type PUCCH_PathlossReferenceRS_Id__cond ::
 Nor P0_PUCCH_Id__Type P0_PUCCH_Id__cond ::
 Nor PUCCH_SpatialRelationInfo__closedLoopIndex__Type PUCCH_SpatialRelationInfo__closedLoopIndex__cond ::
 nil).
Definition PUCCH_SpatialRelationInfo__cond z := 
  PUCCH_SpatialRelationInfoId__cond (PUCCH_SpatialRelationInfo__pucch_SpatialRelationInfoId z) /\
  opt_cond ServCellIndex__cond (PUCCH_SpatialRelationInfo__servingCellId z) /\
  PUCCH_SpatialRelationInfo__referenceSignal__cond (PUCCH_SpatialRelationInfo__referenceSignal z) /\
  PUCCH_PathlossReferenceRS_Id__cond (PUCCH_SpatialRelationInfo__pucch_PathlossReferenceRS_Id z) /\
  P0_PUCCH_Id__cond (PUCCH_SpatialRelationInfo__p0_PUCCH_Id z) /\
  PUCCH_SpatialRelationInfo__closedLoopIndex__cond (PUCCH_SpatialRelationInfo__closedLoopIndex z) /\
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

Definition PUCCH_SpatialRelationInfo__referenceSignal__Format_Type := Eval cbn in get_formats PUCCH_SpatialRelationInfo__referenceSignal__list.
Definition PUCCH_SpatialRelationInfo__referenceSignal__Format_list : PUCCH_SpatialRelationInfo__referenceSignal__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, (PUCCH_SRS__Format, unit__Format))).
Definition PUCCH_SpatialRelationInfo__referenceSignal__list__Format := Eval compute in choice_format PUCCH_SpatialRelationInfo__referenceSignal__list PUCCH_SpatialRelationInfo__referenceSignal__len_helper1 PUCCH_SpatialRelationInfo__referenceSignal__len_helper2  PUCCH_SpatialRelationInfo__referenceSignal__Format_list.
Definition PUCCH_SpatialRelationInfo__referenceSignal__F1 (z : PUCCH_SpatialRelationInfo__referenceSignal__Type) : (choice PUCCH_SpatialRelationInfo__referenceSignal__list) :=
  match z with
   | PUCCH_SpatialRelationInfo__referenceSignal__ssb_Index t => existT _ 0 t
  | PUCCH_SpatialRelationInfo__referenceSignal__csi_RS_Index t => existT _ 1 t
  | PUCCH_SpatialRelationInfo__referenceSignal__srs t => existT _ 2 t
  end.
Definition PUCCH_SpatialRelationInfo__referenceSignal__g := (fun n => typ_set (get_nth_typ PUCCH_SpatialRelationInfo__referenceSignal__list n)).
Definition PUCCH_SpatialRelationInfo__referenceSignal__F2 (y : choice PUCCH_SpatialRelationInfo__referenceSignal__list) : PUCCH_SpatialRelationInfo__referenceSignal__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUCCH_SpatialRelationInfo__referenceSignal__g n -> PUCCH_SpatialRelationInfo__referenceSignal__Type) with
    | 0 => fun (t : SSB_Index__Type) => PUCCH_SpatialRelationInfo__referenceSignal__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => PUCCH_SpatialRelationInfo__referenceSignal__csi_RS_Index t 
    | 2 => fun (t : PUCCH_SRS__Type) => PUCCH_SpatialRelationInfo__referenceSignal__srs t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : PUCCH_SpatialRelationInfo__referenceSignal__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ PUCCH_SpatialRelationInfo__referenceSignal__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUCCH_SpatialRelationInfo__referenceSignal__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return PUCCH_SpatialRelationInfo__referenceSignal__Type with end) n0
           end t0).

Lemma PUCCH_SpatialRelationInfo__referenceSignal__helper2 :  forall (y : PUCCH_SpatialRelationInfo__referenceSignal__Type), PUCCH_SpatialRelationInfo__referenceSignal__cond y -> choice_cond PUCCH_SpatialRelationInfo__referenceSignal__list (PUCCH_SpatialRelationInfo__referenceSignal__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUCCH_SpatialRelationInfo__referenceSignal__helper3 :  forall (y : PUCCH_SpatialRelationInfo__referenceSignal__Type), PUCCH_SpatialRelationInfo__referenceSignal__F2 (PUCCH_SpatialRelationInfo__referenceSignal__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUCCH_SpatialRelationInfo__referenceSignal__helper4 : (forall b : choice PUCCH_SpatialRelationInfo__referenceSignal__list, choice_cond PUCCH_SpatialRelationInfo__referenceSignal__list b -> PUCCH_SpatialRelationInfo__referenceSignal__cond (PUCCH_SpatialRelationInfo__referenceSignal__F2 b) /\ PUCCH_SpatialRelationInfo__referenceSignal__F1 (PUCCH_SpatialRelationInfo__referenceSignal__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUCCH_SpatialRelationInfo__referenceSignal__F1 PUCCH_SpatialRelationInfo__referenceSignal__F2.
Definition PUCCH_SpatialRelationInfo__referenceSignal__Format : T_Format PUCCH_SpatialRelationInfo__referenceSignal__Type PUCCH_SpatialRelationInfo__referenceSignal__cond :=
  (* Eval compute in *) proj2_format PUCCH_SpatialRelationInfo__referenceSignal__cond PUCCH_SpatialRelationInfo__referenceSignal__list__Format PUCCH_SpatialRelationInfo__referenceSignal__F1 PUCCH_SpatialRelationInfo__referenceSignal__F2 PUCCH_SpatialRelationInfo__referenceSignal__helper2 PUCCH_SpatialRelationInfo__referenceSignal__helper3 PUCCH_SpatialRelationInfo__referenceSignal__helper4.
Opaque PUCCH_SpatialRelationInfo__referenceSignal__cond PUCCH_SpatialRelationInfo__referenceSignal__Format.

Definition PUCCH_SpatialRelationInfo__closedLoopIndex__Format : T_Format PUCCH_SpatialRelationInfo__closedLoopIndex__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_SpatialRelationInfo__closedLoopIndex__nat__Format PUCCH_SpatialRelationInfo__closedLoopIndex__F1 PUCCH_SpatialRelationInfo__closedLoopIndex__F2 PUCCH_SpatialRelationInfo__closedLoopIndex__F1F2 PUCCH_SpatialRelationInfo__closedLoopIndex__F2F1.

Opaque PUCCH_SpatialRelationInfo__closedLoopIndex__cond PUCCH_SpatialRelationInfo__closedLoopIndex__Format.


Definition PUCCH_SpatialRelationInfo__Format_Type := Eval cbn in seq_format_prod PUCCH_SpatialRelationInfo__list.
Definition PUCCH_SpatialRelationInfo__Format_list : PUCCH_SpatialRelationInfo__Format_Type :=
  (PUCCH_SpatialRelationInfoId__Format, (ServCellIndex__Format, (PUCCH_SpatialRelationInfo__referenceSignal__Format, (PUCCH_PathlossReferenceRS_Id__Format, (P0_PUCCH_Id__Format, (PUCCH_SpatialRelationInfo__closedLoopIndex__Format, unit_format)))))).
Definition PUCCH_SpatialRelationInfo__list__Format := (*Eval compute in *) seq_format PUCCH_SpatialRelationInfo__list PUCCH_SpatialRelationInfo__Format_list.
Definition PUCCH_SpatialRelationInfo__F1 z :=
  (PUCCH_SpatialRelationInfo__pucch_SpatialRelationInfoId z, (PUCCH_SpatialRelationInfo__servingCellId z, (PUCCH_SpatialRelationInfo__referenceSignal z, (PUCCH_SpatialRelationInfo__pucch_PathlossReferenceRS_Id z, (PUCCH_SpatialRelationInfo__p0_PUCCH_Id z, (PUCCH_SpatialRelationInfo__closedLoopIndex z, tt)))))).
Definition PUCCH_SpatialRelationInfo__F2 (y : seq_type PUCCH_SpatialRelationInfo__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__PUCCH_SpatialRelationInfo__Type i0 i1 i2 i3 i4 i5
  end.
Lemma PUCCH_SpatialRelationInfo__F1F2_cond (z : PUCCH_SpatialRelationInfo__Type)
  : PUCCH_SpatialRelationInfo__cond z ->
  (seq_cond PUCCH_SpatialRelationInfo__list (PUCCH_SpatialRelationInfo__F1 z)).
intro H. unfold PUCCH_SpatialRelationInfo__cond in H. simpl. auto. Qed.
Lemma PUCCH_SpatialRelationInfo__F1F2_cond2 (z : PUCCH_SpatialRelationInfo__Type)
 : PUCCH_SpatialRelationInfo__F2 (PUCCH_SpatialRelationInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_SpatialRelationInfo__F2F1_cond (y : seq_type PUCCH_SpatialRelationInfo__list)
  : seq_cond PUCCH_SpatialRelationInfo__list y ->
 (PUCCH_SpatialRelationInfo__cond (PUCCH_SpatialRelationInfo__F2 y)) /\  PUCCH_SpatialRelationInfo__F1 (PUCCH_SpatialRelationInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_SpatialRelationInfo__cond. simpl in *. auto.
 - simpl. unfold PUCCH_SpatialRelationInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_SpatialRelationInfo__Format : T_Format PUCCH_SpatialRelationInfo__Type PUCCH_SpatialRelationInfo__cond :=
        proj2_format  PUCCH_SpatialRelationInfo__cond PUCCH_SpatialRelationInfo__list__Format
    PUCCH_SpatialRelationInfo__F1 PUCCH_SpatialRelationInfo__F2 PUCCH_SpatialRelationInfo__F1F2_cond  PUCCH_SpatialRelationInfo__F1F2_cond2 PUCCH_SpatialRelationInfo__F2F1_cond.
Opaque PUCCH_SpatialRelationInfo__cond PUCCH_SpatialRelationInfo__Format.

