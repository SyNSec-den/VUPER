Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Record SRS_SpatialRelationInfo__referenceSignal__srs__Type : Set :=
  make__SRS_SpatialRelationInfo__referenceSignal__srs__Type {
    SRS_SpatialRelationInfo__referenceSignal__srs__resourceId : SRS_ResourceId__Type ;
    SRS_SpatialRelationInfo__referenceSignal__srs__uplinkBWP : BWP_Id__Type ;
}.
Definition SRS_SpatialRelationInfo__referenceSignal__srs__list := (
 Nor SRS_ResourceId__Type SRS_ResourceId__cond ::
 Nor BWP_Id__Type BWP_Id__cond ::
 nil).
Definition SRS_SpatialRelationInfo__referenceSignal__srs__cond z := 
  SRS_ResourceId__cond (SRS_SpatialRelationInfo__referenceSignal__srs__resourceId z) /\
  BWP_Id__cond (SRS_SpatialRelationInfo__referenceSignal__srs__uplinkBWP z) /\
  True.


Inductive SRS_SpatialRelationInfo__referenceSignal__Type : Set :=
  | SRS_SpatialRelationInfo__referenceSignal__ssb_Index : SSB_Index__Type -> SRS_SpatialRelationInfo__referenceSignal__Type
  | SRS_SpatialRelationInfo__referenceSignal__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> SRS_SpatialRelationInfo__referenceSignal__Type
  | SRS_SpatialRelationInfo__referenceSignal__srs : SRS_SpatialRelationInfo__referenceSignal__srs__Type -> SRS_SpatialRelationInfo__referenceSignal__Type
.
Definition SRS_SpatialRelationInfo__referenceSignal__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
typ_cons SRS_SpatialRelationInfo__referenceSignal__srs__Type SRS_SpatialRelationInfo__referenceSignal__srs__cond ::
 nil).
Definition SRS_SpatialRelationInfo__referenceSignal__cond (c : SRS_SpatialRelationInfo__referenceSignal__Type) := 
  match c with
  | SRS_SpatialRelationInfo__referenceSignal__ssb_Index t => SSB_Index__cond t 
  | SRS_SpatialRelationInfo__referenceSignal__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  | SRS_SpatialRelationInfo__referenceSignal__srs t => SRS_SpatialRelationInfo__referenceSignal__srs__cond t 
  end.

Lemma SRS_SpatialRelationInfo__referenceSignal__len_helper1 : to_bit_sz (length SRS_SpatialRelationInfo__referenceSignal__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_SpatialRelationInfo__referenceSignal__len_helper2 : 2 <= length2 SRS_SpatialRelationInfo__referenceSignal__list.
 simpl. lia. Qed.
Record SRS_SpatialRelationInfo__Type : Set :=
  make__SRS_SpatialRelationInfo__Type {
    SRS_SpatialRelationInfo__servingCellId : option ServCellIndex__Type ;
    SRS_SpatialRelationInfo__referenceSignal : SRS_SpatialRelationInfo__referenceSignal__Type ;
}.
Definition SRS_SpatialRelationInfo__list := (
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Nor SRS_SpatialRelationInfo__referenceSignal__Type SRS_SpatialRelationInfo__referenceSignal__cond ::
 nil).
Definition SRS_SpatialRelationInfo__cond z := 
  opt_cond ServCellIndex__cond (SRS_SpatialRelationInfo__servingCellId z) /\
  SRS_SpatialRelationInfo__referenceSignal__cond (SRS_SpatialRelationInfo__referenceSignal z) /\
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

Definition SRS_SpatialRelationInfo__referenceSignal__srs__Format_Type := Eval cbn in seq_format_prod SRS_SpatialRelationInfo__referenceSignal__srs__list.
Definition SRS_SpatialRelationInfo__referenceSignal__srs__Format_list : SRS_SpatialRelationInfo__referenceSignal__srs__Format_Type :=
  (SRS_ResourceId__Format, (BWP_Id__Format, unit_format)).
Definition SRS_SpatialRelationInfo__referenceSignal__srs__list__Format := (*Eval compute in *) seq_format SRS_SpatialRelationInfo__referenceSignal__srs__list SRS_SpatialRelationInfo__referenceSignal__srs__Format_list.
Definition SRS_SpatialRelationInfo__referenceSignal__srs__F1 z :=
  (SRS_SpatialRelationInfo__referenceSignal__srs__resourceId z, (SRS_SpatialRelationInfo__referenceSignal__srs__uplinkBWP z, tt)).
Definition SRS_SpatialRelationInfo__referenceSignal__srs__F2 (y : seq_type SRS_SpatialRelationInfo__referenceSignal__srs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_SpatialRelationInfo__referenceSignal__srs__Type i0 i1
  end.
Lemma SRS_SpatialRelationInfo__referenceSignal__srs__F1F2_cond (z : SRS_SpatialRelationInfo__referenceSignal__srs__Type)
  : SRS_SpatialRelationInfo__referenceSignal__srs__cond z ->
  (seq_cond SRS_SpatialRelationInfo__referenceSignal__srs__list (SRS_SpatialRelationInfo__referenceSignal__srs__F1 z)).
intro H. unfold SRS_SpatialRelationInfo__referenceSignal__srs__cond in H. simpl. auto. Qed.
Lemma SRS_SpatialRelationInfo__referenceSignal__srs__F1F2_cond2 (z : SRS_SpatialRelationInfo__referenceSignal__srs__Type)
 : SRS_SpatialRelationInfo__referenceSignal__srs__F2 (SRS_SpatialRelationInfo__referenceSignal__srs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_SpatialRelationInfo__referenceSignal__srs__F2F1_cond (y : seq_type SRS_SpatialRelationInfo__referenceSignal__srs__list)
  : seq_cond SRS_SpatialRelationInfo__referenceSignal__srs__list y ->
 (SRS_SpatialRelationInfo__referenceSignal__srs__cond (SRS_SpatialRelationInfo__referenceSignal__srs__F2 y)) /\  SRS_SpatialRelationInfo__referenceSignal__srs__F1 (SRS_SpatialRelationInfo__referenceSignal__srs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_SpatialRelationInfo__referenceSignal__srs__cond. simpl in *. auto.
 - simpl. unfold SRS_SpatialRelationInfo__referenceSignal__srs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_SpatialRelationInfo__referenceSignal__srs__Format : T_Format SRS_SpatialRelationInfo__referenceSignal__srs__Type SRS_SpatialRelationInfo__referenceSignal__srs__cond :=
        proj2_format  SRS_SpatialRelationInfo__referenceSignal__srs__cond SRS_SpatialRelationInfo__referenceSignal__srs__list__Format
    SRS_SpatialRelationInfo__referenceSignal__srs__F1 SRS_SpatialRelationInfo__referenceSignal__srs__F2 SRS_SpatialRelationInfo__referenceSignal__srs__F1F2_cond  SRS_SpatialRelationInfo__referenceSignal__srs__F1F2_cond2 SRS_SpatialRelationInfo__referenceSignal__srs__F2F1_cond.
Opaque SRS_SpatialRelationInfo__referenceSignal__srs__cond SRS_SpatialRelationInfo__referenceSignal__srs__Format.


Definition SRS_SpatialRelationInfo__referenceSignal__Format_Type := Eval cbn in get_formats SRS_SpatialRelationInfo__referenceSignal__list.
Definition SRS_SpatialRelationInfo__referenceSignal__Format_list : SRS_SpatialRelationInfo__referenceSignal__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, (SRS_SpatialRelationInfo__referenceSignal__srs__Format, unit__Format))).
Definition SRS_SpatialRelationInfo__referenceSignal__list__Format := Eval compute in choice_format SRS_SpatialRelationInfo__referenceSignal__list SRS_SpatialRelationInfo__referenceSignal__len_helper1 SRS_SpatialRelationInfo__referenceSignal__len_helper2  SRS_SpatialRelationInfo__referenceSignal__Format_list.
Definition SRS_SpatialRelationInfo__referenceSignal__F1 (z : SRS_SpatialRelationInfo__referenceSignal__Type) : (choice SRS_SpatialRelationInfo__referenceSignal__list) :=
  match z with
   | SRS_SpatialRelationInfo__referenceSignal__ssb_Index t => existT _ 0 t
  | SRS_SpatialRelationInfo__referenceSignal__csi_RS_Index t => existT _ 1 t
  | SRS_SpatialRelationInfo__referenceSignal__srs t => existT _ 2 t
  end.
Definition SRS_SpatialRelationInfo__referenceSignal__g := (fun n => typ_set (get_nth_typ SRS_SpatialRelationInfo__referenceSignal__list n)).
Definition SRS_SpatialRelationInfo__referenceSignal__F2 (y : choice SRS_SpatialRelationInfo__referenceSignal__list) : SRS_SpatialRelationInfo__referenceSignal__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_SpatialRelationInfo__referenceSignal__g n -> SRS_SpatialRelationInfo__referenceSignal__Type) with
    | 0 => fun (t : SSB_Index__Type) => SRS_SpatialRelationInfo__referenceSignal__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => SRS_SpatialRelationInfo__referenceSignal__csi_RS_Index t 
    | 2 => fun (t : SRS_SpatialRelationInfo__referenceSignal__srs__Type) => SRS_SpatialRelationInfo__referenceSignal__srs t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_SpatialRelationInfo__referenceSignal__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_SpatialRelationInfo__referenceSignal__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_SpatialRelationInfo__referenceSignal__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_SpatialRelationInfo__referenceSignal__Type with end) n0
           end t0).

Lemma SRS_SpatialRelationInfo__referenceSignal__helper2 :  forall (y : SRS_SpatialRelationInfo__referenceSignal__Type), SRS_SpatialRelationInfo__referenceSignal__cond y -> choice_cond SRS_SpatialRelationInfo__referenceSignal__list (SRS_SpatialRelationInfo__referenceSignal__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_SpatialRelationInfo__referenceSignal__helper3 :  forall (y : SRS_SpatialRelationInfo__referenceSignal__Type), SRS_SpatialRelationInfo__referenceSignal__F2 (SRS_SpatialRelationInfo__referenceSignal__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_SpatialRelationInfo__referenceSignal__helper4 : (forall b : choice SRS_SpatialRelationInfo__referenceSignal__list, choice_cond SRS_SpatialRelationInfo__referenceSignal__list b -> SRS_SpatialRelationInfo__referenceSignal__cond (SRS_SpatialRelationInfo__referenceSignal__F2 b) /\ SRS_SpatialRelationInfo__referenceSignal__F1 (SRS_SpatialRelationInfo__referenceSignal__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_SpatialRelationInfo__referenceSignal__F1 SRS_SpatialRelationInfo__referenceSignal__F2.
Definition SRS_SpatialRelationInfo__referenceSignal__Format : T_Format SRS_SpatialRelationInfo__referenceSignal__Type SRS_SpatialRelationInfo__referenceSignal__cond :=
  (* Eval compute in *) proj2_format SRS_SpatialRelationInfo__referenceSignal__cond SRS_SpatialRelationInfo__referenceSignal__list__Format SRS_SpatialRelationInfo__referenceSignal__F1 SRS_SpatialRelationInfo__referenceSignal__F2 SRS_SpatialRelationInfo__referenceSignal__helper2 SRS_SpatialRelationInfo__referenceSignal__helper3 SRS_SpatialRelationInfo__referenceSignal__helper4.
Opaque SRS_SpatialRelationInfo__referenceSignal__cond SRS_SpatialRelationInfo__referenceSignal__Format.


Definition SRS_SpatialRelationInfo__Format_Type := Eval cbn in seq_format_prod SRS_SpatialRelationInfo__list.
Definition SRS_SpatialRelationInfo__Format_list : SRS_SpatialRelationInfo__Format_Type :=
  (ServCellIndex__Format, (SRS_SpatialRelationInfo__referenceSignal__Format, unit_format)).
Definition SRS_SpatialRelationInfo__list__Format := (*Eval compute in *) seq_format SRS_SpatialRelationInfo__list SRS_SpatialRelationInfo__Format_list.
Definition SRS_SpatialRelationInfo__F1 z :=
  (SRS_SpatialRelationInfo__servingCellId z, (SRS_SpatialRelationInfo__referenceSignal z, tt)).
Definition SRS_SpatialRelationInfo__F2 (y : seq_type SRS_SpatialRelationInfo__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_SpatialRelationInfo__Type i0 i1
  end.
Lemma SRS_SpatialRelationInfo__F1F2_cond (z : SRS_SpatialRelationInfo__Type)
  : SRS_SpatialRelationInfo__cond z ->
  (seq_cond SRS_SpatialRelationInfo__list (SRS_SpatialRelationInfo__F1 z)).
intro H. unfold SRS_SpatialRelationInfo__cond in H. simpl. auto. Qed.
Lemma SRS_SpatialRelationInfo__F1F2_cond2 (z : SRS_SpatialRelationInfo__Type)
 : SRS_SpatialRelationInfo__F2 (SRS_SpatialRelationInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_SpatialRelationInfo__F2F1_cond (y : seq_type SRS_SpatialRelationInfo__list)
  : seq_cond SRS_SpatialRelationInfo__list y ->
 (SRS_SpatialRelationInfo__cond (SRS_SpatialRelationInfo__F2 y)) /\  SRS_SpatialRelationInfo__F1 (SRS_SpatialRelationInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_SpatialRelationInfo__cond. simpl in *. auto.
 - simpl. unfold SRS_SpatialRelationInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_SpatialRelationInfo__Format : T_Format SRS_SpatialRelationInfo__Type SRS_SpatialRelationInfo__cond :=
        proj2_format  SRS_SpatialRelationInfo__cond SRS_SpatialRelationInfo__list__Format
    SRS_SpatialRelationInfo__F1 SRS_SpatialRelationInfo__F2 SRS_SpatialRelationInfo__F1F2_cond  SRS_SpatialRelationInfo__F1F2_cond2 SRS_SpatialRelationInfo__F2F1_cond.
Opaque SRS_SpatialRelationInfo__cond SRS_SpatialRelationInfo__Format.

