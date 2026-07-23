Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Require Import NR.NR_DL_PRS_ResourceID_r17.

Opaque NR_DL_PRS_ResourceID_r17__cond NR_DL_PRS_ResourceID_r17__Format.

Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Record SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type : Set :=
  make__SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type {
    SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__resourceId : SRS_ResourceId__Type ;
    SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__uplinkBWP : BWP_Id__Type ;
}.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list := (
 Nor SRS_ResourceId__Type SRS_ResourceId__cond ::
 Nor BWP_Id__Type BWP_Id__cond ::
 nil).
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond z := 
  SRS_ResourceId__cond (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__resourceId z) /\
  BWP_Id__cond (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__uplinkBWP z) /\
  True.


Inductive SpatialRelationInfo_PDC_r17__referenceSignal__root__Type : Set :=
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__ssb_Index : SSB_Index__Type -> SpatialRelationInfo_PDC_r17__referenceSignal__root__Type
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> SpatialRelationInfo_PDC_r17__referenceSignal__root__Type
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__dl_PRS_PDC : NR_DL_PRS_ResourceID_r17__Type -> SpatialRelationInfo_PDC_r17__referenceSignal__root__Type
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__srs : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type -> SpatialRelationInfo_PDC_r17__referenceSignal__root__Type
.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
typ_cons NR_DL_PRS_ResourceID_r17__Type NR_DL_PRS_ResourceID_r17__cond ::
typ_cons SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond ::
 nil).
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__cond (c : SpatialRelationInfo_PDC_r17__referenceSignal__root__Type) := 
  match c with
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__ssb_Index t => SSB_Index__cond t 
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__dl_PRS_PDC t => NR_DL_PRS_ResourceID_r17__cond t 
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__srs t => SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond t 
  end.

Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__len_helper1 : to_bit_sz (length SpatialRelationInfo_PDC_r17__referenceSignal__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__len_helper2 : 2 <= length2 SpatialRelationInfo_PDC_r17__referenceSignal__root__list.
 simpl. lia. Qed.

Definition SpatialRelationInfo_PDC_r17__referenceSignal__ext__Type : Set := Empty_set.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__ext__cond (c : SpatialRelationInfo_PDC_r17__referenceSignal__ext__Type) := True.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__Type : Set := SpatialRelationInfo_PDC_r17__referenceSignal__root__Type + SpatialRelationInfo_PDC_r17__referenceSignal__ext__Type.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__cond :=
  sum_cond SpatialRelationInfo_PDC_r17__referenceSignal__root__cond SpatialRelationInfo_PDC_r17__referenceSignal__ext__cond.
Record SpatialRelationInfo_PDC_r17__Type : Set :=
  make__SpatialRelationInfo_PDC_r17__Type {
    SpatialRelationInfo_PDC_r17__referenceSignal : SpatialRelationInfo_PDC_r17__referenceSignal__Type ;
}.
Definition SpatialRelationInfo_PDC_r17__root_list : list seq_elem := (
 Nor SpatialRelationInfo_PDC_r17__referenceSignal__Type SpatialRelationInfo_PDC_r17__referenceSignal__cond ::
 nil).
Definition SpatialRelationInfo_PDC_r17__ext_list : list typ := (
  nil).
Definition SpatialRelationInfo_PDC_r17__cond (z : SpatialRelationInfo_PDC_r17__Type) := 
(  SpatialRelationInfo_PDC_r17__referenceSignal__cond (SpatialRelationInfo_PDC_r17__referenceSignal z) /\
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

Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format_Type := Eval cbn in seq_format_prod SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format_list : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format_Type :=
  (SRS_ResourceId__Format, (BWP_Id__Format, unit_format)).
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list__Format := (*Eval compute in *) seq_format SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format_list.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1 z :=
  (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__resourceId z, (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__uplinkBWP z, tt)).
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2 (y : seq_type SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type i0 i1
  end.
Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1F2_cond (z : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type)
  : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond z ->
  (seq_cond SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1 z)).
intro H. unfold SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond in H. simpl. auto. Qed.
Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1F2_cond2 (z : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type)
 : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2 (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2F1_cond (y : seq_type SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list)
  : seq_cond SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list y ->
 (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2 y)) /\  SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1 (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond. simpl in *. auto.
 - simpl. unfold SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format : T_Format SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond :=
        proj2_format  SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__list__Format
    SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1 SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2 SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1F2_cond  SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F1F2_cond2 SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__F2F1_cond.
Opaque SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__cond SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format.


Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__Format_Type := Eval cbn in get_formats SpatialRelationInfo_PDC_r17__referenceSignal__root__list.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__Format_list : SpatialRelationInfo_PDC_r17__referenceSignal__root__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, (NR_DL_PRS_ResourceID_r17__Format, (SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Format, unit__Format)))).
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__list__Format := Eval compute in choice_format SpatialRelationInfo_PDC_r17__referenceSignal__root__list SpatialRelationInfo_PDC_r17__referenceSignal__root__len_helper1 SpatialRelationInfo_PDC_r17__referenceSignal__root__len_helper2  SpatialRelationInfo_PDC_r17__referenceSignal__root__Format_list.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__F1 (z : SpatialRelationInfo_PDC_r17__referenceSignal__root__Type) : (choice SpatialRelationInfo_PDC_r17__referenceSignal__root__list) :=
  match z with
   | SpatialRelationInfo_PDC_r17__referenceSignal__root__ssb_Index t => existT _ 0 t
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__csi_RS_Index t => existT _ 1 t
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__dl_PRS_PDC t => existT _ 2 t
  | SpatialRelationInfo_PDC_r17__referenceSignal__root__srs t => existT _ 3 t
  end.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__g := (fun n => typ_set (get_nth_typ SpatialRelationInfo_PDC_r17__referenceSignal__root__list n)).
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__F2 (y : choice SpatialRelationInfo_PDC_r17__referenceSignal__root__list) : SpatialRelationInfo_PDC_r17__referenceSignal__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SpatialRelationInfo_PDC_r17__referenceSignal__root__g n -> SpatialRelationInfo_PDC_r17__referenceSignal__root__Type) with
    | 0 => fun (t : SSB_Index__Type) => SpatialRelationInfo_PDC_r17__referenceSignal__root__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => SpatialRelationInfo_PDC_r17__referenceSignal__root__csi_RS_Index t 
    | 2 => fun (t : NR_DL_PRS_ResourceID_r17__Type) => SpatialRelationInfo_PDC_r17__referenceSignal__root__dl_PRS_PDC t 
    | 3 => fun (t : SpatialRelationInfo_PDC_r17__referenceSignal__root__srs__Type) => SpatialRelationInfo_PDC_r17__referenceSignal__root__srs t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : SpatialRelationInfo_PDC_r17__referenceSignal__root__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ SpatialRelationInfo_PDC_r17__referenceSignal__root__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SpatialRelationInfo_PDC_r17__referenceSignal__root__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return SpatialRelationInfo_PDC_r17__referenceSignal__root__Type with end) n0
           end t0).

Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__helper2 :  forall (y : SpatialRelationInfo_PDC_r17__referenceSignal__root__Type), SpatialRelationInfo_PDC_r17__referenceSignal__root__cond y -> choice_cond SpatialRelationInfo_PDC_r17__referenceSignal__root__list (SpatialRelationInfo_PDC_r17__referenceSignal__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__helper3 :  forall (y : SpatialRelationInfo_PDC_r17__referenceSignal__root__Type), SpatialRelationInfo_PDC_r17__referenceSignal__root__F2 (SpatialRelationInfo_PDC_r17__referenceSignal__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SpatialRelationInfo_PDC_r17__referenceSignal__root__helper4 : (forall b : choice SpatialRelationInfo_PDC_r17__referenceSignal__root__list, choice_cond SpatialRelationInfo_PDC_r17__referenceSignal__root__list b -> SpatialRelationInfo_PDC_r17__referenceSignal__root__cond (SpatialRelationInfo_PDC_r17__referenceSignal__root__F2 b) /\ SpatialRelationInfo_PDC_r17__referenceSignal__root__F1 (SpatialRelationInfo_PDC_r17__referenceSignal__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SpatialRelationInfo_PDC_r17__referenceSignal__root__F1 SpatialRelationInfo_PDC_r17__referenceSignal__root__F2.
Definition SpatialRelationInfo_PDC_r17__referenceSignal__root__Format : T_Format SpatialRelationInfo_PDC_r17__referenceSignal__root__Type SpatialRelationInfo_PDC_r17__referenceSignal__root__cond :=
  (* Eval compute in *) proj2_format SpatialRelationInfo_PDC_r17__referenceSignal__root__cond SpatialRelationInfo_PDC_r17__referenceSignal__root__list__Format SpatialRelationInfo_PDC_r17__referenceSignal__root__F1 SpatialRelationInfo_PDC_r17__referenceSignal__root__F2 SpatialRelationInfo_PDC_r17__referenceSignal__root__helper2 SpatialRelationInfo_PDC_r17__referenceSignal__root__helper3 SpatialRelationInfo_PDC_r17__referenceSignal__root__helper4.
Opaque SpatialRelationInfo_PDC_r17__referenceSignal__root__cond SpatialRelationInfo_PDC_r17__referenceSignal__root__Format.

Definition SpatialRelationInfo_PDC_r17__referenceSignal__ext__Format : T_Format SpatialRelationInfo_PDC_r17__referenceSignal__ext__Type SpatialRelationInfo_PDC_r17__referenceSignal__ext__cond := empty_format.
Opaque SpatialRelationInfo_PDC_r17__referenceSignal__ext__cond SpatialRelationInfo_PDC_r17__referenceSignal__ext__Format.

Definition SpatialRelationInfo_PDC_r17__referenceSignal__Format : T_Format SpatialRelationInfo_PDC_r17__referenceSignal__Type SpatialRelationInfo_PDC_r17__referenceSignal__cond := sum_format SpatialRelationInfo_PDC_r17__referenceSignal__root__Format SpatialRelationInfo_PDC_r17__referenceSignal__ext__Format.
Opaque SpatialRelationInfo_PDC_r17__referenceSignal__cond SpatialRelationInfo_PDC_r17__referenceSignal__Format.


Definition SpatialRelationInfo_PDC_r17__root_Format_Type := Eval cbn in seq_format_prod SpatialRelationInfo_PDC_r17__root_list.
Definition SpatialRelationInfo_PDC_r17__root_Format_list : SpatialRelationInfo_PDC_r17__root_Format_Type :=
  (SpatialRelationInfo_PDC_r17__referenceSignal__Format, unit_format).

Definition SpatialRelationInfo_PDC_r17__ext_Format_Type := Eval cbn in get_formats SpatialRelationInfo_PDC_r17__ext_list.
Definition SpatialRelationInfo_PDC_r17__ext_Format_list : SpatialRelationInfo_PDC_r17__ext_Format_Type :=
  unit__Format.

Definition SpatialRelationInfo_PDC_r17__list_type : Set := (seq_type SpatialRelationInfo_PDC_r17__root_list) * (seq_ext_type SpatialRelationInfo_PDC_r17__ext_list).
Definition SpatialRelationInfo_PDC_r17__list_cond (z : SpatialRelationInfo_PDC_r17__list_type) : Prop :=
        (seq_cond SpatialRelationInfo_PDC_r17__root_list (fst z)) /\ (seq_ext_cond SpatialRelationInfo_PDC_r17__ext_list (snd z)).
Definition SpatialRelationInfo_PDC_r17__list_format : T_Format SpatialRelationInfo_PDC_r17__list_type SpatialRelationInfo_PDC_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SpatialRelationInfo_PDC_r17__root_list SpatialRelationInfo_PDC_r17__root_Format_list SpatialRelationInfo_PDC_r17__ext_list SpatialRelationInfo_PDC_r17__ext_Format_list.

Opaque SpatialRelationInfo_PDC_r17__list_format.
Definition SpatialRelationInfo_PDC_r17__F1 (z : SpatialRelationInfo_PDC_r17__Type) : SpatialRelationInfo_PDC_r17__list_type :=
  (((SpatialRelationInfo_PDC_r17__referenceSignal z, tt)), (
tt)).
Definition SpatialRelationInfo_PDC_r17__F2 (y : SpatialRelationInfo_PDC_r17__list_type) : SpatialRelationInfo_PDC_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__SpatialRelationInfo_PDC_r17__Type j0
  end.
Definition SpatialRelationInfo_PDC_r17__helper1 : (forall a : SpatialRelationInfo_PDC_r17__Type, SpatialRelationInfo_PDC_r17__cond a -> SpatialRelationInfo_PDC_r17__list_cond (SpatialRelationInfo_PDC_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SpatialRelationInfo_PDC_r17__helper2 : (forall a : SpatialRelationInfo_PDC_r17__Type, SpatialRelationInfo_PDC_r17__F2 (SpatialRelationInfo_PDC_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SpatialRelationInfo_PDC_r17__helper3 : (forall b : SpatialRelationInfo_PDC_r17__list_type, SpatialRelationInfo_PDC_r17__list_cond b -> SpatialRelationInfo_PDC_r17__cond (SpatialRelationInfo_PDC_r17__F2 b) /\ SpatialRelationInfo_PDC_r17__F1 (SpatialRelationInfo_PDC_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SpatialRelationInfo_PDC_r17__cond, SpatialRelationInfo_PDC_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SpatialRelationInfo_PDC_r17__Format : T_Format SpatialRelationInfo_PDC_r17__Type SpatialRelationInfo_PDC_r17__cond :=
 proj2_format SpatialRelationInfo_PDC_r17__cond SpatialRelationInfo_PDC_r17__list_format  SpatialRelationInfo_PDC_r17__F1 SpatialRelationInfo_PDC_r17__F2 SpatialRelationInfo_PDC_r17__helper1 SpatialRelationInfo_PDC_r17__helper2 SpatialRelationInfo_PDC_r17__helper3.

Opaque SpatialRelationInfo_PDC_r17__cond SpatialRelationInfo_PDC_r17__Format.

