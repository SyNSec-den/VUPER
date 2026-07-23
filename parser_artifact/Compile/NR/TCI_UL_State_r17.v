Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TCI_UL_State_Id_r17.

Opaque TCI_UL_State_Id_r17__cond TCI_UL_State_Id_r17__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.


Inductive TCI_UL_State_r17__referenceSignal_r17__Type : Set :=
  | TCI_UL_State_r17__referenceSignal_r17__ssb_Index_r17 : SSB_Index__Type -> TCI_UL_State_r17__referenceSignal_r17__Type
  | TCI_UL_State_r17__referenceSignal_r17__csi_RS_Index_r17 : NZP_CSI_RS_ResourceId__Type -> TCI_UL_State_r17__referenceSignal_r17__Type
  | TCI_UL_State_r17__referenceSignal_r17__srs_r17 : SRS_ResourceId__Type -> TCI_UL_State_r17__referenceSignal_r17__Type
.
Definition TCI_UL_State_r17__referenceSignal_r17__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
typ_cons SRS_ResourceId__Type SRS_ResourceId__cond ::
 nil).
Definition TCI_UL_State_r17__referenceSignal_r17__cond (c : TCI_UL_State_r17__referenceSignal_r17__Type) := 
  match c with
  | TCI_UL_State_r17__referenceSignal_r17__ssb_Index_r17 t => SSB_Index__cond t 
  | TCI_UL_State_r17__referenceSignal_r17__csi_RS_Index_r17 t => NZP_CSI_RS_ResourceId__cond t 
  | TCI_UL_State_r17__referenceSignal_r17__srs_r17 t => SRS_ResourceId__cond t 
  end.

Lemma TCI_UL_State_r17__referenceSignal_r17__len_helper1 : to_bit_sz (length TCI_UL_State_r17__referenceSignal_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma TCI_UL_State_r17__referenceSignal_r17__len_helper2 : 2 <= length2 TCI_UL_State_r17__referenceSignal_r17__list.
 simpl. lia. Qed.
Require Import NR.AdditionalPCIIndex_r17.

Opaque AdditionalPCIIndex_r17__cond AdditionalPCIIndex_r17__Format.

Require Import NR.Uplink_powerControlId_r17.

Opaque Uplink_powerControlId_r17__cond Uplink_powerControlId_r17__Format.

Require Import NR.PathlossReferenceRS_Id_r17.

Opaque PathlossReferenceRS_Id_r17__cond PathlossReferenceRS_Id_r17__Format.

Record TCI_UL_State_r17__Type : Set :=
  make__TCI_UL_State_r17__Type {
    TCI_UL_State_r17__tci_UL_State_Id_r17 : TCI_UL_State_Id_r17__Type ;
    TCI_UL_State_r17__servingCellId_r17 : option ServCellIndex__Type ;
    TCI_UL_State_r17__bwp_Id_r17 : option BWP_Id__Type ;
    TCI_UL_State_r17__referenceSignal_r17 : TCI_UL_State_r17__referenceSignal_r17__Type ;
    TCI_UL_State_r17__additionalPCI_r17 : option AdditionalPCIIndex_r17__Type ;
    TCI_UL_State_r17__ul_powerControl_r17 : option Uplink_powerControlId_r17__Type ;
    TCI_UL_State_r17__pathlossReferenceRS_Id_r17 : option PathlossReferenceRS_Id_r17__Type ;
}.
Definition TCI_UL_State_r17__root_list : list seq_elem := (
 Nor TCI_UL_State_Id_r17__Type TCI_UL_State_Id_r17__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Opt BWP_Id__Type BWP_Id__cond ::
 Nor TCI_UL_State_r17__referenceSignal_r17__Type TCI_UL_State_r17__referenceSignal_r17__cond ::
 Opt AdditionalPCIIndex_r17__Type AdditionalPCIIndex_r17__cond ::
 Opt Uplink_powerControlId_r17__Type Uplink_powerControlId_r17__cond ::
 Opt PathlossReferenceRS_Id_r17__Type PathlossReferenceRS_Id_r17__cond ::
 nil).
Definition TCI_UL_State_r17__ext_list : list typ := (
  nil).
Definition TCI_UL_State_r17__cond (z : TCI_UL_State_r17__Type) := 
(  TCI_UL_State_Id_r17__cond (TCI_UL_State_r17__tci_UL_State_Id_r17 z) /\
  opt_cond ServCellIndex__cond (TCI_UL_State_r17__servingCellId_r17 z) /\
  opt_cond BWP_Id__cond (TCI_UL_State_r17__bwp_Id_r17 z) /\
  TCI_UL_State_r17__referenceSignal_r17__cond (TCI_UL_State_r17__referenceSignal_r17 z) /\
  opt_cond AdditionalPCIIndex_r17__cond (TCI_UL_State_r17__additionalPCI_r17 z) /\
  opt_cond Uplink_powerControlId_r17__cond (TCI_UL_State_r17__ul_powerControl_r17 z) /\
  opt_cond PathlossReferenceRS_Id_r17__cond (TCI_UL_State_r17__pathlossReferenceRS_Id_r17 z) /\
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

Definition TCI_UL_State_r17__referenceSignal_r17__Format_Type := Eval cbn in get_formats TCI_UL_State_r17__referenceSignal_r17__list.
Definition TCI_UL_State_r17__referenceSignal_r17__Format_list : TCI_UL_State_r17__referenceSignal_r17__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, (SRS_ResourceId__Format, unit__Format))).
Definition TCI_UL_State_r17__referenceSignal_r17__list__Format := Eval compute in choice_format TCI_UL_State_r17__referenceSignal_r17__list TCI_UL_State_r17__referenceSignal_r17__len_helper1 TCI_UL_State_r17__referenceSignal_r17__len_helper2  TCI_UL_State_r17__referenceSignal_r17__Format_list.
Definition TCI_UL_State_r17__referenceSignal_r17__F1 (z : TCI_UL_State_r17__referenceSignal_r17__Type) : (choice TCI_UL_State_r17__referenceSignal_r17__list) :=
  match z with
   | TCI_UL_State_r17__referenceSignal_r17__ssb_Index_r17 t => existT _ 0 t
  | TCI_UL_State_r17__referenceSignal_r17__csi_RS_Index_r17 t => existT _ 1 t
  | TCI_UL_State_r17__referenceSignal_r17__srs_r17 t => existT _ 2 t
  end.
Definition TCI_UL_State_r17__referenceSignal_r17__g := (fun n => typ_set (get_nth_typ TCI_UL_State_r17__referenceSignal_r17__list n)).
Definition TCI_UL_State_r17__referenceSignal_r17__F2 (y : choice TCI_UL_State_r17__referenceSignal_r17__list) : TCI_UL_State_r17__referenceSignal_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (TCI_UL_State_r17__referenceSignal_r17__g n -> TCI_UL_State_r17__referenceSignal_r17__Type) with
    | 0 => fun (t : SSB_Index__Type) => TCI_UL_State_r17__referenceSignal_r17__ssb_Index_r17 t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => TCI_UL_State_r17__referenceSignal_r17__csi_RS_Index_r17 t 
    | 2 => fun (t : SRS_ResourceId__Type) => TCI_UL_State_r17__referenceSignal_r17__srs_r17 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : TCI_UL_State_r17__referenceSignal_r17__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ TCI_UL_State_r17__referenceSignal_r17__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len TCI_UL_State_r17__referenceSignal_r17__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return TCI_UL_State_r17__referenceSignal_r17__Type with end) n0
           end t0).

Lemma TCI_UL_State_r17__referenceSignal_r17__helper2 :  forall (y : TCI_UL_State_r17__referenceSignal_r17__Type), TCI_UL_State_r17__referenceSignal_r17__cond y -> choice_cond TCI_UL_State_r17__referenceSignal_r17__list (TCI_UL_State_r17__referenceSignal_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma TCI_UL_State_r17__referenceSignal_r17__helper3 :  forall (y : TCI_UL_State_r17__referenceSignal_r17__Type), TCI_UL_State_r17__referenceSignal_r17__F2 (TCI_UL_State_r17__referenceSignal_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma TCI_UL_State_r17__referenceSignal_r17__helper4 : (forall b : choice TCI_UL_State_r17__referenceSignal_r17__list, choice_cond TCI_UL_State_r17__referenceSignal_r17__list b -> TCI_UL_State_r17__referenceSignal_r17__cond (TCI_UL_State_r17__referenceSignal_r17__F2 b) /\ TCI_UL_State_r17__referenceSignal_r17__F1 (TCI_UL_State_r17__referenceSignal_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length TCI_UL_State_r17__referenceSignal_r17__F1 TCI_UL_State_r17__referenceSignal_r17__F2.
Definition TCI_UL_State_r17__referenceSignal_r17__Format : T_Format TCI_UL_State_r17__referenceSignal_r17__Type TCI_UL_State_r17__referenceSignal_r17__cond :=
  (* Eval compute in *) proj2_format TCI_UL_State_r17__referenceSignal_r17__cond TCI_UL_State_r17__referenceSignal_r17__list__Format TCI_UL_State_r17__referenceSignal_r17__F1 TCI_UL_State_r17__referenceSignal_r17__F2 TCI_UL_State_r17__referenceSignal_r17__helper2 TCI_UL_State_r17__referenceSignal_r17__helper3 TCI_UL_State_r17__referenceSignal_r17__helper4.
Opaque TCI_UL_State_r17__referenceSignal_r17__cond TCI_UL_State_r17__referenceSignal_r17__Format.


Definition TCI_UL_State_r17__root_Format_Type := Eval cbn in seq_format_prod TCI_UL_State_r17__root_list.
Definition TCI_UL_State_r17__root_Format_list : TCI_UL_State_r17__root_Format_Type :=
  (TCI_UL_State_Id_r17__Format, (ServCellIndex__Format, (BWP_Id__Format, (TCI_UL_State_r17__referenceSignal_r17__Format, (AdditionalPCIIndex_r17__Format, (Uplink_powerControlId_r17__Format, (PathlossReferenceRS_Id_r17__Format, unit_format))))))).

Definition TCI_UL_State_r17__ext_Format_Type := Eval cbn in get_formats TCI_UL_State_r17__ext_list.
Definition TCI_UL_State_r17__ext_Format_list : TCI_UL_State_r17__ext_Format_Type :=
  unit__Format.

Definition TCI_UL_State_r17__list_type : Set := (seq_type TCI_UL_State_r17__root_list) * (seq_ext_type TCI_UL_State_r17__ext_list).
Definition TCI_UL_State_r17__list_cond (z : TCI_UL_State_r17__list_type) : Prop :=
        (seq_cond TCI_UL_State_r17__root_list (fst z)) /\ (seq_ext_cond TCI_UL_State_r17__ext_list (snd z)).
Definition TCI_UL_State_r17__list_format : T_Format TCI_UL_State_r17__list_type TCI_UL_State_r17__list_cond :=
 (* Eval compute in *) seq_ext_format TCI_UL_State_r17__root_list TCI_UL_State_r17__root_Format_list TCI_UL_State_r17__ext_list TCI_UL_State_r17__ext_Format_list.

Opaque TCI_UL_State_r17__list_format.
Definition TCI_UL_State_r17__F1 (z : TCI_UL_State_r17__Type) : TCI_UL_State_r17__list_type :=
  (((TCI_UL_State_r17__tci_UL_State_Id_r17 z, (TCI_UL_State_r17__servingCellId_r17 z, (TCI_UL_State_r17__bwp_Id_r17 z, (TCI_UL_State_r17__referenceSignal_r17 z, (TCI_UL_State_r17__additionalPCI_r17 z, (TCI_UL_State_r17__ul_powerControl_r17 z, (TCI_UL_State_r17__pathlossReferenceRS_Id_r17 z, tt)))))))), (
tt)).
Definition TCI_UL_State_r17__F2 (y : TCI_UL_State_r17__list_type) : TCI_UL_State_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), _)=>
    make__TCI_UL_State_r17__Type j0 j1 j2 j3 j4 j5 j6
  end.
Definition TCI_UL_State_r17__helper1 : (forall a : TCI_UL_State_r17__Type, TCI_UL_State_r17__cond a -> TCI_UL_State_r17__list_cond (TCI_UL_State_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition TCI_UL_State_r17__helper2 : (forall a : TCI_UL_State_r17__Type, TCI_UL_State_r17__F2 (TCI_UL_State_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition TCI_UL_State_r17__helper3 : (forall b : TCI_UL_State_r17__list_type, TCI_UL_State_r17__list_cond b -> TCI_UL_State_r17__cond (TCI_UL_State_r17__F2 b) /\ TCI_UL_State_r17__F1 (TCI_UL_State_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold TCI_UL_State_r17__cond, TCI_UL_State_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition TCI_UL_State_r17__Format : T_Format TCI_UL_State_r17__Type TCI_UL_State_r17__cond :=
 proj2_format TCI_UL_State_r17__cond TCI_UL_State_r17__list_format  TCI_UL_State_r17__F1 TCI_UL_State_r17__F2 TCI_UL_State_r17__helper1 TCI_UL_State_r17__helper2 TCI_UL_State_r17__helper3.

Opaque TCI_UL_State_r17__cond TCI_UL_State_r17__Format.

