Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUSCH_PathlossReferenceRS_Id.

Opaque PUSCH_PathlossReferenceRS_Id__cond PUSCH_PathlossReferenceRS_Id__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.


Inductive PUSCH_PathlossReferenceRS__referenceSignal__Type : Set :=
  | PUSCH_PathlossReferenceRS__referenceSignal__ssb_Index : SSB_Index__Type -> PUSCH_PathlossReferenceRS__referenceSignal__Type
  | PUSCH_PathlossReferenceRS__referenceSignal__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> PUSCH_PathlossReferenceRS__referenceSignal__Type
.
Definition PUSCH_PathlossReferenceRS__referenceSignal__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition PUSCH_PathlossReferenceRS__referenceSignal__cond (c : PUSCH_PathlossReferenceRS__referenceSignal__Type) := 
  match c with
  | PUSCH_PathlossReferenceRS__referenceSignal__ssb_Index t => SSB_Index__cond t 
  | PUSCH_PathlossReferenceRS__referenceSignal__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  end.

Lemma PUSCH_PathlossReferenceRS__referenceSignal__len_helper1 : to_bit_sz (length PUSCH_PathlossReferenceRS__referenceSignal__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUSCH_PathlossReferenceRS__referenceSignal__len_helper2 : 2 <= length2 PUSCH_PathlossReferenceRS__referenceSignal__list.
 simpl. lia. Qed.
Record PUSCH_PathlossReferenceRS__Type : Set :=
  make__PUSCH_PathlossReferenceRS__Type {
    PUSCH_PathlossReferenceRS__pusch_PathlossReferenceRS_Id : PUSCH_PathlossReferenceRS_Id__Type ;
    PUSCH_PathlossReferenceRS__referenceSignal : PUSCH_PathlossReferenceRS__referenceSignal__Type ;
}.
Definition PUSCH_PathlossReferenceRS__list := (
 Nor PUSCH_PathlossReferenceRS_Id__Type PUSCH_PathlossReferenceRS_Id__cond ::
 Nor PUSCH_PathlossReferenceRS__referenceSignal__Type PUSCH_PathlossReferenceRS__referenceSignal__cond ::
 nil).
Definition PUSCH_PathlossReferenceRS__cond z := 
  PUSCH_PathlossReferenceRS_Id__cond (PUSCH_PathlossReferenceRS__pusch_PathlossReferenceRS_Id z) /\
  PUSCH_PathlossReferenceRS__referenceSignal__cond (PUSCH_PathlossReferenceRS__referenceSignal z) /\
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

Definition PUSCH_PathlossReferenceRS__referenceSignal__Format_Type := Eval cbn in get_formats PUSCH_PathlossReferenceRS__referenceSignal__list.
Definition PUSCH_PathlossReferenceRS__referenceSignal__Format_list : PUSCH_PathlossReferenceRS__referenceSignal__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, unit__Format)).
Definition PUSCH_PathlossReferenceRS__referenceSignal__list__Format := Eval compute in choice_format PUSCH_PathlossReferenceRS__referenceSignal__list PUSCH_PathlossReferenceRS__referenceSignal__len_helper1 PUSCH_PathlossReferenceRS__referenceSignal__len_helper2  PUSCH_PathlossReferenceRS__referenceSignal__Format_list.
Definition PUSCH_PathlossReferenceRS__referenceSignal__F1 (z : PUSCH_PathlossReferenceRS__referenceSignal__Type) : (choice PUSCH_PathlossReferenceRS__referenceSignal__list) :=
  match z with
   | PUSCH_PathlossReferenceRS__referenceSignal__ssb_Index t => existT _ 0 t
  | PUSCH_PathlossReferenceRS__referenceSignal__csi_RS_Index t => existT _ 1 t
  end.
Definition PUSCH_PathlossReferenceRS__referenceSignal__g := (fun n => typ_set (get_nth_typ PUSCH_PathlossReferenceRS__referenceSignal__list n)).
Definition PUSCH_PathlossReferenceRS__referenceSignal__F2 (y : choice PUSCH_PathlossReferenceRS__referenceSignal__list) : PUSCH_PathlossReferenceRS__referenceSignal__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUSCH_PathlossReferenceRS__referenceSignal__g n -> PUSCH_PathlossReferenceRS__referenceSignal__Type) with
    | 0 => fun (t : SSB_Index__Type) => PUSCH_PathlossReferenceRS__referenceSignal__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => PUSCH_PathlossReferenceRS__referenceSignal__csi_RS_Index t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PUSCH_PathlossReferenceRS__referenceSignal__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PUSCH_PathlossReferenceRS__referenceSignal__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUSCH_PathlossReferenceRS__referenceSignal__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PUSCH_PathlossReferenceRS__referenceSignal__Type with end) n0
           end t0).

Lemma PUSCH_PathlossReferenceRS__referenceSignal__helper2 :  forall (y : PUSCH_PathlossReferenceRS__referenceSignal__Type), PUSCH_PathlossReferenceRS__referenceSignal__cond y -> choice_cond PUSCH_PathlossReferenceRS__referenceSignal__list (PUSCH_PathlossReferenceRS__referenceSignal__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUSCH_PathlossReferenceRS__referenceSignal__helper3 :  forall (y : PUSCH_PathlossReferenceRS__referenceSignal__Type), PUSCH_PathlossReferenceRS__referenceSignal__F2 (PUSCH_PathlossReferenceRS__referenceSignal__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUSCH_PathlossReferenceRS__referenceSignal__helper4 : (forall b : choice PUSCH_PathlossReferenceRS__referenceSignal__list, choice_cond PUSCH_PathlossReferenceRS__referenceSignal__list b -> PUSCH_PathlossReferenceRS__referenceSignal__cond (PUSCH_PathlossReferenceRS__referenceSignal__F2 b) /\ PUSCH_PathlossReferenceRS__referenceSignal__F1 (PUSCH_PathlossReferenceRS__referenceSignal__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUSCH_PathlossReferenceRS__referenceSignal__F1 PUSCH_PathlossReferenceRS__referenceSignal__F2.
Definition PUSCH_PathlossReferenceRS__referenceSignal__Format : T_Format PUSCH_PathlossReferenceRS__referenceSignal__Type PUSCH_PathlossReferenceRS__referenceSignal__cond :=
  (* Eval compute in *) proj2_format PUSCH_PathlossReferenceRS__referenceSignal__cond PUSCH_PathlossReferenceRS__referenceSignal__list__Format PUSCH_PathlossReferenceRS__referenceSignal__F1 PUSCH_PathlossReferenceRS__referenceSignal__F2 PUSCH_PathlossReferenceRS__referenceSignal__helper2 PUSCH_PathlossReferenceRS__referenceSignal__helper3 PUSCH_PathlossReferenceRS__referenceSignal__helper4.
Opaque PUSCH_PathlossReferenceRS__referenceSignal__cond PUSCH_PathlossReferenceRS__referenceSignal__Format.


Definition PUSCH_PathlossReferenceRS__Format_Type := Eval cbn in seq_format_prod PUSCH_PathlossReferenceRS__list.
Definition PUSCH_PathlossReferenceRS__Format_list : PUSCH_PathlossReferenceRS__Format_Type :=
  (PUSCH_PathlossReferenceRS_Id__Format, (PUSCH_PathlossReferenceRS__referenceSignal__Format, unit_format)).
Definition PUSCH_PathlossReferenceRS__list__Format := (*Eval compute in *) seq_format PUSCH_PathlossReferenceRS__list PUSCH_PathlossReferenceRS__Format_list.
Definition PUSCH_PathlossReferenceRS__F1 z :=
  (PUSCH_PathlossReferenceRS__pusch_PathlossReferenceRS_Id z, (PUSCH_PathlossReferenceRS__referenceSignal z, tt)).
Definition PUSCH_PathlossReferenceRS__F2 (y : seq_type PUSCH_PathlossReferenceRS__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUSCH_PathlossReferenceRS__Type i0 i1
  end.
Lemma PUSCH_PathlossReferenceRS__F1F2_cond (z : PUSCH_PathlossReferenceRS__Type)
  : PUSCH_PathlossReferenceRS__cond z ->
  (seq_cond PUSCH_PathlossReferenceRS__list (PUSCH_PathlossReferenceRS__F1 z)).
intro H. unfold PUSCH_PathlossReferenceRS__cond in H. simpl. auto. Qed.
Lemma PUSCH_PathlossReferenceRS__F1F2_cond2 (z : PUSCH_PathlossReferenceRS__Type)
 : PUSCH_PathlossReferenceRS__F2 (PUSCH_PathlossReferenceRS__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_PathlossReferenceRS__F2F1_cond (y : seq_type PUSCH_PathlossReferenceRS__list)
  : seq_cond PUSCH_PathlossReferenceRS__list y ->
 (PUSCH_PathlossReferenceRS__cond (PUSCH_PathlossReferenceRS__F2 y)) /\  PUSCH_PathlossReferenceRS__F1 (PUSCH_PathlossReferenceRS__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_PathlossReferenceRS__cond. simpl in *. auto.
 - simpl. unfold PUSCH_PathlossReferenceRS__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_PathlossReferenceRS__Format : T_Format PUSCH_PathlossReferenceRS__Type PUSCH_PathlossReferenceRS__cond :=
        proj2_format  PUSCH_PathlossReferenceRS__cond PUSCH_PathlossReferenceRS__list__Format
    PUSCH_PathlossReferenceRS__F1 PUSCH_PathlossReferenceRS__F2 PUSCH_PathlossReferenceRS__F1F2_cond  PUSCH_PathlossReferenceRS__F1F2_cond2 PUSCH_PathlossReferenceRS__F2F1_cond.
Opaque PUSCH_PathlossReferenceRS__cond PUSCH_PathlossReferenceRS__Format.

