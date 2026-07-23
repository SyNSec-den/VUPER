Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PathlossReferenceRS_Id_r17.

Opaque PathlossReferenceRS_Id_r17__cond PathlossReferenceRS_Id_r17__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.


Inductive PathlossReferenceRS_r17__referenceSignal_r17__Type : Set :=
  | PathlossReferenceRS_r17__referenceSignal_r17__ssb_Index : SSB_Index__Type -> PathlossReferenceRS_r17__referenceSignal_r17__Type
  | PathlossReferenceRS_r17__referenceSignal_r17__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> PathlossReferenceRS_r17__referenceSignal_r17__Type
.
Definition PathlossReferenceRS_r17__referenceSignal_r17__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition PathlossReferenceRS_r17__referenceSignal_r17__cond (c : PathlossReferenceRS_r17__referenceSignal_r17__Type) := 
  match c with
  | PathlossReferenceRS_r17__referenceSignal_r17__ssb_Index t => SSB_Index__cond t 
  | PathlossReferenceRS_r17__referenceSignal_r17__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  end.

Lemma PathlossReferenceRS_r17__referenceSignal_r17__len_helper1 : to_bit_sz (length PathlossReferenceRS_r17__referenceSignal_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PathlossReferenceRS_r17__referenceSignal_r17__len_helper2 : 2 <= length2 PathlossReferenceRS_r17__referenceSignal_r17__list.
 simpl. lia. Qed.
Require Import NR.AdditionalPCIIndex_r17.

Opaque AdditionalPCIIndex_r17__cond AdditionalPCIIndex_r17__Format.

Record PathlossReferenceRS_r17__Type : Set :=
  make__PathlossReferenceRS_r17__Type {
    PathlossReferenceRS_r17__pathlossReferenceRS_Id_r17 : PathlossReferenceRS_Id_r17__Type ;
    PathlossReferenceRS_r17__referenceSignal_r17 : PathlossReferenceRS_r17__referenceSignal_r17__Type ;
    PathlossReferenceRS_r17__additionalPCI_r17 : option AdditionalPCIIndex_r17__Type ;
}.
Definition PathlossReferenceRS_r17__list := (
 Nor PathlossReferenceRS_Id_r17__Type PathlossReferenceRS_Id_r17__cond ::
 Nor PathlossReferenceRS_r17__referenceSignal_r17__Type PathlossReferenceRS_r17__referenceSignal_r17__cond ::
 Opt AdditionalPCIIndex_r17__Type AdditionalPCIIndex_r17__cond ::
 nil).
Definition PathlossReferenceRS_r17__cond z := 
  PathlossReferenceRS_Id_r17__cond (PathlossReferenceRS_r17__pathlossReferenceRS_Id_r17 z) /\
  PathlossReferenceRS_r17__referenceSignal_r17__cond (PathlossReferenceRS_r17__referenceSignal_r17 z) /\
  opt_cond AdditionalPCIIndex_r17__cond (PathlossReferenceRS_r17__additionalPCI_r17 z) /\
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

Definition PathlossReferenceRS_r17__referenceSignal_r17__Format_Type := Eval cbn in get_formats PathlossReferenceRS_r17__referenceSignal_r17__list.
Definition PathlossReferenceRS_r17__referenceSignal_r17__Format_list : PathlossReferenceRS_r17__referenceSignal_r17__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, unit__Format)).
Definition PathlossReferenceRS_r17__referenceSignal_r17__list__Format := Eval compute in choice_format PathlossReferenceRS_r17__referenceSignal_r17__list PathlossReferenceRS_r17__referenceSignal_r17__len_helper1 PathlossReferenceRS_r17__referenceSignal_r17__len_helper2  PathlossReferenceRS_r17__referenceSignal_r17__Format_list.
Definition PathlossReferenceRS_r17__referenceSignal_r17__F1 (z : PathlossReferenceRS_r17__referenceSignal_r17__Type) : (choice PathlossReferenceRS_r17__referenceSignal_r17__list) :=
  match z with
   | PathlossReferenceRS_r17__referenceSignal_r17__ssb_Index t => existT _ 0 t
  | PathlossReferenceRS_r17__referenceSignal_r17__csi_RS_Index t => existT _ 1 t
  end.
Definition PathlossReferenceRS_r17__referenceSignal_r17__g := (fun n => typ_set (get_nth_typ PathlossReferenceRS_r17__referenceSignal_r17__list n)).
Definition PathlossReferenceRS_r17__referenceSignal_r17__F2 (y : choice PathlossReferenceRS_r17__referenceSignal_r17__list) : PathlossReferenceRS_r17__referenceSignal_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PathlossReferenceRS_r17__referenceSignal_r17__g n -> PathlossReferenceRS_r17__referenceSignal_r17__Type) with
    | 0 => fun (t : SSB_Index__Type) => PathlossReferenceRS_r17__referenceSignal_r17__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => PathlossReferenceRS_r17__referenceSignal_r17__csi_RS_Index t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PathlossReferenceRS_r17__referenceSignal_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PathlossReferenceRS_r17__referenceSignal_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PathlossReferenceRS_r17__referenceSignal_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PathlossReferenceRS_r17__referenceSignal_r17__Type with end) n0
           end t0).

Lemma PathlossReferenceRS_r17__referenceSignal_r17__helper2 :  forall (y : PathlossReferenceRS_r17__referenceSignal_r17__Type), PathlossReferenceRS_r17__referenceSignal_r17__cond y -> choice_cond PathlossReferenceRS_r17__referenceSignal_r17__list (PathlossReferenceRS_r17__referenceSignal_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PathlossReferenceRS_r17__referenceSignal_r17__helper3 :  forall (y : PathlossReferenceRS_r17__referenceSignal_r17__Type), PathlossReferenceRS_r17__referenceSignal_r17__F2 (PathlossReferenceRS_r17__referenceSignal_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PathlossReferenceRS_r17__referenceSignal_r17__helper4 : (forall b : choice PathlossReferenceRS_r17__referenceSignal_r17__list, choice_cond PathlossReferenceRS_r17__referenceSignal_r17__list b -> PathlossReferenceRS_r17__referenceSignal_r17__cond (PathlossReferenceRS_r17__referenceSignal_r17__F2 b) /\ PathlossReferenceRS_r17__referenceSignal_r17__F1 (PathlossReferenceRS_r17__referenceSignal_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PathlossReferenceRS_r17__referenceSignal_r17__F1 PathlossReferenceRS_r17__referenceSignal_r17__F2.
Definition PathlossReferenceRS_r17__referenceSignal_r17__Format : T_Format PathlossReferenceRS_r17__referenceSignal_r17__Type PathlossReferenceRS_r17__referenceSignal_r17__cond :=
  (* Eval compute in *) proj2_format PathlossReferenceRS_r17__referenceSignal_r17__cond PathlossReferenceRS_r17__referenceSignal_r17__list__Format PathlossReferenceRS_r17__referenceSignal_r17__F1 PathlossReferenceRS_r17__referenceSignal_r17__F2 PathlossReferenceRS_r17__referenceSignal_r17__helper2 PathlossReferenceRS_r17__referenceSignal_r17__helper3 PathlossReferenceRS_r17__referenceSignal_r17__helper4.
Opaque PathlossReferenceRS_r17__referenceSignal_r17__cond PathlossReferenceRS_r17__referenceSignal_r17__Format.


Definition PathlossReferenceRS_r17__Format_Type := Eval cbn in seq_format_prod PathlossReferenceRS_r17__list.
Definition PathlossReferenceRS_r17__Format_list : PathlossReferenceRS_r17__Format_Type :=
  (PathlossReferenceRS_Id_r17__Format, (PathlossReferenceRS_r17__referenceSignal_r17__Format, (AdditionalPCIIndex_r17__Format, unit_format))).
Definition PathlossReferenceRS_r17__list__Format := (*Eval compute in *) seq_format PathlossReferenceRS_r17__list PathlossReferenceRS_r17__Format_list.
Definition PathlossReferenceRS_r17__F1 z :=
  (PathlossReferenceRS_r17__pathlossReferenceRS_Id_r17 z, (PathlossReferenceRS_r17__referenceSignal_r17 z, (PathlossReferenceRS_r17__additionalPCI_r17 z, tt))).
Definition PathlossReferenceRS_r17__F2 (y : seq_type PathlossReferenceRS_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PathlossReferenceRS_r17__Type i0 i1 i2
  end.
Lemma PathlossReferenceRS_r17__F1F2_cond (z : PathlossReferenceRS_r17__Type)
  : PathlossReferenceRS_r17__cond z ->
  (seq_cond PathlossReferenceRS_r17__list (PathlossReferenceRS_r17__F1 z)).
intro H. unfold PathlossReferenceRS_r17__cond in H. simpl. auto. Qed.
Lemma PathlossReferenceRS_r17__F1F2_cond2 (z : PathlossReferenceRS_r17__Type)
 : PathlossReferenceRS_r17__F2 (PathlossReferenceRS_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PathlossReferenceRS_r17__F2F1_cond (y : seq_type PathlossReferenceRS_r17__list)
  : seq_cond PathlossReferenceRS_r17__list y ->
 (PathlossReferenceRS_r17__cond (PathlossReferenceRS_r17__F2 y)) /\  PathlossReferenceRS_r17__F1 (PathlossReferenceRS_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PathlossReferenceRS_r17__cond. simpl in *. auto.
 - simpl. unfold PathlossReferenceRS_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PathlossReferenceRS_r17__Format : T_Format PathlossReferenceRS_r17__Type PathlossReferenceRS_r17__cond :=
        proj2_format  PathlossReferenceRS_r17__cond PathlossReferenceRS_r17__list__Format
    PathlossReferenceRS_r17__F1 PathlossReferenceRS_r17__F2 PathlossReferenceRS_r17__F1F2_cond  PathlossReferenceRS_r17__F1F2_cond2 PathlossReferenceRS_r17__F2F1_cond.
Opaque PathlossReferenceRS_r17__cond PathlossReferenceRS_r17__Format.

