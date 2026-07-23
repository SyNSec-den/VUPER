Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.


Inductive CandidateBeamRS_r16__candidateBeamConfig_r16__Type : Set :=
  | CandidateBeamRS_r16__candidateBeamConfig_r16__ssb_r16 : SSB_Index__Type -> CandidateBeamRS_r16__candidateBeamConfig_r16__Type
  | CandidateBeamRS_r16__candidateBeamConfig_r16__csi_RS_r16 : NZP_CSI_RS_ResourceId__Type -> CandidateBeamRS_r16__candidateBeamConfig_r16__Type
.
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__cond (c : CandidateBeamRS_r16__candidateBeamConfig_r16__Type) := 
  match c with
  | CandidateBeamRS_r16__candidateBeamConfig_r16__ssb_r16 t => SSB_Index__cond t 
  | CandidateBeamRS_r16__candidateBeamConfig_r16__csi_RS_r16 t => NZP_CSI_RS_ResourceId__cond t 
  end.

Lemma CandidateBeamRS_r16__candidateBeamConfig_r16__len_helper1 : to_bit_sz (length CandidateBeamRS_r16__candidateBeamConfig_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CandidateBeamRS_r16__candidateBeamConfig_r16__len_helper2 : 2 <= length2 CandidateBeamRS_r16__candidateBeamConfig_r16__list.
 simpl. lia. Qed.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record CandidateBeamRS_r16__Type : Set :=
  make__CandidateBeamRS_r16__Type {
    CandidateBeamRS_r16__candidateBeamConfig_r16 : CandidateBeamRS_r16__candidateBeamConfig_r16__Type ;
    CandidateBeamRS_r16__servingCellId : option ServCellIndex__Type ;
}.
Definition CandidateBeamRS_r16__list := (
 Nor CandidateBeamRS_r16__candidateBeamConfig_r16__Type CandidateBeamRS_r16__candidateBeamConfig_r16__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition CandidateBeamRS_r16__cond z := 
  CandidateBeamRS_r16__candidateBeamConfig_r16__cond (CandidateBeamRS_r16__candidateBeamConfig_r16 z) /\
  opt_cond ServCellIndex__cond (CandidateBeamRS_r16__servingCellId z) /\
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

Definition CandidateBeamRS_r16__candidateBeamConfig_r16__Format_Type := Eval cbn in get_formats CandidateBeamRS_r16__candidateBeamConfig_r16__list.
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__Format_list : CandidateBeamRS_r16__candidateBeamConfig_r16__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, unit__Format)).
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__list__Format := Eval compute in choice_format CandidateBeamRS_r16__candidateBeamConfig_r16__list CandidateBeamRS_r16__candidateBeamConfig_r16__len_helper1 CandidateBeamRS_r16__candidateBeamConfig_r16__len_helper2  CandidateBeamRS_r16__candidateBeamConfig_r16__Format_list.
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__F1 (z : CandidateBeamRS_r16__candidateBeamConfig_r16__Type) : (choice CandidateBeamRS_r16__candidateBeamConfig_r16__list) :=
  match z with
   | CandidateBeamRS_r16__candidateBeamConfig_r16__ssb_r16 t => existT _ 0 t
  | CandidateBeamRS_r16__candidateBeamConfig_r16__csi_RS_r16 t => existT _ 1 t
  end.
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__g := (fun n => typ_set (get_nth_typ CandidateBeamRS_r16__candidateBeamConfig_r16__list n)).
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__F2 (y : choice CandidateBeamRS_r16__candidateBeamConfig_r16__list) : CandidateBeamRS_r16__candidateBeamConfig_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CandidateBeamRS_r16__candidateBeamConfig_r16__g n -> CandidateBeamRS_r16__candidateBeamConfig_r16__Type) with
    | 0 => fun (t : SSB_Index__Type) => CandidateBeamRS_r16__candidateBeamConfig_r16__ssb_r16 t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => CandidateBeamRS_r16__candidateBeamConfig_r16__csi_RS_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CandidateBeamRS_r16__candidateBeamConfig_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CandidateBeamRS_r16__candidateBeamConfig_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CandidateBeamRS_r16__candidateBeamConfig_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CandidateBeamRS_r16__candidateBeamConfig_r16__Type with end) n0
           end t0).

Lemma CandidateBeamRS_r16__candidateBeamConfig_r16__helper2 :  forall (y : CandidateBeamRS_r16__candidateBeamConfig_r16__Type), CandidateBeamRS_r16__candidateBeamConfig_r16__cond y -> choice_cond CandidateBeamRS_r16__candidateBeamConfig_r16__list (CandidateBeamRS_r16__candidateBeamConfig_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CandidateBeamRS_r16__candidateBeamConfig_r16__helper3 :  forall (y : CandidateBeamRS_r16__candidateBeamConfig_r16__Type), CandidateBeamRS_r16__candidateBeamConfig_r16__F2 (CandidateBeamRS_r16__candidateBeamConfig_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CandidateBeamRS_r16__candidateBeamConfig_r16__helper4 : (forall b : choice CandidateBeamRS_r16__candidateBeamConfig_r16__list, choice_cond CandidateBeamRS_r16__candidateBeamConfig_r16__list b -> CandidateBeamRS_r16__candidateBeamConfig_r16__cond (CandidateBeamRS_r16__candidateBeamConfig_r16__F2 b) /\ CandidateBeamRS_r16__candidateBeamConfig_r16__F1 (CandidateBeamRS_r16__candidateBeamConfig_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CandidateBeamRS_r16__candidateBeamConfig_r16__F1 CandidateBeamRS_r16__candidateBeamConfig_r16__F2.
Definition CandidateBeamRS_r16__candidateBeamConfig_r16__Format : T_Format CandidateBeamRS_r16__candidateBeamConfig_r16__Type CandidateBeamRS_r16__candidateBeamConfig_r16__cond :=
  (* Eval compute in *) proj2_format CandidateBeamRS_r16__candidateBeamConfig_r16__cond CandidateBeamRS_r16__candidateBeamConfig_r16__list__Format CandidateBeamRS_r16__candidateBeamConfig_r16__F1 CandidateBeamRS_r16__candidateBeamConfig_r16__F2 CandidateBeamRS_r16__candidateBeamConfig_r16__helper2 CandidateBeamRS_r16__candidateBeamConfig_r16__helper3 CandidateBeamRS_r16__candidateBeamConfig_r16__helper4.
Opaque CandidateBeamRS_r16__candidateBeamConfig_r16__cond CandidateBeamRS_r16__candidateBeamConfig_r16__Format.


Definition CandidateBeamRS_r16__Format_Type := Eval cbn in seq_format_prod CandidateBeamRS_r16__list.
Definition CandidateBeamRS_r16__Format_list : CandidateBeamRS_r16__Format_Type :=
  (CandidateBeamRS_r16__candidateBeamConfig_r16__Format, (ServCellIndex__Format, unit_format)).
Definition CandidateBeamRS_r16__list__Format := (*Eval compute in *) seq_format CandidateBeamRS_r16__list CandidateBeamRS_r16__Format_list.
Definition CandidateBeamRS_r16__F1 z :=
  (CandidateBeamRS_r16__candidateBeamConfig_r16 z, (CandidateBeamRS_r16__servingCellId z, tt)).
Definition CandidateBeamRS_r16__F2 (y : seq_type CandidateBeamRS_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CandidateBeamRS_r16__Type i0 i1
  end.
Lemma CandidateBeamRS_r16__F1F2_cond (z : CandidateBeamRS_r16__Type)
  : CandidateBeamRS_r16__cond z ->
  (seq_cond CandidateBeamRS_r16__list (CandidateBeamRS_r16__F1 z)).
intro H. unfold CandidateBeamRS_r16__cond in H. simpl. auto. Qed.
Lemma CandidateBeamRS_r16__F1F2_cond2 (z : CandidateBeamRS_r16__Type)
 : CandidateBeamRS_r16__F2 (CandidateBeamRS_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CandidateBeamRS_r16__F2F1_cond (y : seq_type CandidateBeamRS_r16__list)
  : seq_cond CandidateBeamRS_r16__list y ->
 (CandidateBeamRS_r16__cond (CandidateBeamRS_r16__F2 y)) /\  CandidateBeamRS_r16__F1 (CandidateBeamRS_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CandidateBeamRS_r16__cond. simpl in *. auto.
 - simpl. unfold CandidateBeamRS_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CandidateBeamRS_r16__Format : T_Format CandidateBeamRS_r16__Type CandidateBeamRS_r16__cond :=
        proj2_format  CandidateBeamRS_r16__cond CandidateBeamRS_r16__list__Format
    CandidateBeamRS_r16__F1 CandidateBeamRS_r16__F2 CandidateBeamRS_r16__F1F2_cond  CandidateBeamRS_r16__F1F2_cond2 CandidateBeamRS_r16__F2F1_cond.
Opaque CandidateBeamRS_r16__cond CandidateBeamRS_r16__Format.

