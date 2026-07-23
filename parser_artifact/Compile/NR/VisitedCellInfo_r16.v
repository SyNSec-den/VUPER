Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.PCI_ARFCN_NR_r16.

Opaque PCI_ARFCN_NR_r16__cond PCI_ARFCN_NR_r16__Format.


Inductive VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type : Set :=
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cgi_Info : CGI_Info_Logging_r16__Type -> VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__pci_arfcn_r16 : PCI_ARFCN_NR_r16__Type -> VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type
.
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons PCI_ARFCN_NR_r16__Type PCI_ARFCN_NR_r16__cond ::
 nil).
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond (c : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type) := 
  match c with
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cgi_Info t => CGI_Info_Logging_r16__cond t 
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__pci_arfcn_r16 t => PCI_ARFCN_NR_r16__cond t 
  end.

Lemma VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__len_helper1 : to_bit_sz (length VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__len_helper2 : 2 <= length2 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list.
 simpl. lia. Qed.
Require Import NR.CGI_InfoEUTRA.

Opaque CGI_InfoEUTRA__cond CGI_InfoEUTRA__Format.

Require Import NR.PCI_ARFCN_EUTRA_r16.

Opaque PCI_ARFCN_EUTRA_r16__cond PCI_ARFCN_EUTRA_r16__Format.


Inductive VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type : Set :=
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cellGlobalId_r16 : CGI_InfoEUTRA__Type -> VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__pci_arfcn_r16 : PCI_ARFCN_EUTRA_r16__Type -> VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type
.
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list : list typ := (
typ_cons CGI_InfoEUTRA__Type CGI_InfoEUTRA__cond ::
typ_cons PCI_ARFCN_EUTRA_r16__Type PCI_ARFCN_EUTRA_r16__cond ::
 nil).
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond (c : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type) := 
  match c with
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cellGlobalId_r16 t => CGI_InfoEUTRA__cond t 
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__pci_arfcn_r16 t => PCI_ARFCN_EUTRA_r16__cond t 
  end.

Lemma VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__len_helper1 : to_bit_sz (length VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__len_helper2 : 2 <= length2 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list.
 simpl. lia. Qed.

Inductive VisitedCellInfo_r16__visitedCellId_r16__Type : Set :=
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16 : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type -> VisitedCellInfo_r16__visitedCellId_r16__Type
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16 : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type -> VisitedCellInfo_r16__visitedCellId_r16__Type
.
Definition VisitedCellInfo_r16__visitedCellId_r16__list : list typ := (
typ_cons VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond ::
typ_cons VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond ::
 nil).
Definition VisitedCellInfo_r16__visitedCellId_r16__cond (c : VisitedCellInfo_r16__visitedCellId_r16__Type) := 
  match c with
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16 t => VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond t 
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16 t => VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond t 
  end.

Lemma VisitedCellInfo_r16__visitedCellId_r16__len_helper1 : to_bit_sz (length VisitedCellInfo_r16__visitedCellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VisitedCellInfo_r16__visitedCellId_r16__len_helper2 : 2 <= length2 VisitedCellInfo_r16__visitedCellId_r16__list.
 simpl. lia. Qed.
Lemma VisitedCellInfo_r16__timeSpent_r16__helper1 : (0 <= 4095)%Z.  lia. Qed.
Lemma VisitedCellInfo_r16__timeSpent_r16__helper2 : to_bit_sz (Z.to_nat (4095 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4095 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply VisitedCellInfo_r16__timeSpent_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition VisitedCellInfo_r16__timeSpent_r16__Type := Z.
Definition VisitedCellInfo_r16__timeSpent_r16__cond := (fun z => (0 <= z <= 4095)%Z).
Require Import NR.VisitedPSCellInfoList_r17.

Opaque VisitedPSCellInfoList_r17__cond VisitedPSCellInfoList_r17__Format.

Record VisitedCellInfo_r16__ext0O__Type : Set :=
  make__VisitedCellInfo_r16__ext0O__Type {
    VisitedCellInfo_r16__ext0O__visitedPSCellInfoListReport_r17 : option VisitedPSCellInfoList_r17__Type ;
}.
Definition VisitedCellInfo_r16__ext0O__list := (
 Opt VisitedPSCellInfoList_r17__Type VisitedPSCellInfoList_r17__cond ::
 nil).
Definition VisitedCellInfo_r16__ext0O__cond z := 
  opt_cond VisitedPSCellInfoList_r17__cond (VisitedCellInfo_r16__ext0O__visitedPSCellInfoListReport_r17 z) /\
  True.

Definition VisitedCellInfo_r16__ext0__Type := VisitedCellInfo_r16__ext0O__Type.
Definition VisitedCellInfo_r16__ext0__cond := VisitedCellInfo_r16__ext0O__cond.

Record VisitedCellInfo_r16__Type : Set :=
  make__VisitedCellInfo_r16__Type {
    VisitedCellInfo_r16__visitedCellId_r16 : option VisitedCellInfo_r16__visitedCellId_r16__Type ;
    VisitedCellInfo_r16__timeSpent_r16 : Z ;
    VisitedCellInfo_r16__ext0 : option VisitedCellInfo_r16__ext0__Type ;
}.
Definition VisitedCellInfo_r16__root_list : list seq_elem := (
 Opt VisitedCellInfo_r16__visitedCellId_r16__Type VisitedCellInfo_r16__visitedCellId_r16__cond ::
 Nor Z VisitedCellInfo_r16__timeSpent_r16__cond ::
 nil).
Definition VisitedCellInfo_r16__ext_list : list typ := (
  typ_cons VisitedCellInfo_r16__ext0__Type VisitedCellInfo_r16__ext0__cond ::
  nil).
Definition VisitedCellInfo_r16__cond (z : VisitedCellInfo_r16__Type) := 
(  opt_cond VisitedCellInfo_r16__visitedCellId_r16__cond (VisitedCellInfo_r16__visitedCellId_r16 z) /\
  VisitedCellInfo_r16__timeSpent_r16__cond (VisitedCellInfo_r16__timeSpent_r16 z) /\
  True) /\ 
(  opt_cond VisitedCellInfo_r16__ext0__cond (VisitedCellInfo_r16__ext0 z) /\
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

Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format_Type := Eval cbn in get_formats VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list.
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format_list : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format_Type :=
  (CGI_Info_Logging_r16__Format, (PCI_ARFCN_NR_r16__Format, unit__Format)).
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list__Format := Eval compute in choice_format VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__len_helper1 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__len_helper2  VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format_list.
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 (z : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type) : (choice VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list) :=
  match z with
   | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cgi_Info t => existT _ 0 t
  | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__pci_arfcn_r16 t => existT _ 1 t
  end.
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__g := (fun n => typ_set (get_nth_typ VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list n)).
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2 (y : choice VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list) : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__g n -> VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cgi_Info t 
    | 1 => fun (t : PCI_ARFCN_NR_r16__Type) => VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__pci_arfcn_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type with end) n0
           end t0).

Lemma VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__helper2 :  forall (y : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type), VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond y -> choice_cond VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list (VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__helper3 :  forall (y : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type), VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2 (VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__helper4 : (forall b : choice VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list, choice_cond VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list b -> VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond (VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2 b) /\ VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 (VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2.
Definition VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format : T_Format VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond :=
  (* Eval compute in *) proj2_format VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list__Format VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__helper2 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__helper3 VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__helper4.
Opaque VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cond VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format.


Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format_Type := Eval cbn in get_formats VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list.
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format_list : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format_Type :=
  (CGI_InfoEUTRA__Format, (PCI_ARFCN_EUTRA_r16__Format, unit__Format)).
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list__Format := Eval compute in choice_format VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__len_helper1 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__len_helper2  VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format_list.
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 (z : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type) : (choice VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list) :=
  match z with
   | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cellGlobalId_r16 t => existT _ 0 t
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__pci_arfcn_r16 t => existT _ 1 t
  end.
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__g := (fun n => typ_set (get_nth_typ VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list n)).
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2 (y : choice VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list) : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__g n -> VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type) with
    | 0 => fun (t : CGI_InfoEUTRA__Type) => VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cellGlobalId_r16 t 
    | 1 => fun (t : PCI_ARFCN_EUTRA_r16__Type) => VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__pci_arfcn_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type with end) n0
           end t0).

Lemma VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__helper2 :  forall (y : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type), VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond y -> choice_cond VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list (VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__helper3 :  forall (y : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type), VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2 (VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__helper4 : (forall b : choice VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list, choice_cond VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list b -> VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond (VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2 b) /\ VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 (VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2.
Definition VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format : T_Format VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond :=
  (* Eval compute in *) proj2_format VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list__Format VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__helper2 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__helper3 VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__helper4.
Opaque VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cond VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format.


Definition VisitedCellInfo_r16__visitedCellId_r16__Format_Type := Eval cbn in get_formats VisitedCellInfo_r16__visitedCellId_r16__list.
Definition VisitedCellInfo_r16__visitedCellId_r16__Format_list : VisitedCellInfo_r16__visitedCellId_r16__Format_Type :=
  (VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format, (VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format, unit__Format)).
Definition VisitedCellInfo_r16__visitedCellId_r16__list__Format := Eval compute in choice_format VisitedCellInfo_r16__visitedCellId_r16__list VisitedCellInfo_r16__visitedCellId_r16__len_helper1 VisitedCellInfo_r16__visitedCellId_r16__len_helper2  VisitedCellInfo_r16__visitedCellId_r16__Format_list.
Definition VisitedCellInfo_r16__visitedCellId_r16__F1 (z : VisitedCellInfo_r16__visitedCellId_r16__Type) : (choice VisitedCellInfo_r16__visitedCellId_r16__list) :=
  match z with
   | VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16 t => existT _ 0 t
  | VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16 t => existT _ 1 t
  end.
Definition VisitedCellInfo_r16__visitedCellId_r16__g := (fun n => typ_set (get_nth_typ VisitedCellInfo_r16__visitedCellId_r16__list n)).
Definition VisitedCellInfo_r16__visitedCellId_r16__F2 (y : choice VisitedCellInfo_r16__visitedCellId_r16__list) : VisitedCellInfo_r16__visitedCellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VisitedCellInfo_r16__visitedCellId_r16__g n -> VisitedCellInfo_r16__visitedCellId_r16__Type) with
    | 0 => fun (t : VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type) => VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16 t 
    | 1 => fun (t : VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type) => VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VisitedCellInfo_r16__visitedCellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VisitedCellInfo_r16__visitedCellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VisitedCellInfo_r16__visitedCellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VisitedCellInfo_r16__visitedCellId_r16__Type with end) n0
           end t0).

Lemma VisitedCellInfo_r16__visitedCellId_r16__helper2 :  forall (y : VisitedCellInfo_r16__visitedCellId_r16__Type), VisitedCellInfo_r16__visitedCellId_r16__cond y -> choice_cond VisitedCellInfo_r16__visitedCellId_r16__list (VisitedCellInfo_r16__visitedCellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VisitedCellInfo_r16__visitedCellId_r16__helper3 :  forall (y : VisitedCellInfo_r16__visitedCellId_r16__Type), VisitedCellInfo_r16__visitedCellId_r16__F2 (VisitedCellInfo_r16__visitedCellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VisitedCellInfo_r16__visitedCellId_r16__helper4 : (forall b : choice VisitedCellInfo_r16__visitedCellId_r16__list, choice_cond VisitedCellInfo_r16__visitedCellId_r16__list b -> VisitedCellInfo_r16__visitedCellId_r16__cond (VisitedCellInfo_r16__visitedCellId_r16__F2 b) /\ VisitedCellInfo_r16__visitedCellId_r16__F1 (VisitedCellInfo_r16__visitedCellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VisitedCellInfo_r16__visitedCellId_r16__F1 VisitedCellInfo_r16__visitedCellId_r16__F2.
Definition VisitedCellInfo_r16__visitedCellId_r16__Format : T_Format VisitedCellInfo_r16__visitedCellId_r16__Type VisitedCellInfo_r16__visitedCellId_r16__cond :=
  (* Eval compute in *) proj2_format VisitedCellInfo_r16__visitedCellId_r16__cond VisitedCellInfo_r16__visitedCellId_r16__list__Format VisitedCellInfo_r16__visitedCellId_r16__F1 VisitedCellInfo_r16__visitedCellId_r16__F2 VisitedCellInfo_r16__visitedCellId_r16__helper2 VisitedCellInfo_r16__visitedCellId_r16__helper3 VisitedCellInfo_r16__visitedCellId_r16__helper4.
Opaque VisitedCellInfo_r16__visitedCellId_r16__cond VisitedCellInfo_r16__visitedCellId_r16__Format.

Definition VisitedCellInfo_r16__timeSpent_r16__Format : T_Format Z VisitedCellInfo_r16__timeSpent_r16__cond :=
 ranged_int_format (0) (4095) VisitedCellInfo_r16__timeSpent_r16__helper1 VisitedCellInfo_r16__timeSpent_r16__helper2.

Opaque VisitedCellInfo_r16__timeSpent_r16__cond VisitedCellInfo_r16__timeSpent_r16__Format.


Definition VisitedCellInfo_r16__ext0O__Format_Type := Eval cbn in seq_format_prod VisitedCellInfo_r16__ext0O__list.
Definition VisitedCellInfo_r16__ext0O__Format_list : VisitedCellInfo_r16__ext0O__Format_Type :=
  (VisitedPSCellInfoList_r17__Format, unit_format).
Definition VisitedCellInfo_r16__ext0O__list__Format := (*Eval compute in *) seq_format VisitedCellInfo_r16__ext0O__list VisitedCellInfo_r16__ext0O__Format_list.
Definition VisitedCellInfo_r16__ext0O__F1 z :=
  (VisitedCellInfo_r16__ext0O__visitedPSCellInfoListReport_r17 z, tt).
Definition VisitedCellInfo_r16__ext0O__F2 (y : seq_type VisitedCellInfo_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__VisitedCellInfo_r16__ext0O__Type i0
  end.
Lemma VisitedCellInfo_r16__ext0O__F1F2_cond (z : VisitedCellInfo_r16__ext0O__Type)
  : VisitedCellInfo_r16__ext0O__cond z ->
  (seq_cond VisitedCellInfo_r16__ext0O__list (VisitedCellInfo_r16__ext0O__F1 z)).
intro H. unfold VisitedCellInfo_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma VisitedCellInfo_r16__ext0O__F1F2_cond2 (z : VisitedCellInfo_r16__ext0O__Type)
 : VisitedCellInfo_r16__ext0O__F2 (VisitedCellInfo_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VisitedCellInfo_r16__ext0O__F2F1_cond (y : seq_type VisitedCellInfo_r16__ext0O__list)
  : seq_cond VisitedCellInfo_r16__ext0O__list y ->
 (VisitedCellInfo_r16__ext0O__cond (VisitedCellInfo_r16__ext0O__F2 y)) /\  VisitedCellInfo_r16__ext0O__F1 (VisitedCellInfo_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VisitedCellInfo_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold VisitedCellInfo_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VisitedCellInfo_r16__ext0O__Format : T_Format VisitedCellInfo_r16__ext0O__Type VisitedCellInfo_r16__ext0O__cond :=
        proj2_format  VisitedCellInfo_r16__ext0O__cond VisitedCellInfo_r16__ext0O__list__Format
    VisitedCellInfo_r16__ext0O__F1 VisitedCellInfo_r16__ext0O__F2 VisitedCellInfo_r16__ext0O__F1F2_cond  VisitedCellInfo_r16__ext0O__F1F2_cond2 VisitedCellInfo_r16__ext0O__F2F1_cond.
Opaque VisitedCellInfo_r16__ext0O__cond VisitedCellInfo_r16__ext0O__Format.

Definition VisitedCellInfo_r16__ext0__check_all_none (b : VisitedCellInfo_r16__ext0O__Type) : bool :=
match b with 
  | make__VisitedCellInfo_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition VisitedCellInfo_r16__ext0__Format : T_Format VisitedCellInfo_r16__ext0__Type VisitedCellInfo_r16__ext0__cond :=
  restrict_add_format VisitedCellInfo_r16__ext0__check_all_none VisitedCellInfo_r16__ext0O__Format.

Opaque VisitedCellInfo_r16__ext0__cond VisitedCellInfo_r16__ext0__Format.


Definition VisitedCellInfo_r16__root_Format_Type := Eval cbn in seq_format_prod VisitedCellInfo_r16__root_list.
Definition VisitedCellInfo_r16__root_Format_list : VisitedCellInfo_r16__root_Format_Type :=
  (VisitedCellInfo_r16__visitedCellId_r16__Format, (VisitedCellInfo_r16__timeSpent_r16__Format, unit_format)).

Definition VisitedCellInfo_r16__ext_Format_Type := Eval cbn in get_formats VisitedCellInfo_r16__ext_list.
Definition VisitedCellInfo_r16__ext_Format_list : VisitedCellInfo_r16__ext_Format_Type :=
  (VisitedCellInfo_r16__ext0__Format, unit__Format).

Definition VisitedCellInfo_r16__list_type : Set := (seq_type VisitedCellInfo_r16__root_list) * (seq_ext_type VisitedCellInfo_r16__ext_list).
Definition VisitedCellInfo_r16__list_cond (z : VisitedCellInfo_r16__list_type) : Prop :=
        (seq_cond VisitedCellInfo_r16__root_list (fst z)) /\ (seq_ext_cond VisitedCellInfo_r16__ext_list (snd z)).
Definition VisitedCellInfo_r16__list_format : T_Format VisitedCellInfo_r16__list_type VisitedCellInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format VisitedCellInfo_r16__root_list VisitedCellInfo_r16__root_Format_list VisitedCellInfo_r16__ext_list VisitedCellInfo_r16__ext_Format_list.

Opaque VisitedCellInfo_r16__list_format.
Definition VisitedCellInfo_r16__F1 (z : VisitedCellInfo_r16__Type) : VisitedCellInfo_r16__list_type :=
  (((VisitedCellInfo_r16__visitedCellId_r16 z, (VisitedCellInfo_r16__timeSpent_r16 z, tt))), (
(VisitedCellInfo_r16__ext0 z, tt))).
Definition VisitedCellInfo_r16__F2 (y : VisitedCellInfo_r16__list_type) : VisitedCellInfo_r16__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__VisitedCellInfo_r16__Type j0 j1 i0
  end.
Definition VisitedCellInfo_r16__helper1 : (forall a : VisitedCellInfo_r16__Type, VisitedCellInfo_r16__cond a -> VisitedCellInfo_r16__list_cond (VisitedCellInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition VisitedCellInfo_r16__helper2 : (forall a : VisitedCellInfo_r16__Type, VisitedCellInfo_r16__F2 (VisitedCellInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition VisitedCellInfo_r16__helper3 : (forall b : VisitedCellInfo_r16__list_type, VisitedCellInfo_r16__list_cond b -> VisitedCellInfo_r16__cond (VisitedCellInfo_r16__F2 b) /\ VisitedCellInfo_r16__F1 (VisitedCellInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold VisitedCellInfo_r16__cond, VisitedCellInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition VisitedCellInfo_r16__Format : T_Format VisitedCellInfo_r16__Type VisitedCellInfo_r16__cond :=
 proj2_format VisitedCellInfo_r16__cond VisitedCellInfo_r16__list_format  VisitedCellInfo_r16__F1 VisitedCellInfo_r16__F2 VisitedCellInfo_r16__helper1 VisitedCellInfo_r16__helper2 VisitedCellInfo_r16__helper3.

Opaque VisitedCellInfo_r16__cond VisitedCellInfo_r16__Format.

