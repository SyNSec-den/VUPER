Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.PCI_ARFCN_NR_r16.

Opaque PCI_ARFCN_NR_r16__cond PCI_ARFCN_NR_r16__Format.


Inductive VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type : Set :=
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cgi_Info_r17 : CGI_Info_Logging_r16__Type -> VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__pci_arfcn_r17 : PCI_ARFCN_NR_r16__Type -> VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type
.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons PCI_ARFCN_NR_r16__Type PCI_ARFCN_NR_r16__cond ::
 nil).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond (c : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type) := 
  match c with
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cgi_Info_r17 t => CGI_Info_Logging_r16__cond t 
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__pci_arfcn_r17 t => PCI_ARFCN_NR_r16__cond t 
  end.

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__len_helper1 : to_bit_sz (length VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__len_helper2 : 2 <= length2 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list.
 simpl. lia. Qed.
Require Import NR.CGI_InfoEUTRALogging.

Opaque CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__Format.

Require Import NR.PCI_ARFCN_EUTRA_r16.

Opaque PCI_ARFCN_EUTRA_r16__cond PCI_ARFCN_EUTRA_r16__Format.


Inductive VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type : Set :=
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cellGlobalId_r17 : CGI_InfoEUTRALogging__Type -> VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__pci_arfcn_r17 : PCI_ARFCN_EUTRA_r16__Type -> VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type
.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list : list typ := (
typ_cons CGI_InfoEUTRALogging__Type CGI_InfoEUTRALogging__cond ::
typ_cons PCI_ARFCN_EUTRA_r16__Type PCI_ARFCN_EUTRA_r16__cond ::
 nil).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond (c : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type) := 
  match c with
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cellGlobalId_r17 t => CGI_InfoEUTRALogging__cond t 
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__pci_arfcn_r17 t => PCI_ARFCN_EUTRA_r16__cond t 
  end.

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__len_helper1 : to_bit_sz (length VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__len_helper2 : 2 <= length2 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list.
 simpl. lia. Qed.

Inductive VisitedPSCellInfo_r17__visitedCellId_r17__Type : Set :=
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17 : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type -> VisitedPSCellInfo_r17__visitedCellId_r17__Type
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17 : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type -> VisitedPSCellInfo_r17__visitedCellId_r17__Type
.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__list : list typ := (
typ_cons VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond ::
typ_cons VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond ::
 nil).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__cond (c : VisitedPSCellInfo_r17__visitedCellId_r17__Type) := 
  match c with
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17 t => VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond t 
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17 t => VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond t 
  end.

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__len_helper1 : to_bit_sz (length VisitedPSCellInfo_r17__visitedCellId_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VisitedPSCellInfo_r17__visitedCellId_r17__len_helper2 : 2 <= length2 VisitedPSCellInfo_r17__visitedCellId_r17__list.
 simpl. lia. Qed.
Lemma VisitedPSCellInfo_r17__timeSpent_r17__helper1 : (0 <= 4095)%Z.  lia. Qed.
Lemma VisitedPSCellInfo_r17__timeSpent_r17__helper2 : to_bit_sz (Z.to_nat (4095 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4095 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply VisitedPSCellInfo_r17__timeSpent_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition VisitedPSCellInfo_r17__timeSpent_r17__Type := Z.
Definition VisitedPSCellInfo_r17__timeSpent_r17__cond := (fun z => (0 <= z <= 4095)%Z).
Record VisitedPSCellInfo_r17__Type : Set :=
  make__VisitedPSCellInfo_r17__Type {
    VisitedPSCellInfo_r17__visitedCellId_r17 : option VisitedPSCellInfo_r17__visitedCellId_r17__Type ;
    VisitedPSCellInfo_r17__timeSpent_r17 : Z ;
}.
Definition VisitedPSCellInfo_r17__root_list : list seq_elem := (
 Opt VisitedPSCellInfo_r17__visitedCellId_r17__Type VisitedPSCellInfo_r17__visitedCellId_r17__cond ::
 Nor Z VisitedPSCellInfo_r17__timeSpent_r17__cond ::
 nil).
Definition VisitedPSCellInfo_r17__ext_list : list typ := (
  nil).
Definition VisitedPSCellInfo_r17__cond (z : VisitedPSCellInfo_r17__Type) := 
(  opt_cond VisitedPSCellInfo_r17__visitedCellId_r17__cond (VisitedPSCellInfo_r17__visitedCellId_r17 z) /\
  VisitedPSCellInfo_r17__timeSpent_r17__cond (VisitedPSCellInfo_r17__timeSpent_r17 z) /\
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

Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format_Type := Eval cbn in get_formats VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format_list : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format_Type :=
  (CGI_Info_Logging_r16__Format, (PCI_ARFCN_NR_r16__Format, unit__Format)).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list__Format := Eval compute in choice_format VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__len_helper1 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__len_helper2  VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format_list.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 (z : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type) : (choice VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list) :=
  match z with
   | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cgi_Info_r17 t => existT _ 0 t
  | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__pci_arfcn_r17 t => existT _ 1 t
  end.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__g := (fun n => typ_set (get_nth_typ VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list n)).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2 (y : choice VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list) : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__g n -> VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cgi_Info_r17 t 
    | 1 => fun (t : PCI_ARFCN_NR_r16__Type) => VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__pci_arfcn_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type with end) n0
           end t0).

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__helper2 :  forall (y : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type), VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond y -> choice_cond VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list (VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__helper3 :  forall (y : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type), VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2 (VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__helper4 : (forall b : choice VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list, choice_cond VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list b -> VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond (VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2 b) /\ VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 (VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format : T_Format VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond :=
  (* Eval compute in *) proj2_format VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list__Format VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__helper2 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__helper3 VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__helper4.
Opaque VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cond VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format.


Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format_Type := Eval cbn in get_formats VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format_list : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format_Type :=
  (CGI_InfoEUTRALogging__Format, (PCI_ARFCN_EUTRA_r16__Format, unit__Format)).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list__Format := Eval compute in choice_format VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__len_helper1 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__len_helper2  VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format_list.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 (z : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type) : (choice VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list) :=
  match z with
   | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cellGlobalId_r17 t => existT _ 0 t
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__pci_arfcn_r17 t => existT _ 1 t
  end.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__g := (fun n => typ_set (get_nth_typ VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list n)).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2 (y : choice VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list) : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__g n -> VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type) with
    | 0 => fun (t : CGI_InfoEUTRALogging__Type) => VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cellGlobalId_r17 t 
    | 1 => fun (t : PCI_ARFCN_EUTRA_r16__Type) => VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__pci_arfcn_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type with end) n0
           end t0).

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__helper2 :  forall (y : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type), VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond y -> choice_cond VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list (VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__helper3 :  forall (y : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type), VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2 (VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__helper4 : (forall b : choice VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list, choice_cond VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list b -> VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond (VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2 b) /\ VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 (VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format : T_Format VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond :=
  (* Eval compute in *) proj2_format VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list__Format VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__helper2 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__helper3 VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__helper4.
Opaque VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cond VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format.


Definition VisitedPSCellInfo_r17__visitedCellId_r17__Format_Type := Eval cbn in get_formats VisitedPSCellInfo_r17__visitedCellId_r17__list.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__Format_list : VisitedPSCellInfo_r17__visitedCellId_r17__Format_Type :=
  (VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format, (VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format, unit__Format)).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__list__Format := Eval compute in choice_format VisitedPSCellInfo_r17__visitedCellId_r17__list VisitedPSCellInfo_r17__visitedCellId_r17__len_helper1 VisitedPSCellInfo_r17__visitedCellId_r17__len_helper2  VisitedPSCellInfo_r17__visitedCellId_r17__Format_list.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__F1 (z : VisitedPSCellInfo_r17__visitedCellId_r17__Type) : (choice VisitedPSCellInfo_r17__visitedCellId_r17__list) :=
  match z with
   | VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17 t => existT _ 0 t
  | VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17 t => existT _ 1 t
  end.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__g := (fun n => typ_set (get_nth_typ VisitedPSCellInfo_r17__visitedCellId_r17__list n)).
Definition VisitedPSCellInfo_r17__visitedCellId_r17__F2 (y : choice VisitedPSCellInfo_r17__visitedCellId_r17__list) : VisitedPSCellInfo_r17__visitedCellId_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VisitedPSCellInfo_r17__visitedCellId_r17__g n -> VisitedPSCellInfo_r17__visitedCellId_r17__Type) with
    | 0 => fun (t : VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type) => VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17 t 
    | 1 => fun (t : VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type) => VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VisitedPSCellInfo_r17__visitedCellId_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VisitedPSCellInfo_r17__visitedCellId_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VisitedPSCellInfo_r17__visitedCellId_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VisitedPSCellInfo_r17__visitedCellId_r17__Type with end) n0
           end t0).

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__helper2 :  forall (y : VisitedPSCellInfo_r17__visitedCellId_r17__Type), VisitedPSCellInfo_r17__visitedCellId_r17__cond y -> choice_cond VisitedPSCellInfo_r17__visitedCellId_r17__list (VisitedPSCellInfo_r17__visitedCellId_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VisitedPSCellInfo_r17__visitedCellId_r17__helper3 :  forall (y : VisitedPSCellInfo_r17__visitedCellId_r17__Type), VisitedPSCellInfo_r17__visitedCellId_r17__F2 (VisitedPSCellInfo_r17__visitedCellId_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VisitedPSCellInfo_r17__visitedCellId_r17__helper4 : (forall b : choice VisitedPSCellInfo_r17__visitedCellId_r17__list, choice_cond VisitedPSCellInfo_r17__visitedCellId_r17__list b -> VisitedPSCellInfo_r17__visitedCellId_r17__cond (VisitedPSCellInfo_r17__visitedCellId_r17__F2 b) /\ VisitedPSCellInfo_r17__visitedCellId_r17__F1 (VisitedPSCellInfo_r17__visitedCellId_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VisitedPSCellInfo_r17__visitedCellId_r17__F1 VisitedPSCellInfo_r17__visitedCellId_r17__F2.
Definition VisitedPSCellInfo_r17__visitedCellId_r17__Format : T_Format VisitedPSCellInfo_r17__visitedCellId_r17__Type VisitedPSCellInfo_r17__visitedCellId_r17__cond :=
  (* Eval compute in *) proj2_format VisitedPSCellInfo_r17__visitedCellId_r17__cond VisitedPSCellInfo_r17__visitedCellId_r17__list__Format VisitedPSCellInfo_r17__visitedCellId_r17__F1 VisitedPSCellInfo_r17__visitedCellId_r17__F2 VisitedPSCellInfo_r17__visitedCellId_r17__helper2 VisitedPSCellInfo_r17__visitedCellId_r17__helper3 VisitedPSCellInfo_r17__visitedCellId_r17__helper4.
Opaque VisitedPSCellInfo_r17__visitedCellId_r17__cond VisitedPSCellInfo_r17__visitedCellId_r17__Format.

Definition VisitedPSCellInfo_r17__timeSpent_r17__Format : T_Format Z VisitedPSCellInfo_r17__timeSpent_r17__cond :=
 ranged_int_format (0) (4095) VisitedPSCellInfo_r17__timeSpent_r17__helper1 VisitedPSCellInfo_r17__timeSpent_r17__helper2.

Opaque VisitedPSCellInfo_r17__timeSpent_r17__cond VisitedPSCellInfo_r17__timeSpent_r17__Format.


Definition VisitedPSCellInfo_r17__root_Format_Type := Eval cbn in seq_format_prod VisitedPSCellInfo_r17__root_list.
Definition VisitedPSCellInfo_r17__root_Format_list : VisitedPSCellInfo_r17__root_Format_Type :=
  (VisitedPSCellInfo_r17__visitedCellId_r17__Format, (VisitedPSCellInfo_r17__timeSpent_r17__Format, unit_format)).

Definition VisitedPSCellInfo_r17__ext_Format_Type := Eval cbn in get_formats VisitedPSCellInfo_r17__ext_list.
Definition VisitedPSCellInfo_r17__ext_Format_list : VisitedPSCellInfo_r17__ext_Format_Type :=
  unit__Format.

Definition VisitedPSCellInfo_r17__list_type : Set := (seq_type VisitedPSCellInfo_r17__root_list) * (seq_ext_type VisitedPSCellInfo_r17__ext_list).
Definition VisitedPSCellInfo_r17__list_cond (z : VisitedPSCellInfo_r17__list_type) : Prop :=
        (seq_cond VisitedPSCellInfo_r17__root_list (fst z)) /\ (seq_ext_cond VisitedPSCellInfo_r17__ext_list (snd z)).
Definition VisitedPSCellInfo_r17__list_format : T_Format VisitedPSCellInfo_r17__list_type VisitedPSCellInfo_r17__list_cond :=
 (* Eval compute in *) seq_ext_format VisitedPSCellInfo_r17__root_list VisitedPSCellInfo_r17__root_Format_list VisitedPSCellInfo_r17__ext_list VisitedPSCellInfo_r17__ext_Format_list.

Opaque VisitedPSCellInfo_r17__list_format.
Definition VisitedPSCellInfo_r17__F1 (z : VisitedPSCellInfo_r17__Type) : VisitedPSCellInfo_r17__list_type :=
  (((VisitedPSCellInfo_r17__visitedCellId_r17 z, (VisitedPSCellInfo_r17__timeSpent_r17 z, tt))), (
tt)).
Definition VisitedPSCellInfo_r17__F2 (y : VisitedPSCellInfo_r17__list_type) : VisitedPSCellInfo_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__VisitedPSCellInfo_r17__Type j0 j1
  end.
Definition VisitedPSCellInfo_r17__helper1 : (forall a : VisitedPSCellInfo_r17__Type, VisitedPSCellInfo_r17__cond a -> VisitedPSCellInfo_r17__list_cond (VisitedPSCellInfo_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition VisitedPSCellInfo_r17__helper2 : (forall a : VisitedPSCellInfo_r17__Type, VisitedPSCellInfo_r17__F2 (VisitedPSCellInfo_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition VisitedPSCellInfo_r17__helper3 : (forall b : VisitedPSCellInfo_r17__list_type, VisitedPSCellInfo_r17__list_cond b -> VisitedPSCellInfo_r17__cond (VisitedPSCellInfo_r17__F2 b) /\ VisitedPSCellInfo_r17__F1 (VisitedPSCellInfo_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold VisitedPSCellInfo_r17__cond, VisitedPSCellInfo_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition VisitedPSCellInfo_r17__Format : T_Format VisitedPSCellInfo_r17__Type VisitedPSCellInfo_r17__cond :=
 proj2_format VisitedPSCellInfo_r17__cond VisitedPSCellInfo_r17__list_format  VisitedPSCellInfo_r17__F1 VisitedPSCellInfo_r17__F2 VisitedPSCellInfo_r17__helper1 VisitedPSCellInfo_r17__helper2 VisitedPSCellInfo_r17__helper3.

Opaque VisitedPSCellInfo_r17__cond VisitedPSCellInfo_r17__Format.

