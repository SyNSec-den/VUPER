Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.PCI_ARFCN_NR_r16.

Opaque PCI_ARFCN_NR_r16__cond PCI_ARFCN_NR_r16__Format.


Inductive ChoCandidateCell_r17__Type : Set :=
  | ChoCandidateCell_r17__cellGlobalId_r17 : CGI_Info_Logging_r16__Type -> ChoCandidateCell_r17__Type
  | ChoCandidateCell_r17__pci_arfcn_r17 : PCI_ARFCN_NR_r16__Type -> ChoCandidateCell_r17__Type
.
Definition ChoCandidateCell_r17__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons PCI_ARFCN_NR_r16__Type PCI_ARFCN_NR_r16__cond ::
 nil).
Definition ChoCandidateCell_r17__cond (c : ChoCandidateCell_r17__Type) := 
  match c with
  | ChoCandidateCell_r17__cellGlobalId_r17 t => CGI_Info_Logging_r16__cond t 
  | ChoCandidateCell_r17__pci_arfcn_r17 t => PCI_ARFCN_NR_r16__cond t 
  end.

Lemma ChoCandidateCell_r17__len_helper1 : to_bit_sz (length ChoCandidateCell_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ChoCandidateCell_r17__len_helper2 : 2 <= length2 ChoCandidateCell_r17__list.
 simpl. lia. Qed.

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

Definition ChoCandidateCell_r17__Format_Type := Eval cbn in get_formats ChoCandidateCell_r17__list.
Definition ChoCandidateCell_r17__Format_list : ChoCandidateCell_r17__Format_Type :=
  (CGI_Info_Logging_r16__Format, (PCI_ARFCN_NR_r16__Format, unit__Format)).
Definition ChoCandidateCell_r17__list__Format := Eval compute in choice_format ChoCandidateCell_r17__list ChoCandidateCell_r17__len_helper1 ChoCandidateCell_r17__len_helper2  ChoCandidateCell_r17__Format_list.
Definition ChoCandidateCell_r17__F1 (z : ChoCandidateCell_r17__Type) : (choice ChoCandidateCell_r17__list) :=
  match z with
   | ChoCandidateCell_r17__cellGlobalId_r17 t => existT _ 0 t
  | ChoCandidateCell_r17__pci_arfcn_r17 t => existT _ 1 t
  end.
Definition ChoCandidateCell_r17__g := (fun n => typ_set (get_nth_typ ChoCandidateCell_r17__list n)).
Definition ChoCandidateCell_r17__F2 (y : choice ChoCandidateCell_r17__list) : ChoCandidateCell_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ChoCandidateCell_r17__g n -> ChoCandidateCell_r17__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => ChoCandidateCell_r17__cellGlobalId_r17 t 
    | 1 => fun (t : PCI_ARFCN_NR_r16__Type) => ChoCandidateCell_r17__pci_arfcn_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ChoCandidateCell_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ChoCandidateCell_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ChoCandidateCell_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ChoCandidateCell_r17__Type with end) n0
           end t0).

Lemma ChoCandidateCell_r17__helper2 :  forall (y : ChoCandidateCell_r17__Type), ChoCandidateCell_r17__cond y -> choice_cond ChoCandidateCell_r17__list (ChoCandidateCell_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ChoCandidateCell_r17__helper3 :  forall (y : ChoCandidateCell_r17__Type), ChoCandidateCell_r17__F2 (ChoCandidateCell_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ChoCandidateCell_r17__helper4 : (forall b : choice ChoCandidateCell_r17__list, choice_cond ChoCandidateCell_r17__list b -> ChoCandidateCell_r17__cond (ChoCandidateCell_r17__F2 b) /\ ChoCandidateCell_r17__F1 (ChoCandidateCell_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ChoCandidateCell_r17__F1 ChoCandidateCell_r17__F2.
Definition ChoCandidateCell_r17__Format : T_Format ChoCandidateCell_r17__Type ChoCandidateCell_r17__cond :=
  (* Eval compute in *) proj2_format ChoCandidateCell_r17__cond ChoCandidateCell_r17__list__Format ChoCandidateCell_r17__F1 ChoCandidateCell_r17__F2 ChoCandidateCell_r17__helper2 ChoCandidateCell_r17__helper3 ChoCandidateCell_r17__helper4.
Opaque ChoCandidateCell_r17__cond ChoCandidateCell_r17__Format.

