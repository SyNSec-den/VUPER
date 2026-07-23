Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Require Import NR.PhysCellIdUTRA_FDD_r16.

Opaque PhysCellIdUTRA_FDD_r16__cond PhysCellIdUTRA_FDD_r16__Format.


Inductive CellsTriggeredList__seq_of__Type : Set :=
  | CellsTriggeredList__seq_of__physCellId : PhysCellId__Type -> CellsTriggeredList__seq_of__Type
  | CellsTriggeredList__seq_of__physCellIdEUTRA : EUTRA_PhysCellId__Type -> CellsTriggeredList__seq_of__Type
  | CellsTriggeredList__seq_of__physCellIdUTRA_FDD_r16 : PhysCellIdUTRA_FDD_r16__Type -> CellsTriggeredList__seq_of__Type
.
Definition CellsTriggeredList__seq_of__list : list typ := (
typ_cons PhysCellId__Type PhysCellId__cond ::
typ_cons EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
typ_cons PhysCellIdUTRA_FDD_r16__Type PhysCellIdUTRA_FDD_r16__cond ::
 nil).
Definition CellsTriggeredList__seq_of__cond (c : CellsTriggeredList__seq_of__Type) := 
  match c with
  | CellsTriggeredList__seq_of__physCellId t => PhysCellId__cond t 
  | CellsTriggeredList__seq_of__physCellIdEUTRA t => EUTRA_PhysCellId__cond t 
  | CellsTriggeredList__seq_of__physCellIdUTRA_FDD_r16 t => PhysCellIdUTRA_FDD_r16__cond t 
  end.

Lemma CellsTriggeredList__seq_of__len_helper1 : to_bit_sz (length CellsTriggeredList__seq_of__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CellsTriggeredList__seq_of__len_helper2 : 2 <= length2 CellsTriggeredList__seq_of__list.
 simpl. lia. Qed.
Definition CellsTriggeredList__Type := list CellsTriggeredList__seq_of__Type.

Lemma CellsTriggeredList__helper1 : (0 <= 1 <= maxNrofCellMeas)%Z. unfold maxNrofCellMeas.
 lia. Qed.
Lemma CellsTriggeredList__helper2 : to_bit_sz (Z.to_nat (maxNrofCellMeas - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCellMeas - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellsTriggeredList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellsTriggeredList__cond (z : CellsTriggeredList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCellMeas)%Z /\ (list_and CellsTriggeredList__seq_of__cond z) .


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

Definition CellsTriggeredList__seq_of__Format_Type := Eval cbn in get_formats CellsTriggeredList__seq_of__list.
Definition CellsTriggeredList__seq_of__Format_list : CellsTriggeredList__seq_of__Format_Type :=
  (PhysCellId__Format, (EUTRA_PhysCellId__Format, (PhysCellIdUTRA_FDD_r16__Format, unit__Format))).
Definition CellsTriggeredList__seq_of__list__Format := Eval compute in choice_format CellsTriggeredList__seq_of__list CellsTriggeredList__seq_of__len_helper1 CellsTriggeredList__seq_of__len_helper2  CellsTriggeredList__seq_of__Format_list.
Definition CellsTriggeredList__seq_of__F1 (z : CellsTriggeredList__seq_of__Type) : (choice CellsTriggeredList__seq_of__list) :=
  match z with
   | CellsTriggeredList__seq_of__physCellId t => existT _ 0 t
  | CellsTriggeredList__seq_of__physCellIdEUTRA t => existT _ 1 t
  | CellsTriggeredList__seq_of__physCellIdUTRA_FDD_r16 t => existT _ 2 t
  end.
Definition CellsTriggeredList__seq_of__g := (fun n => typ_set (get_nth_typ CellsTriggeredList__seq_of__list n)).
Definition CellsTriggeredList__seq_of__F2 (y : choice CellsTriggeredList__seq_of__list) : CellsTriggeredList__seq_of__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CellsTriggeredList__seq_of__g n -> CellsTriggeredList__seq_of__Type) with
    | 0 => fun (t : PhysCellId__Type) => CellsTriggeredList__seq_of__physCellId t 
    | 1 => fun (t : EUTRA_PhysCellId__Type) => CellsTriggeredList__seq_of__physCellIdEUTRA t 
    | 2 => fun (t : PhysCellIdUTRA_FDD_r16__Type) => CellsTriggeredList__seq_of__physCellIdUTRA_FDD_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : CellsTriggeredList__seq_of__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ CellsTriggeredList__seq_of__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CellsTriggeredList__seq_of__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return CellsTriggeredList__seq_of__Type with end) n0
           end t0).

Lemma CellsTriggeredList__seq_of__helper2 :  forall (y : CellsTriggeredList__seq_of__Type), CellsTriggeredList__seq_of__cond y -> choice_cond CellsTriggeredList__seq_of__list (CellsTriggeredList__seq_of__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CellsTriggeredList__seq_of__helper3 :  forall (y : CellsTriggeredList__seq_of__Type), CellsTriggeredList__seq_of__F2 (CellsTriggeredList__seq_of__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CellsTriggeredList__seq_of__helper4 : (forall b : choice CellsTriggeredList__seq_of__list, choice_cond CellsTriggeredList__seq_of__list b -> CellsTriggeredList__seq_of__cond (CellsTriggeredList__seq_of__F2 b) /\ CellsTriggeredList__seq_of__F1 (CellsTriggeredList__seq_of__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CellsTriggeredList__seq_of__F1 CellsTriggeredList__seq_of__F2.
Definition CellsTriggeredList__seq_of__Format : T_Format CellsTriggeredList__seq_of__Type CellsTriggeredList__seq_of__cond :=
  (* Eval compute in *) proj2_format CellsTriggeredList__seq_of__cond CellsTriggeredList__seq_of__list__Format CellsTriggeredList__seq_of__F1 CellsTriggeredList__seq_of__F2 CellsTriggeredList__seq_of__helper2 CellsTriggeredList__seq_of__helper3 CellsTriggeredList__seq_of__helper4.
Opaque CellsTriggeredList__seq_of__cond CellsTriggeredList__seq_of__Format.

Definition CellsTriggeredList__Format : T_Format CellsTriggeredList__Type CellsTriggeredList__cond := seq_of_format CellsTriggeredList__seq_of__Format 1 maxNrofCellMeas CellsTriggeredList__helper1 CellsTriggeredList__helper2.

Opaque CellsTriggeredList__cond CellsTriggeredList__Format.

