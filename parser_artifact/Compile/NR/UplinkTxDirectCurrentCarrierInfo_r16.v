Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Inductive UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type : Set :=
 | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__deactivated
.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__cond := (fun (_ : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type) => True).
Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__nat__helper.

Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1 t :=
  match t with
  | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__deactivated => 0
  end.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2 n :=
  match n with
  | 0 => UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__deactivated
  | _ => UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__deactivated
  end.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1F2 : forall x : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type, (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1 x <= 0) /\ UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2 (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1 x) = x. imp_solve. Qed.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2F1 : forall (y : nat) (H : y <= 0), UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1 (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2 y) = y. enum_solve H y. Qed.


Inductive UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type : Set :=
  | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__bwp_Id_r16 : BWP_Id__Type -> UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type
  | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16 : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type -> UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type
.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list : list typ := (
typ_cons BWP_Id__Type BWP_Id__cond ::
typ_cons UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__cond ::
 nil).
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond (c : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type) := 
  match c with
  | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__bwp_Id_r16 t => BWP_Id__cond t 
  | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16 t => UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__cond t 
  end.

Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__len_helper1 : to_bit_sz (length UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__len_helper2 : 2 <= length2 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list.
 simpl. lia. Qed.
Record UplinkTxDirectCurrentCarrierInfo_r16__Type : Set :=
  make__UplinkTxDirectCurrentCarrierInfo_r16__Type {
    UplinkTxDirectCurrentCarrierInfo_r16__servCellIndex_r16 : ServCellIndex__Type ;
    UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16 : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type ;
}.
Definition UplinkTxDirectCurrentCarrierInfo_r16__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond ::
 nil).
Definition UplinkTxDirectCurrentCarrierInfo_r16__cond z := 
  ServCellIndex__cond (UplinkTxDirectCurrentCarrierInfo_r16__servCellIndex_r16 z) /\
  UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16 z) /\
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
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Format : T_Format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__nat__Format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1F2 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2F1.

Opaque UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Format.


Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format_Type := Eval cbn in get_formats UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format_list : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format_Type :=
  (BWP_Id__Format, (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Format, unit__Format)).
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list__Format := Eval compute in choice_format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__len_helper1 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__len_helper2  UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format_list.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 (z : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type) : (choice UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list) :=
  match z with
   | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__bwp_Id_r16 t => existT _ 0 t
  | UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16 t => existT _ 1 t
  end.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__g := (fun n => typ_set (get_nth_typ UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list n)).
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2 (y : choice UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list) : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__g n -> UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type) with
    | 0 => fun (t : BWP_Id__Type) => UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__bwp_Id_r16 t 
    | 1 => fun (t : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type) => UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type with end) n0
           end t0).

Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__helper2 :  forall (y : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type), UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond y -> choice_cond UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__helper3 :  forall (y : UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type), UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2 (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__helper4 : (forall b : choice UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list, choice_cond UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list b -> UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2 b) /\ UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2.
Definition UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format : T_Format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond :=
  (* Eval compute in *) proj2_format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list__Format UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__helper2 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__helper3 UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__helper4.
Opaque UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format.


Definition UplinkTxDirectCurrentCarrierInfo_r16__Format_Type := Eval cbn in seq_format_prod UplinkTxDirectCurrentCarrierInfo_r16__list.
Definition UplinkTxDirectCurrentCarrierInfo_r16__Format_list : UplinkTxDirectCurrentCarrierInfo_r16__Format_Type :=
  (ServCellIndex__Format, (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format, unit_format)).
Definition UplinkTxDirectCurrentCarrierInfo_r16__list__Format := (*Eval compute in *) seq_format UplinkTxDirectCurrentCarrierInfo_r16__list UplinkTxDirectCurrentCarrierInfo_r16__Format_list.
Definition UplinkTxDirectCurrentCarrierInfo_r16__F1 z :=
  (UplinkTxDirectCurrentCarrierInfo_r16__servCellIndex_r16 z, (UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16 z, tt)).
Definition UplinkTxDirectCurrentCarrierInfo_r16__F2 (y : seq_type UplinkTxDirectCurrentCarrierInfo_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UplinkTxDirectCurrentCarrierInfo_r16__Type i0 i1
  end.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__F1F2_cond (z : UplinkTxDirectCurrentCarrierInfo_r16__Type)
  : UplinkTxDirectCurrentCarrierInfo_r16__cond z ->
  (seq_cond UplinkTxDirectCurrentCarrierInfo_r16__list (UplinkTxDirectCurrentCarrierInfo_r16__F1 z)).
intro H. unfold UplinkTxDirectCurrentCarrierInfo_r16__cond in H. simpl. auto. Qed.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__F1F2_cond2 (z : UplinkTxDirectCurrentCarrierInfo_r16__Type)
 : UplinkTxDirectCurrentCarrierInfo_r16__F2 (UplinkTxDirectCurrentCarrierInfo_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkTxDirectCurrentCarrierInfo_r16__F2F1_cond (y : seq_type UplinkTxDirectCurrentCarrierInfo_r16__list)
  : seq_cond UplinkTxDirectCurrentCarrierInfo_r16__list y ->
 (UplinkTxDirectCurrentCarrierInfo_r16__cond (UplinkTxDirectCurrentCarrierInfo_r16__F2 y)) /\  UplinkTxDirectCurrentCarrierInfo_r16__F1 (UplinkTxDirectCurrentCarrierInfo_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkTxDirectCurrentCarrierInfo_r16__cond. simpl in *. auto.
 - simpl. unfold UplinkTxDirectCurrentCarrierInfo_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkTxDirectCurrentCarrierInfo_r16__Format : T_Format UplinkTxDirectCurrentCarrierInfo_r16__Type UplinkTxDirectCurrentCarrierInfo_r16__cond :=
        proj2_format  UplinkTxDirectCurrentCarrierInfo_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__list__Format
    UplinkTxDirectCurrentCarrierInfo_r16__F1 UplinkTxDirectCurrentCarrierInfo_r16__F2 UplinkTxDirectCurrentCarrierInfo_r16__F1F2_cond  UplinkTxDirectCurrentCarrierInfo_r16__F1F2_cond2 UplinkTxDirectCurrentCarrierInfo_r16__F2F1_cond.
Opaque UplinkTxDirectCurrentCarrierInfo_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__Format.

