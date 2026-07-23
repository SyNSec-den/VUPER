Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasObjectId.

Opaque MeasObjectId__cond MeasObjectId__Format.

Require Import NR.MeasObjectNR.

Opaque MeasObjectNR__cond MeasObjectNR__Format.


Inductive MeasObjectToAddMod__measObject__root__Type : Set := | MeasObjectToAddMod__measObject__root__measObjectNR : MeasObjectNR__Type -> MeasObjectToAddMod__measObject__root__Type.
Definition MeasObjectToAddMod__measObject__root__cond (c : MeasObjectToAddMod__measObject__root__Type) := 
  match c with
  | MeasObjectToAddMod__measObject__root__measObjectNR t => MeasObjectNR__cond t 
  end.

Require Import NR.MeasObjectEUTRA.

Opaque MeasObjectEUTRA__cond MeasObjectEUTRA__Format.

Require Import NR.MeasObjectUTRA_FDD_r16.

Opaque MeasObjectUTRA_FDD_r16__cond MeasObjectUTRA_FDD_r16__Format.

Require Import NR.MeasObjectNR_SL_r16.

Opaque MeasObjectNR_SL_r16__cond MeasObjectNR_SL_r16__Format.

Require Import NR.MeasObjectCLI_r16.

Opaque MeasObjectCLI_r16__cond MeasObjectCLI_r16__Format.

Require Import NR.MeasObjectRxTxDiff_r17.

Opaque MeasObjectRxTxDiff_r17__cond MeasObjectRxTxDiff_r17__Format.

Require Import NR.SL_MeasObject_r16.

Opaque SL_MeasObject_r16__cond SL_MeasObject_r16__Format.


Inductive MeasObjectToAddMod__measObject__ext__Type : Set :=
  | MeasObjectToAddMod__measObject__ext__measObjectEUTRA : MeasObjectEUTRA__Type -> MeasObjectToAddMod__measObject__ext__Type
  | MeasObjectToAddMod__measObject__ext__measObjectUTRA_FDD_r16 : MeasObjectUTRA_FDD_r16__Type -> MeasObjectToAddMod__measObject__ext__Type
  | MeasObjectToAddMod__measObject__ext__measObjectNR_SL_r16 : MeasObjectNR_SL_r16__Type -> MeasObjectToAddMod__measObject__ext__Type
  | MeasObjectToAddMod__measObject__ext__measObjectCLI_r16 : MeasObjectCLI_r16__Type -> MeasObjectToAddMod__measObject__ext__Type
  | MeasObjectToAddMod__measObject__ext__measObjectRxTxDiff_r17 : MeasObjectRxTxDiff_r17__Type -> MeasObjectToAddMod__measObject__ext__Type
  | MeasObjectToAddMod__measObject__ext__measObjectRelay_r17 : SL_MeasObject_r16__Type -> MeasObjectToAddMod__measObject__ext__Type
.
Definition MeasObjectToAddMod__measObject__ext__list : list typ := (
typ_cons MeasObjectEUTRA__Type MeasObjectEUTRA__cond ::
typ_cons MeasObjectUTRA_FDD_r16__Type MeasObjectUTRA_FDD_r16__cond ::
typ_cons MeasObjectNR_SL_r16__Type MeasObjectNR_SL_r16__cond ::
typ_cons MeasObjectCLI_r16__Type MeasObjectCLI_r16__cond ::
typ_cons MeasObjectRxTxDiff_r17__Type MeasObjectRxTxDiff_r17__cond ::
typ_cons SL_MeasObject_r16__Type SL_MeasObject_r16__cond ::
 nil).
Definition MeasObjectToAddMod__measObject__ext__cond (c : MeasObjectToAddMod__measObject__ext__Type) := 
  match c with
  | MeasObjectToAddMod__measObject__ext__measObjectEUTRA t => MeasObjectEUTRA__cond t 
  | MeasObjectToAddMod__measObject__ext__measObjectUTRA_FDD_r16 t => MeasObjectUTRA_FDD_r16__cond t 
  | MeasObjectToAddMod__measObject__ext__measObjectNR_SL_r16 t => MeasObjectNR_SL_r16__cond t 
  | MeasObjectToAddMod__measObject__ext__measObjectCLI_r16 t => MeasObjectCLI_r16__cond t 
  | MeasObjectToAddMod__measObject__ext__measObjectRxTxDiff_r17 t => MeasObjectRxTxDiff_r17__cond t 
  | MeasObjectToAddMod__measObject__ext__measObjectRelay_r17 t => SL_MeasObject_r16__cond t 
  end.

Lemma MeasObjectToAddMod__measObject__ext__len_helper1 : to_bit_sz (length MeasObjectToAddMod__measObject__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition MeasObjectToAddMod__measObject__Type : Set := MeasObjectToAddMod__measObject__root__Type + MeasObjectToAddMod__measObject__ext__Type.
Definition MeasObjectToAddMod__measObject__cond :=
  sum_cond MeasObjectToAddMod__measObject__root__cond MeasObjectToAddMod__measObject__ext__cond.
Record MeasObjectToAddMod__Type : Set :=
  make__MeasObjectToAddMod__Type {
    MeasObjectToAddMod__measObjectId : MeasObjectId__Type ;
    MeasObjectToAddMod__measObject : MeasObjectToAddMod__measObject__Type ;
}.
Definition MeasObjectToAddMod__list := (
 Nor MeasObjectId__Type MeasObjectId__cond ::
 Nor MeasObjectToAddMod__measObject__Type MeasObjectToAddMod__measObject__cond ::
 nil).
Definition MeasObjectToAddMod__cond z := 
  MeasObjectId__cond (MeasObjectToAddMod__measObjectId z) /\
  MeasObjectToAddMod__measObject__cond (MeasObjectToAddMod__measObject z) /\
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
Definition MeasObjectToAddMod__measObject__root__F1 (z : MeasObjectToAddMod__measObject__root__Type) : MeasObjectNR__Type := 
  match z with
  | MeasObjectToAddMod__measObject__root__measObjectNR t => t
  end.
Definition MeasObjectToAddMod__measObject__root__F2 (y : MeasObjectNR__Type) : MeasObjectToAddMod__measObject__root__Type := MeasObjectToAddMod__measObject__root__measObjectNR y.

Definition MeasObjectToAddMod__measObject__root__helper2 : (forall z : MeasObjectToAddMod__measObject__root__Type, MeasObjectToAddMod__measObject__root__cond z -> MeasObjectNR__cond (MeasObjectToAddMod__measObject__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition MeasObjectToAddMod__measObject__root__helper3 : (forall z : MeasObjectToAddMod__measObject__root__Type, MeasObjectToAddMod__measObject__root__F2 (MeasObjectToAddMod__measObject__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition MeasObjectToAddMod__measObject__root__helper4 : (forall y : MeasObjectNR__Type, MeasObjectNR__cond y -> MeasObjectToAddMod__measObject__root__cond (MeasObjectToAddMod__measObject__root__F2 y) /\  MeasObjectToAddMod__measObject__root__F1 (MeasObjectToAddMod__measObject__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition MeasObjectToAddMod__measObject__root__Format : T_Format MeasObjectToAddMod__measObject__root__Type MeasObjectToAddMod__measObject__root__cond :=
  proj2_format MeasObjectToAddMod__measObject__root__cond MeasObjectNR__Format MeasObjectToAddMod__measObject__root__F1 MeasObjectToAddMod__measObject__root__F2 MeasObjectToAddMod__measObject__root__helper2 MeasObjectToAddMod__measObject__root__helper3 MeasObjectToAddMod__measObject__root__helper4.
Opaque MeasObjectToAddMod__measObject__root__cond MeasObjectToAddMod__measObject__root__Format.


Definition MeasObjectToAddMod__measObject__ext__Format_Type := Eval cbn in get_formats MeasObjectToAddMod__measObject__ext__list.
Definition MeasObjectToAddMod__measObject__ext__Format_list : MeasObjectToAddMod__measObject__ext__Format_Type :=
  (MeasObjectEUTRA__Format, (MeasObjectUTRA_FDD_r16__Format, (MeasObjectNR_SL_r16__Format, (MeasObjectCLI_r16__Format, (MeasObjectRxTxDiff_r17__Format, (SL_MeasObject_r16__Format, unit__Format)))))).
Definition MeasObjectToAddMod__measObject__ext__list__Format := Eval compute in choice_ext_format MeasObjectToAddMod__measObject__ext__list MeasObjectToAddMod__measObject__ext__Format_list.
Definition MeasObjectToAddMod__measObject__ext__F1 (z : MeasObjectToAddMod__measObject__ext__Type) : (choice MeasObjectToAddMod__measObject__ext__list) :=
  match z with
   | MeasObjectToAddMod__measObject__ext__measObjectEUTRA t => existT _ 0 t
  | MeasObjectToAddMod__measObject__ext__measObjectUTRA_FDD_r16 t => existT _ 1 t
  | MeasObjectToAddMod__measObject__ext__measObjectNR_SL_r16 t => existT _ 2 t
  | MeasObjectToAddMod__measObject__ext__measObjectCLI_r16 t => existT _ 3 t
  | MeasObjectToAddMod__measObject__ext__measObjectRxTxDiff_r17 t => existT _ 4 t
  | MeasObjectToAddMod__measObject__ext__measObjectRelay_r17 t => existT _ 5 t
  end.
Definition MeasObjectToAddMod__measObject__ext__g := (fun n => typ_set (get_nth_typ MeasObjectToAddMod__measObject__ext__list n)).
Definition MeasObjectToAddMod__measObject__ext__F2 (y : choice MeasObjectToAddMod__measObject__ext__list) : MeasObjectToAddMod__measObject__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasObjectToAddMod__measObject__ext__g n -> MeasObjectToAddMod__measObject__ext__Type) with
    | 0 => fun (t : MeasObjectEUTRA__Type) => MeasObjectToAddMod__measObject__ext__measObjectEUTRA t 
    | 1 => fun (t : MeasObjectUTRA_FDD_r16__Type) => MeasObjectToAddMod__measObject__ext__measObjectUTRA_FDD_r16 t 
    | 2 => fun (t : MeasObjectNR_SL_r16__Type) => MeasObjectToAddMod__measObject__ext__measObjectNR_SL_r16 t 
    | 3 => fun (t : MeasObjectCLI_r16__Type) => MeasObjectToAddMod__measObject__ext__measObjectCLI_r16 t 
    | 4 => fun (t : MeasObjectRxTxDiff_r17__Type) => MeasObjectToAddMod__measObject__ext__measObjectRxTxDiff_r17 t 
    | 5 => fun (t : SL_MeasObject_r16__Type) => MeasObjectToAddMod__measObject__ext__measObjectRelay_r17 t 
 | (S (S (S (S (S (S n0)))))) => (fun (x' : nat) (t'' : MeasObjectToAddMod__measObject__ext__g (S (S (S (S (S (S x'))))))) =>let t' :=
                       eq_rect (get_nth_typ MeasObjectToAddMod__measObject__ext__list (S (S (S (S (S (S x')))))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len MeasObjectToAddMod__measObject__ext__list (S (S (S (S (S (S x'))))))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))) in match t' return MeasObjectToAddMod__measObject__ext__Type with end) n0
                       end t0).

Lemma MeasObjectToAddMod__measObject__ext__helper2 :  forall (y : MeasObjectToAddMod__measObject__ext__Type), MeasObjectToAddMod__measObject__ext__cond y -> choice_cond MeasObjectToAddMod__measObject__ext__list (MeasObjectToAddMod__measObject__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasObjectToAddMod__measObject__ext__helper3 :  forall (y : MeasObjectToAddMod__measObject__ext__Type), MeasObjectToAddMod__measObject__ext__F2 (MeasObjectToAddMod__measObject__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasObjectToAddMod__measObject__ext__helper4 : (forall b : choice MeasObjectToAddMod__measObject__ext__list, choice_cond MeasObjectToAddMod__measObject__ext__list b -> MeasObjectToAddMod__measObject__ext__cond (MeasObjectToAddMod__measObject__ext__F2 b) /\ MeasObjectToAddMod__measObject__ext__F1 (MeasObjectToAddMod__measObject__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasObjectToAddMod__measObject__ext__F1 MeasObjectToAddMod__measObject__ext__F2.
Definition MeasObjectToAddMod__measObject__ext__Format : T_Format MeasObjectToAddMod__measObject__ext__Type MeasObjectToAddMod__measObject__ext__cond :=
          proj2_format MeasObjectToAddMod__measObject__ext__cond MeasObjectToAddMod__measObject__ext__list__Format MeasObjectToAddMod__measObject__ext__F1 MeasObjectToAddMod__measObject__ext__F2 MeasObjectToAddMod__measObject__ext__helper2 MeasObjectToAddMod__measObject__ext__helper3 MeasObjectToAddMod__measObject__ext__helper4.
Opaque MeasObjectToAddMod__measObject__ext__cond MeasObjectToAddMod__measObject__ext__Format.

Definition MeasObjectToAddMod__measObject__Format : T_Format MeasObjectToAddMod__measObject__Type MeasObjectToAddMod__measObject__cond := sum_format MeasObjectToAddMod__measObject__root__Format MeasObjectToAddMod__measObject__ext__Format.
Opaque MeasObjectToAddMod__measObject__cond MeasObjectToAddMod__measObject__Format.


Definition MeasObjectToAddMod__Format_Type := Eval cbn in seq_format_prod MeasObjectToAddMod__list.
Definition MeasObjectToAddMod__Format_list : MeasObjectToAddMod__Format_Type :=
  (MeasObjectId__Format, (MeasObjectToAddMod__measObject__Format, unit_format)).
Definition MeasObjectToAddMod__list__Format := (*Eval compute in *) seq_format MeasObjectToAddMod__list MeasObjectToAddMod__Format_list.
Definition MeasObjectToAddMod__F1 z :=
  (MeasObjectToAddMod__measObjectId z, (MeasObjectToAddMod__measObject z, tt)).
Definition MeasObjectToAddMod__F2 (y : seq_type MeasObjectToAddMod__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasObjectToAddMod__Type i0 i1
  end.
Lemma MeasObjectToAddMod__F1F2_cond (z : MeasObjectToAddMod__Type)
  : MeasObjectToAddMod__cond z ->
  (seq_cond MeasObjectToAddMod__list (MeasObjectToAddMod__F1 z)).
intro H. unfold MeasObjectToAddMod__cond in H. simpl. auto. Qed.
Lemma MeasObjectToAddMod__F1F2_cond2 (z : MeasObjectToAddMod__Type)
 : MeasObjectToAddMod__F2 (MeasObjectToAddMod__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasObjectToAddMod__F2F1_cond (y : seq_type MeasObjectToAddMod__list)
  : seq_cond MeasObjectToAddMod__list y ->
 (MeasObjectToAddMod__cond (MeasObjectToAddMod__F2 y)) /\  MeasObjectToAddMod__F1 (MeasObjectToAddMod__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasObjectToAddMod__cond. simpl in *. auto.
 - simpl. unfold MeasObjectToAddMod__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasObjectToAddMod__Format : T_Format MeasObjectToAddMod__Type MeasObjectToAddMod__cond :=
        proj2_format  MeasObjectToAddMod__cond MeasObjectToAddMod__list__Format
    MeasObjectToAddMod__F1 MeasObjectToAddMod__F2 MeasObjectToAddMod__F1F2_cond  MeasObjectToAddMod__F1F2_cond2 MeasObjectToAddMod__F2F1_cond.
Opaque MeasObjectToAddMod__cond MeasObjectToAddMod__Format.

