Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MBSInterestIndication_r17_IEs.

Opaque MBSInterestIndication_r17_IEs__cond MBSInterestIndication_r17_IEs__Format.

Record MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type : Set := make__MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__cond (z : MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive MBSInterestIndication_r17__criticalExtensions__Type : Set :=
  | MBSInterestIndication_r17__criticalExtensions__mbsInterestIndication_r17 : MBSInterestIndication_r17_IEs__Type -> MBSInterestIndication_r17__criticalExtensions__Type
  | MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture : MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type -> MBSInterestIndication_r17__criticalExtensions__Type
.
Definition MBSInterestIndication_r17__criticalExtensions__list : list typ := (
typ_cons MBSInterestIndication_r17_IEs__Type MBSInterestIndication_r17_IEs__cond ::
typ_cons MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition MBSInterestIndication_r17__criticalExtensions__cond (c : MBSInterestIndication_r17__criticalExtensions__Type) := 
  match c with
  | MBSInterestIndication_r17__criticalExtensions__mbsInterestIndication_r17 t => MBSInterestIndication_r17_IEs__cond t 
  | MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture t => MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma MBSInterestIndication_r17__criticalExtensions__len_helper1 : to_bit_sz (length MBSInterestIndication_r17__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MBSInterestIndication_r17__criticalExtensions__len_helper2 : 2 <= length2 MBSInterestIndication_r17__criticalExtensions__list.
 simpl. lia. Qed.
Record MBSInterestIndication_r17__Type : Set :=
  make__MBSInterestIndication_r17__Type {
    MBSInterestIndication_r17__criticalExtensions : MBSInterestIndication_r17__criticalExtensions__Type ;
}.
Definition MBSInterestIndication_r17__list := (
 Nor MBSInterestIndication_r17__criticalExtensions__Type MBSInterestIndication_r17__criticalExtensions__cond ::
 nil).
Definition MBSInterestIndication_r17__cond z := 
  MBSInterestIndication_r17__criticalExtensions__cond (MBSInterestIndication_r17__criticalExtensions z) /\
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
Definition MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__helper : forall a : MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Format : T_Format MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type)
    MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__cond MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Format.


Definition MBSInterestIndication_r17__criticalExtensions__Format_Type := Eval cbn in get_formats MBSInterestIndication_r17__criticalExtensions__list.
Definition MBSInterestIndication_r17__criticalExtensions__Format_list : MBSInterestIndication_r17__criticalExtensions__Format_Type :=
  (MBSInterestIndication_r17_IEs__Format, (MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition MBSInterestIndication_r17__criticalExtensions__list__Format := Eval compute in choice_format MBSInterestIndication_r17__criticalExtensions__list MBSInterestIndication_r17__criticalExtensions__len_helper1 MBSInterestIndication_r17__criticalExtensions__len_helper2  MBSInterestIndication_r17__criticalExtensions__Format_list.
Definition MBSInterestIndication_r17__criticalExtensions__F1 (z : MBSInterestIndication_r17__criticalExtensions__Type) : (choice MBSInterestIndication_r17__criticalExtensions__list) :=
  match z with
   | MBSInterestIndication_r17__criticalExtensions__mbsInterestIndication_r17 t => existT _ 0 t
  | MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition MBSInterestIndication_r17__criticalExtensions__g := (fun n => typ_set (get_nth_typ MBSInterestIndication_r17__criticalExtensions__list n)).
Definition MBSInterestIndication_r17__criticalExtensions__F2 (y : choice MBSInterestIndication_r17__criticalExtensions__list) : MBSInterestIndication_r17__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MBSInterestIndication_r17__criticalExtensions__g n -> MBSInterestIndication_r17__criticalExtensions__Type) with
    | 0 => fun (t : MBSInterestIndication_r17_IEs__Type) => MBSInterestIndication_r17__criticalExtensions__mbsInterestIndication_r17 t 
    | 1 => fun (t : MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type) => MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MBSInterestIndication_r17__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MBSInterestIndication_r17__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MBSInterestIndication_r17__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MBSInterestIndication_r17__criticalExtensions__Type with end) n0
           end t0).

Lemma MBSInterestIndication_r17__criticalExtensions__helper2 :  forall (y : MBSInterestIndication_r17__criticalExtensions__Type), MBSInterestIndication_r17__criticalExtensions__cond y -> choice_cond MBSInterestIndication_r17__criticalExtensions__list (MBSInterestIndication_r17__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MBSInterestIndication_r17__criticalExtensions__helper3 :  forall (y : MBSInterestIndication_r17__criticalExtensions__Type), MBSInterestIndication_r17__criticalExtensions__F2 (MBSInterestIndication_r17__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MBSInterestIndication_r17__criticalExtensions__helper4 : (forall b : choice MBSInterestIndication_r17__criticalExtensions__list, choice_cond MBSInterestIndication_r17__criticalExtensions__list b -> MBSInterestIndication_r17__criticalExtensions__cond (MBSInterestIndication_r17__criticalExtensions__F2 b) /\ MBSInterestIndication_r17__criticalExtensions__F1 (MBSInterestIndication_r17__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MBSInterestIndication_r17__criticalExtensions__F1 MBSInterestIndication_r17__criticalExtensions__F2.
Definition MBSInterestIndication_r17__criticalExtensions__Format : T_Format MBSInterestIndication_r17__criticalExtensions__Type MBSInterestIndication_r17__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format MBSInterestIndication_r17__criticalExtensions__cond MBSInterestIndication_r17__criticalExtensions__list__Format MBSInterestIndication_r17__criticalExtensions__F1 MBSInterestIndication_r17__criticalExtensions__F2 MBSInterestIndication_r17__criticalExtensions__helper2 MBSInterestIndication_r17__criticalExtensions__helper3 MBSInterestIndication_r17__criticalExtensions__helper4.
Opaque MBSInterestIndication_r17__criticalExtensions__cond MBSInterestIndication_r17__criticalExtensions__Format.


Definition MBSInterestIndication_r17__Format_Type := Eval cbn in seq_format_prod MBSInterestIndication_r17__list.
Definition MBSInterestIndication_r17__Format_list : MBSInterestIndication_r17__Format_Type :=
  (MBSInterestIndication_r17__criticalExtensions__Format, unit_format).
Definition MBSInterestIndication_r17__list__Format := (*Eval compute in *) seq_format MBSInterestIndication_r17__list MBSInterestIndication_r17__Format_list.
Definition MBSInterestIndication_r17__F1 z :=
  (MBSInterestIndication_r17__criticalExtensions z, tt).
Definition MBSInterestIndication_r17__F2 (y : seq_type MBSInterestIndication_r17__list) :=
  match y with
  | (i0, _)=>
    make__MBSInterestIndication_r17__Type i0
  end.
Lemma MBSInterestIndication_r17__F1F2_cond (z : MBSInterestIndication_r17__Type)
  : MBSInterestIndication_r17__cond z ->
  (seq_cond MBSInterestIndication_r17__list (MBSInterestIndication_r17__F1 z)).
intro H. unfold MBSInterestIndication_r17__cond in H. simpl. auto. Qed.
Lemma MBSInterestIndication_r17__F1F2_cond2 (z : MBSInterestIndication_r17__Type)
 : MBSInterestIndication_r17__F2 (MBSInterestIndication_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MBSInterestIndication_r17__F2F1_cond (y : seq_type MBSInterestIndication_r17__list)
  : seq_cond MBSInterestIndication_r17__list y ->
 (MBSInterestIndication_r17__cond (MBSInterestIndication_r17__F2 y)) /\  MBSInterestIndication_r17__F1 (MBSInterestIndication_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MBSInterestIndication_r17__cond. simpl in *. auto.
 - simpl. unfold MBSInterestIndication_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MBSInterestIndication_r17__Format : T_Format MBSInterestIndication_r17__Type MBSInterestIndication_r17__cond :=
        proj2_format  MBSInterestIndication_r17__cond MBSInterestIndication_r17__list__Format
    MBSInterestIndication_r17__F1 MBSInterestIndication_r17__F2 MBSInterestIndication_r17__F1F2_cond  MBSInterestIndication_r17__F1F2_cond2 MBSInterestIndication_r17__F2F1_cond.
Opaque MBSInterestIndication_r17__cond MBSInterestIndication_r17__Format.

