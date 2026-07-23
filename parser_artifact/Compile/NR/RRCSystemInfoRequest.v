Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRCSystemInfoRequest_IEs.

Opaque RRCSystemInfoRequest_IEs__cond RRCSystemInfoRequest_IEs__Format.

Require Import NR.RRC_PosSystemInfoRequest_r16_IEs.

Opaque RRC_PosSystemInfoRequest_r16_IEs__cond RRC_PosSystemInfoRequest_r16_IEs__Format.

Record RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type : Set := make__RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type {}.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__cond (z : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type) := True.

Inductive RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type : Set :=
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__rrcPosSystemInfoRequest_r16 : RRC_PosSystemInfoRequest_r16_IEs__Type -> RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type -> RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type
.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list : list typ := (
typ_cons RRC_PosSystemInfoRequest_r16_IEs__Type RRC_PosSystemInfoRequest_r16_IEs__cond ::
typ_cons RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__cond ::
 nil).
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond (c : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type) := 
  match c with
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__rrcPosSystemInfoRequest_r16 t => RRC_PosSystemInfoRequest_r16_IEs__cond t 
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture t => RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__cond t 
  end.

Lemma RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__len_helper1 : to_bit_sz (length RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__len_helper2 : 2 <= length2 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list.
 simpl. lia. Qed.

Inductive RRCSystemInfoRequest__criticalExtensions__Type : Set :=
  | RRCSystemInfoRequest__criticalExtensions__rrcSystemInfoRequest : RRCSystemInfoRequest_IEs__Type -> RRCSystemInfoRequest__criticalExtensions__Type
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16 : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type -> RRCSystemInfoRequest__criticalExtensions__Type
.
Definition RRCSystemInfoRequest__criticalExtensions__list : list typ := (
typ_cons RRCSystemInfoRequest_IEs__Type RRCSystemInfoRequest_IEs__cond ::
typ_cons RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond ::
 nil).
Definition RRCSystemInfoRequest__criticalExtensions__cond (c : RRCSystemInfoRequest__criticalExtensions__Type) := 
  match c with
  | RRCSystemInfoRequest__criticalExtensions__rrcSystemInfoRequest t => RRCSystemInfoRequest_IEs__cond t 
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16 t => RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond t 
  end.

Lemma RRCSystemInfoRequest__criticalExtensions__len_helper1 : to_bit_sz (length RRCSystemInfoRequest__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCSystemInfoRequest__criticalExtensions__len_helper2 : 2 <= length2 RRCSystemInfoRequest__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCSystemInfoRequest__Type : Set :=
  make__RRCSystemInfoRequest__Type {
    RRCSystemInfoRequest__criticalExtensions : RRCSystemInfoRequest__criticalExtensions__Type ;
}.
Definition RRCSystemInfoRequest__list := (
 Nor RRCSystemInfoRequest__criticalExtensions__Type RRCSystemInfoRequest__criticalExtensions__cond ::
 nil).
Definition RRCSystemInfoRequest__cond z := 
  RRCSystemInfoRequest__criticalExtensions__cond (RRCSystemInfoRequest__criticalExtensions z) /\
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
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__helper : forall a : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type, True -> True /\ make__RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Format : T_Format RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type)
    RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__cond RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Format.


Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format_Type := Eval cbn in get_formats RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format_list : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format_Type :=
  (RRC_PosSystemInfoRequest_r16_IEs__Format, (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list__Format := Eval compute in choice_format RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__len_helper1 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__len_helper2  RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format_list.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F1 (z : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type) : (choice RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list) :=
  match z with
   | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__rrcPosSystemInfoRequest_r16 t => existT _ 0 t
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__g := (fun n => typ_set (get_nth_typ RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list n)).
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F2 (y : choice RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list) : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__g n -> RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type) with
    | 0 => fun (t : RRC_PosSystemInfoRequest_r16_IEs__Type) => RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__rrcPosSystemInfoRequest_r16 t 
    | 1 => fun (t : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture__Type) => RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type with end) n0
           end t0).

Lemma RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__helper2 :  forall (y : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type), RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond y -> choice_cond RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__helper3 :  forall (y : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type), RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F2 (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__helper4 : (forall b : choice RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list, choice_cond RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list b -> RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F2 b) /\ RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F1 (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F1 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F2.
Definition RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format : T_Format RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond :=
  (* Eval compute in *) proj2_format RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__list__Format RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F1 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__F2 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__helper2 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__helper3 RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__helper4.
Opaque RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__cond RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format.


Definition RRCSystemInfoRequest__criticalExtensions__Format_Type := Eval cbn in get_formats RRCSystemInfoRequest__criticalExtensions__list.
Definition RRCSystemInfoRequest__criticalExtensions__Format_list : RRCSystemInfoRequest__criticalExtensions__Format_Type :=
  (RRCSystemInfoRequest_IEs__Format, (RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Format, unit__Format)).
Definition RRCSystemInfoRequest__criticalExtensions__list__Format := Eval compute in choice_format RRCSystemInfoRequest__criticalExtensions__list RRCSystemInfoRequest__criticalExtensions__len_helper1 RRCSystemInfoRequest__criticalExtensions__len_helper2  RRCSystemInfoRequest__criticalExtensions__Format_list.
Definition RRCSystemInfoRequest__criticalExtensions__F1 (z : RRCSystemInfoRequest__criticalExtensions__Type) : (choice RRCSystemInfoRequest__criticalExtensions__list) :=
  match z with
   | RRCSystemInfoRequest__criticalExtensions__rrcSystemInfoRequest t => existT _ 0 t
  | RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16 t => existT _ 1 t
  end.
Definition RRCSystemInfoRequest__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCSystemInfoRequest__criticalExtensions__list n)).
Definition RRCSystemInfoRequest__criticalExtensions__F2 (y : choice RRCSystemInfoRequest__criticalExtensions__list) : RRCSystemInfoRequest__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCSystemInfoRequest__criticalExtensions__g n -> RRCSystemInfoRequest__criticalExtensions__Type) with
    | 0 => fun (t : RRCSystemInfoRequest_IEs__Type) => RRCSystemInfoRequest__criticalExtensions__rrcSystemInfoRequest t 
    | 1 => fun (t : RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16__Type) => RRCSystemInfoRequest__criticalExtensions__criticalExtensionsFuture_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCSystemInfoRequest__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCSystemInfoRequest__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCSystemInfoRequest__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCSystemInfoRequest__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCSystemInfoRequest__criticalExtensions__helper2 :  forall (y : RRCSystemInfoRequest__criticalExtensions__Type), RRCSystemInfoRequest__criticalExtensions__cond y -> choice_cond RRCSystemInfoRequest__criticalExtensions__list (RRCSystemInfoRequest__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCSystemInfoRequest__criticalExtensions__helper3 :  forall (y : RRCSystemInfoRequest__criticalExtensions__Type), RRCSystemInfoRequest__criticalExtensions__F2 (RRCSystemInfoRequest__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCSystemInfoRequest__criticalExtensions__helper4 : (forall b : choice RRCSystemInfoRequest__criticalExtensions__list, choice_cond RRCSystemInfoRequest__criticalExtensions__list b -> RRCSystemInfoRequest__criticalExtensions__cond (RRCSystemInfoRequest__criticalExtensions__F2 b) /\ RRCSystemInfoRequest__criticalExtensions__F1 (RRCSystemInfoRequest__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCSystemInfoRequest__criticalExtensions__F1 RRCSystemInfoRequest__criticalExtensions__F2.
Definition RRCSystemInfoRequest__criticalExtensions__Format : T_Format RRCSystemInfoRequest__criticalExtensions__Type RRCSystemInfoRequest__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCSystemInfoRequest__criticalExtensions__cond RRCSystemInfoRequest__criticalExtensions__list__Format RRCSystemInfoRequest__criticalExtensions__F1 RRCSystemInfoRequest__criticalExtensions__F2 RRCSystemInfoRequest__criticalExtensions__helper2 RRCSystemInfoRequest__criticalExtensions__helper3 RRCSystemInfoRequest__criticalExtensions__helper4.
Opaque RRCSystemInfoRequest__criticalExtensions__cond RRCSystemInfoRequest__criticalExtensions__Format.


Definition RRCSystemInfoRequest__Format_Type := Eval cbn in seq_format_prod RRCSystemInfoRequest__list.
Definition RRCSystemInfoRequest__Format_list : RRCSystemInfoRequest__Format_Type :=
  (RRCSystemInfoRequest__criticalExtensions__Format, unit_format).
Definition RRCSystemInfoRequest__list__Format := (*Eval compute in *) seq_format RRCSystemInfoRequest__list RRCSystemInfoRequest__Format_list.
Definition RRCSystemInfoRequest__F1 z :=
  (RRCSystemInfoRequest__criticalExtensions z, tt).
Definition RRCSystemInfoRequest__F2 (y : seq_type RRCSystemInfoRequest__list) :=
  match y with
  | (i0, _)=>
    make__RRCSystemInfoRequest__Type i0
  end.
Lemma RRCSystemInfoRequest__F1F2_cond (z : RRCSystemInfoRequest__Type)
  : RRCSystemInfoRequest__cond z ->
  (seq_cond RRCSystemInfoRequest__list (RRCSystemInfoRequest__F1 z)).
intro H. unfold RRCSystemInfoRequest__cond in H. simpl. auto. Qed.
Lemma RRCSystemInfoRequest__F1F2_cond2 (z : RRCSystemInfoRequest__Type)
 : RRCSystemInfoRequest__F2 (RRCSystemInfoRequest__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSystemInfoRequest__F2F1_cond (y : seq_type RRCSystemInfoRequest__list)
  : seq_cond RRCSystemInfoRequest__list y ->
 (RRCSystemInfoRequest__cond (RRCSystemInfoRequest__F2 y)) /\  RRCSystemInfoRequest__F1 (RRCSystemInfoRequest__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSystemInfoRequest__cond. simpl in *. auto.
 - simpl. unfold RRCSystemInfoRequest__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSystemInfoRequest__Format : T_Format RRCSystemInfoRequest__Type RRCSystemInfoRequest__cond :=
        proj2_format  RRCSystemInfoRequest__cond RRCSystemInfoRequest__list__Format
    RRCSystemInfoRequest__F1 RRCSystemInfoRequest__F2 RRCSystemInfoRequest__F1F2_cond  RRCSystemInfoRequest__F1F2_cond2 RRCSystemInfoRequest__F2F1_cond.
Opaque RRCSystemInfoRequest__cond RRCSystemInfoRequest__Format.

