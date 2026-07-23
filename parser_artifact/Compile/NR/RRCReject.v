Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRCReject_IEs.

Opaque RRCReject_IEs__cond RRCReject_IEs__Format.

Record RRCReject__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReject__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReject__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReject__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReject__criticalExtensions__Type : Set :=
  | RRCReject__criticalExtensions__rrcReject : RRCReject_IEs__Type -> RRCReject__criticalExtensions__Type
  | RRCReject__criticalExtensions__criticalExtensionsFuture : RRCReject__criticalExtensions__criticalExtensionsFuture__Type -> RRCReject__criticalExtensions__Type
.
Definition RRCReject__criticalExtensions__list : list typ := (
typ_cons RRCReject_IEs__Type RRCReject_IEs__cond ::
typ_cons RRCReject__criticalExtensions__criticalExtensionsFuture__Type RRCReject__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReject__criticalExtensions__cond (c : RRCReject__criticalExtensions__Type) := 
  match c with
  | RRCReject__criticalExtensions__rrcReject t => RRCReject_IEs__cond t 
  | RRCReject__criticalExtensions__criticalExtensionsFuture t => RRCReject__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReject__criticalExtensions__len_helper1 : to_bit_sz (length RRCReject__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReject__criticalExtensions__len_helper2 : 2 <= length2 RRCReject__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReject__Type : Set :=
  make__RRCReject__Type {
    RRCReject__criticalExtensions : RRCReject__criticalExtensions__Type ;
}.
Definition RRCReject__list := (
 Nor RRCReject__criticalExtensions__Type RRCReject__criticalExtensions__cond ::
 nil).
Definition RRCReject__cond z := 
  RRCReject__criticalExtensions__cond (RRCReject__criticalExtensions z) /\
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
Definition RRCReject__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReject__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReject__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReject__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReject__criticalExtensions__criticalExtensionsFuture__Type RRCReject__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReject__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReject__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReject__criticalExtensions__criticalExtensionsFuture__cond RRCReject__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReject__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReject__criticalExtensions__list.
Definition RRCReject__criticalExtensions__Format_list : RRCReject__criticalExtensions__Format_Type :=
  (RRCReject_IEs__Format, (RRCReject__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReject__criticalExtensions__list__Format := Eval compute in choice_format RRCReject__criticalExtensions__list RRCReject__criticalExtensions__len_helper1 RRCReject__criticalExtensions__len_helper2  RRCReject__criticalExtensions__Format_list.
Definition RRCReject__criticalExtensions__F1 (z : RRCReject__criticalExtensions__Type) : (choice RRCReject__criticalExtensions__list) :=
  match z with
   | RRCReject__criticalExtensions__rrcReject t => existT _ 0 t
  | RRCReject__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReject__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReject__criticalExtensions__list n)).
Definition RRCReject__criticalExtensions__F2 (y : choice RRCReject__criticalExtensions__list) : RRCReject__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReject__criticalExtensions__g n -> RRCReject__criticalExtensions__Type) with
    | 0 => fun (t : RRCReject_IEs__Type) => RRCReject__criticalExtensions__rrcReject t 
    | 1 => fun (t : RRCReject__criticalExtensions__criticalExtensionsFuture__Type) => RRCReject__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReject__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReject__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReject__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReject__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReject__criticalExtensions__helper2 :  forall (y : RRCReject__criticalExtensions__Type), RRCReject__criticalExtensions__cond y -> choice_cond RRCReject__criticalExtensions__list (RRCReject__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReject__criticalExtensions__helper3 :  forall (y : RRCReject__criticalExtensions__Type), RRCReject__criticalExtensions__F2 (RRCReject__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReject__criticalExtensions__helper4 : (forall b : choice RRCReject__criticalExtensions__list, choice_cond RRCReject__criticalExtensions__list b -> RRCReject__criticalExtensions__cond (RRCReject__criticalExtensions__F2 b) /\ RRCReject__criticalExtensions__F1 (RRCReject__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReject__criticalExtensions__F1 RRCReject__criticalExtensions__F2.
Definition RRCReject__criticalExtensions__Format : T_Format RRCReject__criticalExtensions__Type RRCReject__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReject__criticalExtensions__cond RRCReject__criticalExtensions__list__Format RRCReject__criticalExtensions__F1 RRCReject__criticalExtensions__F2 RRCReject__criticalExtensions__helper2 RRCReject__criticalExtensions__helper3 RRCReject__criticalExtensions__helper4.
Opaque RRCReject__criticalExtensions__cond RRCReject__criticalExtensions__Format.


Definition RRCReject__Format_Type := Eval cbn in seq_format_prod RRCReject__list.
Definition RRCReject__Format_list : RRCReject__Format_Type :=
  (RRCReject__criticalExtensions__Format, unit_format).
Definition RRCReject__list__Format := (*Eval compute in *) seq_format RRCReject__list RRCReject__Format_list.
Definition RRCReject__F1 z :=
  (RRCReject__criticalExtensions z, tt).
Definition RRCReject__F2 (y : seq_type RRCReject__list) :=
  match y with
  | (i0, _)=>
    make__RRCReject__Type i0
  end.
Lemma RRCReject__F1F2_cond (z : RRCReject__Type)
  : RRCReject__cond z ->
  (seq_cond RRCReject__list (RRCReject__F1 z)).
intro H. unfold RRCReject__cond in H. simpl. auto. Qed.
Lemma RRCReject__F1F2_cond2 (z : RRCReject__Type)
 : RRCReject__F2 (RRCReject__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReject__F2F1_cond (y : seq_type RRCReject__list)
  : seq_cond RRCReject__list y ->
 (RRCReject__cond (RRCReject__F2 y)) /\  RRCReject__F1 (RRCReject__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReject__cond. simpl in *. auto.
 - simpl. unfold RRCReject__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReject__Format : T_Format RRCReject__Type RRCReject__cond :=
        proj2_format  RRCReject__cond RRCReject__list__Format
    RRCReject__F1 RRCReject__F2 RRCReject__F1F2_cond  RRCReject__F1F2_cond2 RRCReject__F2F1_cond.
Opaque RRCReject__cond RRCReject__Format.

