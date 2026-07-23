Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RemoteUEInformationSidelink_r17_IEs.

Opaque RemoteUEInformationSidelink_r17_IEs__cond RemoteUEInformationSidelink_r17_IEs__Format.

Record RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond (z : RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RemoteUEInformationSidelink_r17__criticalExtensions__Type : Set :=
  | RemoteUEInformationSidelink_r17__criticalExtensions__remoteUEInformationSidelink_r17 : RemoteUEInformationSidelink_r17_IEs__Type -> RemoteUEInformationSidelink_r17__criticalExtensions__Type
  | RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture : RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type -> RemoteUEInformationSidelink_r17__criticalExtensions__Type
.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__list : list typ := (
typ_cons RemoteUEInformationSidelink_r17_IEs__Type RemoteUEInformationSidelink_r17_IEs__cond ::
typ_cons RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RemoteUEInformationSidelink_r17__criticalExtensions__cond (c : RemoteUEInformationSidelink_r17__criticalExtensions__Type) := 
  match c with
  | RemoteUEInformationSidelink_r17__criticalExtensions__remoteUEInformationSidelink_r17 t => RemoteUEInformationSidelink_r17_IEs__cond t 
  | RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture t => RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RemoteUEInformationSidelink_r17__criticalExtensions__len_helper1 : to_bit_sz (length RemoteUEInformationSidelink_r17__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RemoteUEInformationSidelink_r17__criticalExtensions__len_helper2 : 2 <= length2 RemoteUEInformationSidelink_r17__criticalExtensions__list.
 simpl. lia. Qed.
Record RemoteUEInformationSidelink_r17__Type : Set :=
  make__RemoteUEInformationSidelink_r17__Type {
    RemoteUEInformationSidelink_r17__criticalExtensions : RemoteUEInformationSidelink_r17__criticalExtensions__Type ;
}.
Definition RemoteUEInformationSidelink_r17__list := (
 Nor RemoteUEInformationSidelink_r17__criticalExtensions__Type RemoteUEInformationSidelink_r17__criticalExtensions__cond ::
 nil).
Definition RemoteUEInformationSidelink_r17__cond z := 
  RemoteUEInformationSidelink_r17__criticalExtensions__cond (RemoteUEInformationSidelink_r17__criticalExtensions z) /\
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
Definition RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__helper : forall a : RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Format : T_Format RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type)
    RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Format.


Definition RemoteUEInformationSidelink_r17__criticalExtensions__Format_Type := Eval cbn in get_formats RemoteUEInformationSidelink_r17__criticalExtensions__list.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__Format_list : RemoteUEInformationSidelink_r17__criticalExtensions__Format_Type :=
  (RemoteUEInformationSidelink_r17_IEs__Format, (RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RemoteUEInformationSidelink_r17__criticalExtensions__list__Format := Eval compute in choice_format RemoteUEInformationSidelink_r17__criticalExtensions__list RemoteUEInformationSidelink_r17__criticalExtensions__len_helper1 RemoteUEInformationSidelink_r17__criticalExtensions__len_helper2  RemoteUEInformationSidelink_r17__criticalExtensions__Format_list.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__F1 (z : RemoteUEInformationSidelink_r17__criticalExtensions__Type) : (choice RemoteUEInformationSidelink_r17__criticalExtensions__list) :=
  match z with
   | RemoteUEInformationSidelink_r17__criticalExtensions__remoteUEInformationSidelink_r17 t => existT _ 0 t
  | RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__g := (fun n => typ_set (get_nth_typ RemoteUEInformationSidelink_r17__criticalExtensions__list n)).
Definition RemoteUEInformationSidelink_r17__criticalExtensions__F2 (y : choice RemoteUEInformationSidelink_r17__criticalExtensions__list) : RemoteUEInformationSidelink_r17__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RemoteUEInformationSidelink_r17__criticalExtensions__g n -> RemoteUEInformationSidelink_r17__criticalExtensions__Type) with
    | 0 => fun (t : RemoteUEInformationSidelink_r17_IEs__Type) => RemoteUEInformationSidelink_r17__criticalExtensions__remoteUEInformationSidelink_r17 t 
    | 1 => fun (t : RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type) => RemoteUEInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RemoteUEInformationSidelink_r17__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RemoteUEInformationSidelink_r17__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RemoteUEInformationSidelink_r17__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RemoteUEInformationSidelink_r17__criticalExtensions__Type with end) n0
           end t0).

Lemma RemoteUEInformationSidelink_r17__criticalExtensions__helper2 :  forall (y : RemoteUEInformationSidelink_r17__criticalExtensions__Type), RemoteUEInformationSidelink_r17__criticalExtensions__cond y -> choice_cond RemoteUEInformationSidelink_r17__criticalExtensions__list (RemoteUEInformationSidelink_r17__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RemoteUEInformationSidelink_r17__criticalExtensions__helper3 :  forall (y : RemoteUEInformationSidelink_r17__criticalExtensions__Type), RemoteUEInformationSidelink_r17__criticalExtensions__F2 (RemoteUEInformationSidelink_r17__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RemoteUEInformationSidelink_r17__criticalExtensions__helper4 : (forall b : choice RemoteUEInformationSidelink_r17__criticalExtensions__list, choice_cond RemoteUEInformationSidelink_r17__criticalExtensions__list b -> RemoteUEInformationSidelink_r17__criticalExtensions__cond (RemoteUEInformationSidelink_r17__criticalExtensions__F2 b) /\ RemoteUEInformationSidelink_r17__criticalExtensions__F1 (RemoteUEInformationSidelink_r17__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RemoteUEInformationSidelink_r17__criticalExtensions__F1 RemoteUEInformationSidelink_r17__criticalExtensions__F2.
Definition RemoteUEInformationSidelink_r17__criticalExtensions__Format : T_Format RemoteUEInformationSidelink_r17__criticalExtensions__Type RemoteUEInformationSidelink_r17__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RemoteUEInformationSidelink_r17__criticalExtensions__cond RemoteUEInformationSidelink_r17__criticalExtensions__list__Format RemoteUEInformationSidelink_r17__criticalExtensions__F1 RemoteUEInformationSidelink_r17__criticalExtensions__F2 RemoteUEInformationSidelink_r17__criticalExtensions__helper2 RemoteUEInformationSidelink_r17__criticalExtensions__helper3 RemoteUEInformationSidelink_r17__criticalExtensions__helper4.
Opaque RemoteUEInformationSidelink_r17__criticalExtensions__cond RemoteUEInformationSidelink_r17__criticalExtensions__Format.


Definition RemoteUEInformationSidelink_r17__Format_Type := Eval cbn in seq_format_prod RemoteUEInformationSidelink_r17__list.
Definition RemoteUEInformationSidelink_r17__Format_list : RemoteUEInformationSidelink_r17__Format_Type :=
  (RemoteUEInformationSidelink_r17__criticalExtensions__Format, unit_format).
Definition RemoteUEInformationSidelink_r17__list__Format := (*Eval compute in *) seq_format RemoteUEInformationSidelink_r17__list RemoteUEInformationSidelink_r17__Format_list.
Definition RemoteUEInformationSidelink_r17__F1 z :=
  (RemoteUEInformationSidelink_r17__criticalExtensions z, tt).
Definition RemoteUEInformationSidelink_r17__F2 (y : seq_type RemoteUEInformationSidelink_r17__list) :=
  match y with
  | (i0, _)=>
    make__RemoteUEInformationSidelink_r17__Type i0
  end.
Lemma RemoteUEInformationSidelink_r17__F1F2_cond (z : RemoteUEInformationSidelink_r17__Type)
  : RemoteUEInformationSidelink_r17__cond z ->
  (seq_cond RemoteUEInformationSidelink_r17__list (RemoteUEInformationSidelink_r17__F1 z)).
intro H. unfold RemoteUEInformationSidelink_r17__cond in H. simpl. auto. Qed.
Lemma RemoteUEInformationSidelink_r17__F1F2_cond2 (z : RemoteUEInformationSidelink_r17__Type)
 : RemoteUEInformationSidelink_r17__F2 (RemoteUEInformationSidelink_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RemoteUEInformationSidelink_r17__F2F1_cond (y : seq_type RemoteUEInformationSidelink_r17__list)
  : seq_cond RemoteUEInformationSidelink_r17__list y ->
 (RemoteUEInformationSidelink_r17__cond (RemoteUEInformationSidelink_r17__F2 y)) /\  RemoteUEInformationSidelink_r17__F1 (RemoteUEInformationSidelink_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RemoteUEInformationSidelink_r17__cond. simpl in *. auto.
 - simpl. unfold RemoteUEInformationSidelink_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RemoteUEInformationSidelink_r17__Format : T_Format RemoteUEInformationSidelink_r17__Type RemoteUEInformationSidelink_r17__cond :=
        proj2_format  RemoteUEInformationSidelink_r17__cond RemoteUEInformationSidelink_r17__list__Format
    RemoteUEInformationSidelink_r17__F1 RemoteUEInformationSidelink_r17__F2 RemoteUEInformationSidelink_r17__F1F2_cond  RemoteUEInformationSidelink_r17__F1F2_cond2 RemoteUEInformationSidelink_r17__F2F1_cond.
Opaque RemoteUEInformationSidelink_r17__cond RemoteUEInformationSidelink_r17__Format.

