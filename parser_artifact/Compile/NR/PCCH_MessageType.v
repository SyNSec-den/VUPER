Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.Paging.

Opaque Paging__cond Paging__Format.


Inductive PCCH_MessageType__c1__Type : Set :=
  | PCCH_MessageType__c1__paging : Paging__Type -> PCCH_MessageType__c1__Type
  | PCCH_MessageType__c1__spare1 : unit -> PCCH_MessageType__c1__Type
.
Definition PCCH_MessageType__c1__list : list typ := (
typ_cons Paging__Type Paging__cond ::
typ_cons unit (fun _ => True) ::
 nil).
Definition PCCH_MessageType__c1__cond (c : PCCH_MessageType__c1__Type) := 
  match c with
  | PCCH_MessageType__c1__paging t => Paging__cond t 
  | PCCH_MessageType__c1__spare1 t => (fun _ => True) t 
  end.

Lemma PCCH_MessageType__c1__len_helper1 : to_bit_sz (length PCCH_MessageType__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PCCH_MessageType__c1__len_helper2 : 2 <= length2 PCCH_MessageType__c1__list.
 simpl. lia. Qed.
Record PCCH_MessageType__messageClassExtension__Type : Set := make__PCCH_MessageType__messageClassExtension__Type {}.
Definition PCCH_MessageType__messageClassExtension__cond (z : PCCH_MessageType__messageClassExtension__Type) := True.

Inductive PCCH_MessageType__Type : Set :=
  | PCCH_MessageType__c1 : PCCH_MessageType__c1__Type -> PCCH_MessageType__Type
  | PCCH_MessageType__messageClassExtension : PCCH_MessageType__messageClassExtension__Type -> PCCH_MessageType__Type
.
Definition PCCH_MessageType__list : list typ := (
typ_cons PCCH_MessageType__c1__Type PCCH_MessageType__c1__cond ::
typ_cons PCCH_MessageType__messageClassExtension__Type PCCH_MessageType__messageClassExtension__cond ::
 nil).
Definition PCCH_MessageType__cond (c : PCCH_MessageType__Type) := 
  match c with
  | PCCH_MessageType__c1 t => PCCH_MessageType__c1__cond t 
  | PCCH_MessageType__messageClassExtension t => PCCH_MessageType__messageClassExtension__cond t 
  end.

Lemma PCCH_MessageType__len_helper1 : to_bit_sz (length PCCH_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PCCH_MessageType__len_helper2 : 2 <= length2 PCCH_MessageType__list.
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

Definition PCCH_MessageType__c1__Format_Type := Eval cbn in get_formats PCCH_MessageType__c1__list.
Definition PCCH_MessageType__c1__Format_list : PCCH_MessageType__c1__Format_Type :=
  (Paging__Format, (unit__Format, unit__Format)).
Definition PCCH_MessageType__c1__list__Format := Eval compute in choice_format PCCH_MessageType__c1__list PCCH_MessageType__c1__len_helper1 PCCH_MessageType__c1__len_helper2  PCCH_MessageType__c1__Format_list.
Definition PCCH_MessageType__c1__F1 (z : PCCH_MessageType__c1__Type) : (choice PCCH_MessageType__c1__list) :=
  match z with
   | PCCH_MessageType__c1__paging t => existT _ 0 t
  | PCCH_MessageType__c1__spare1 t => existT _ 1 t
  end.
Definition PCCH_MessageType__c1__g := (fun n => typ_set (get_nth_typ PCCH_MessageType__c1__list n)).
Definition PCCH_MessageType__c1__F2 (y : choice PCCH_MessageType__c1__list) : PCCH_MessageType__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PCCH_MessageType__c1__g n -> PCCH_MessageType__c1__Type) with
    | 0 => fun (t : Paging__Type) => PCCH_MessageType__c1__paging t 
    | 1 => fun (t : unit) => PCCH_MessageType__c1__spare1 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PCCH_MessageType__c1__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PCCH_MessageType__c1__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PCCH_MessageType__c1__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PCCH_MessageType__c1__Type with end) n0
           end t0).

Lemma PCCH_MessageType__c1__helper2 :  forall (y : PCCH_MessageType__c1__Type), PCCH_MessageType__c1__cond y -> choice_cond PCCH_MessageType__c1__list (PCCH_MessageType__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PCCH_MessageType__c1__helper3 :  forall (y : PCCH_MessageType__c1__Type), PCCH_MessageType__c1__F2 (PCCH_MessageType__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PCCH_MessageType__c1__helper4 : (forall b : choice PCCH_MessageType__c1__list, choice_cond PCCH_MessageType__c1__list b -> PCCH_MessageType__c1__cond (PCCH_MessageType__c1__F2 b) /\ PCCH_MessageType__c1__F1 (PCCH_MessageType__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PCCH_MessageType__c1__F1 PCCH_MessageType__c1__F2.
Definition PCCH_MessageType__c1__Format : T_Format PCCH_MessageType__c1__Type PCCH_MessageType__c1__cond :=
  (* Eval compute in *) proj2_format PCCH_MessageType__c1__cond PCCH_MessageType__c1__list__Format PCCH_MessageType__c1__F1 PCCH_MessageType__c1__F2 PCCH_MessageType__c1__helper2 PCCH_MessageType__c1__helper3 PCCH_MessageType__c1__helper4.
Opaque PCCH_MessageType__c1__cond PCCH_MessageType__c1__Format.

Definition PCCH_MessageType__messageClassExtension__helper : forall a : PCCH_MessageType__messageClassExtension__Type, True -> True /\ make__PCCH_MessageType__messageClassExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition PCCH_MessageType__messageClassExtension__Format : T_Format PCCH_MessageType__messageClassExtension__Type PCCH_MessageType__messageClassExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__PCCH_MessageType__messageClassExtension__Type)
    PCCH_MessageType__messageClassExtension__helper unit_unique (fun _ => left I).

Opaque PCCH_MessageType__messageClassExtension__cond PCCH_MessageType__messageClassExtension__Format.


Definition PCCH_MessageType__Format_Type := Eval cbn in get_formats PCCH_MessageType__list.
Definition PCCH_MessageType__Format_list : PCCH_MessageType__Format_Type :=
  (PCCH_MessageType__c1__Format, (PCCH_MessageType__messageClassExtension__Format, unit__Format)).
Definition PCCH_MessageType__list__Format := Eval compute in choice_format PCCH_MessageType__list PCCH_MessageType__len_helper1 PCCH_MessageType__len_helper2  PCCH_MessageType__Format_list.
Definition PCCH_MessageType__F1 (z : PCCH_MessageType__Type) : (choice PCCH_MessageType__list) :=
  match z with
   | PCCH_MessageType__c1 t => existT _ 0 t
  | PCCH_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition PCCH_MessageType__g := (fun n => typ_set (get_nth_typ PCCH_MessageType__list n)).
Definition PCCH_MessageType__F2 (y : choice PCCH_MessageType__list) : PCCH_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PCCH_MessageType__g n -> PCCH_MessageType__Type) with
    | 0 => fun (t : PCCH_MessageType__c1__Type) => PCCH_MessageType__c1 t 
    | 1 => fun (t : PCCH_MessageType__messageClassExtension__Type) => PCCH_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PCCH_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PCCH_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PCCH_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PCCH_MessageType__Type with end) n0
           end t0).

Lemma PCCH_MessageType__helper2 :  forall (y : PCCH_MessageType__Type), PCCH_MessageType__cond y -> choice_cond PCCH_MessageType__list (PCCH_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PCCH_MessageType__helper3 :  forall (y : PCCH_MessageType__Type), PCCH_MessageType__F2 (PCCH_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PCCH_MessageType__helper4 : (forall b : choice PCCH_MessageType__list, choice_cond PCCH_MessageType__list b -> PCCH_MessageType__cond (PCCH_MessageType__F2 b) /\ PCCH_MessageType__F1 (PCCH_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PCCH_MessageType__F1 PCCH_MessageType__F2.
Definition PCCH_MessageType__Format : T_Format PCCH_MessageType__Type PCCH_MessageType__cond :=
  (* Eval compute in *) proj2_format PCCH_MessageType__cond PCCH_MessageType__list__Format PCCH_MessageType__F1 PCCH_MessageType__F2 PCCH_MessageType__helper2 PCCH_MessageType__helper3 PCCH_MessageType__helper4.
Opaque PCCH_MessageType__cond PCCH_MessageType__Format.

