Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MBSBroadcastConfiguration_r17.

Opaque MBSBroadcastConfiguration_r17__cond MBSBroadcastConfiguration_r17__Format.


Inductive MCCH_MessageType_r17__c1__Type : Set :=
  | MCCH_MessageType_r17__c1__mbsBroadcastConfiguration_r17 : MBSBroadcastConfiguration_r17__Type -> MCCH_MessageType_r17__c1__Type
  | MCCH_MessageType_r17__c1__spare1 : unit -> MCCH_MessageType_r17__c1__Type
.
Definition MCCH_MessageType_r17__c1__list : list typ := (
typ_cons MBSBroadcastConfiguration_r17__Type MBSBroadcastConfiguration_r17__cond ::
typ_cons unit (fun _ => True) ::
 nil).
Definition MCCH_MessageType_r17__c1__cond (c : MCCH_MessageType_r17__c1__Type) := 
  match c with
  | MCCH_MessageType_r17__c1__mbsBroadcastConfiguration_r17 t => MBSBroadcastConfiguration_r17__cond t 
  | MCCH_MessageType_r17__c1__spare1 t => (fun _ => True) t 
  end.

Lemma MCCH_MessageType_r17__c1__len_helper1 : to_bit_sz (length MCCH_MessageType_r17__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MCCH_MessageType_r17__c1__len_helper2 : 2 <= length2 MCCH_MessageType_r17__c1__list.
 simpl. lia. Qed.
Record MCCH_MessageType_r17__messageClassExtension__Type : Set := make__MCCH_MessageType_r17__messageClassExtension__Type {}.
Definition MCCH_MessageType_r17__messageClassExtension__cond (z : MCCH_MessageType_r17__messageClassExtension__Type) := True.

Inductive MCCH_MessageType_r17__Type : Set :=
  | MCCH_MessageType_r17__c1 : MCCH_MessageType_r17__c1__Type -> MCCH_MessageType_r17__Type
  | MCCH_MessageType_r17__messageClassExtension : MCCH_MessageType_r17__messageClassExtension__Type -> MCCH_MessageType_r17__Type
.
Definition MCCH_MessageType_r17__list : list typ := (
typ_cons MCCH_MessageType_r17__c1__Type MCCH_MessageType_r17__c1__cond ::
typ_cons MCCH_MessageType_r17__messageClassExtension__Type MCCH_MessageType_r17__messageClassExtension__cond ::
 nil).
Definition MCCH_MessageType_r17__cond (c : MCCH_MessageType_r17__Type) := 
  match c with
  | MCCH_MessageType_r17__c1 t => MCCH_MessageType_r17__c1__cond t 
  | MCCH_MessageType_r17__messageClassExtension t => MCCH_MessageType_r17__messageClassExtension__cond t 
  end.

Lemma MCCH_MessageType_r17__len_helper1 : to_bit_sz (length MCCH_MessageType_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MCCH_MessageType_r17__len_helper2 : 2 <= length2 MCCH_MessageType_r17__list.
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

Definition MCCH_MessageType_r17__c1__Format_Type := Eval cbn in get_formats MCCH_MessageType_r17__c1__list.
Definition MCCH_MessageType_r17__c1__Format_list : MCCH_MessageType_r17__c1__Format_Type :=
  (MBSBroadcastConfiguration_r17__Format, (unit__Format, unit__Format)).
Definition MCCH_MessageType_r17__c1__list__Format := Eval compute in choice_format MCCH_MessageType_r17__c1__list MCCH_MessageType_r17__c1__len_helper1 MCCH_MessageType_r17__c1__len_helper2  MCCH_MessageType_r17__c1__Format_list.
Definition MCCH_MessageType_r17__c1__F1 (z : MCCH_MessageType_r17__c1__Type) : (choice MCCH_MessageType_r17__c1__list) :=
  match z with
   | MCCH_MessageType_r17__c1__mbsBroadcastConfiguration_r17 t => existT _ 0 t
  | MCCH_MessageType_r17__c1__spare1 t => existT _ 1 t
  end.
Definition MCCH_MessageType_r17__c1__g := (fun n => typ_set (get_nth_typ MCCH_MessageType_r17__c1__list n)).
Definition MCCH_MessageType_r17__c1__F2 (y : choice MCCH_MessageType_r17__c1__list) : MCCH_MessageType_r17__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MCCH_MessageType_r17__c1__g n -> MCCH_MessageType_r17__c1__Type) with
    | 0 => fun (t : MBSBroadcastConfiguration_r17__Type) => MCCH_MessageType_r17__c1__mbsBroadcastConfiguration_r17 t 
    | 1 => fun (t : unit) => MCCH_MessageType_r17__c1__spare1 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MCCH_MessageType_r17__c1__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MCCH_MessageType_r17__c1__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MCCH_MessageType_r17__c1__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MCCH_MessageType_r17__c1__Type with end) n0
           end t0).

Lemma MCCH_MessageType_r17__c1__helper2 :  forall (y : MCCH_MessageType_r17__c1__Type), MCCH_MessageType_r17__c1__cond y -> choice_cond MCCH_MessageType_r17__c1__list (MCCH_MessageType_r17__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MCCH_MessageType_r17__c1__helper3 :  forall (y : MCCH_MessageType_r17__c1__Type), MCCH_MessageType_r17__c1__F2 (MCCH_MessageType_r17__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MCCH_MessageType_r17__c1__helper4 : (forall b : choice MCCH_MessageType_r17__c1__list, choice_cond MCCH_MessageType_r17__c1__list b -> MCCH_MessageType_r17__c1__cond (MCCH_MessageType_r17__c1__F2 b) /\ MCCH_MessageType_r17__c1__F1 (MCCH_MessageType_r17__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MCCH_MessageType_r17__c1__F1 MCCH_MessageType_r17__c1__F2.
Definition MCCH_MessageType_r17__c1__Format : T_Format MCCH_MessageType_r17__c1__Type MCCH_MessageType_r17__c1__cond :=
  (* Eval compute in *) proj2_format MCCH_MessageType_r17__c1__cond MCCH_MessageType_r17__c1__list__Format MCCH_MessageType_r17__c1__F1 MCCH_MessageType_r17__c1__F2 MCCH_MessageType_r17__c1__helper2 MCCH_MessageType_r17__c1__helper3 MCCH_MessageType_r17__c1__helper4.
Opaque MCCH_MessageType_r17__c1__cond MCCH_MessageType_r17__c1__Format.

Definition MCCH_MessageType_r17__messageClassExtension__helper : forall a : MCCH_MessageType_r17__messageClassExtension__Type, True -> True /\ make__MCCH_MessageType_r17__messageClassExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition MCCH_MessageType_r17__messageClassExtension__Format : T_Format MCCH_MessageType_r17__messageClassExtension__Type MCCH_MessageType_r17__messageClassExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MCCH_MessageType_r17__messageClassExtension__Type)
    MCCH_MessageType_r17__messageClassExtension__helper unit_unique (fun _ => left I).

Opaque MCCH_MessageType_r17__messageClassExtension__cond MCCH_MessageType_r17__messageClassExtension__Format.


Definition MCCH_MessageType_r17__Format_Type := Eval cbn in get_formats MCCH_MessageType_r17__list.
Definition MCCH_MessageType_r17__Format_list : MCCH_MessageType_r17__Format_Type :=
  (MCCH_MessageType_r17__c1__Format, (MCCH_MessageType_r17__messageClassExtension__Format, unit__Format)).
Definition MCCH_MessageType_r17__list__Format := Eval compute in choice_format MCCH_MessageType_r17__list MCCH_MessageType_r17__len_helper1 MCCH_MessageType_r17__len_helper2  MCCH_MessageType_r17__Format_list.
Definition MCCH_MessageType_r17__F1 (z : MCCH_MessageType_r17__Type) : (choice MCCH_MessageType_r17__list) :=
  match z with
   | MCCH_MessageType_r17__c1 t => existT _ 0 t
  | MCCH_MessageType_r17__messageClassExtension t => existT _ 1 t
  end.
Definition MCCH_MessageType_r17__g := (fun n => typ_set (get_nth_typ MCCH_MessageType_r17__list n)).
Definition MCCH_MessageType_r17__F2 (y : choice MCCH_MessageType_r17__list) : MCCH_MessageType_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MCCH_MessageType_r17__g n -> MCCH_MessageType_r17__Type) with
    | 0 => fun (t : MCCH_MessageType_r17__c1__Type) => MCCH_MessageType_r17__c1 t 
    | 1 => fun (t : MCCH_MessageType_r17__messageClassExtension__Type) => MCCH_MessageType_r17__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MCCH_MessageType_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MCCH_MessageType_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MCCH_MessageType_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MCCH_MessageType_r17__Type with end) n0
           end t0).

Lemma MCCH_MessageType_r17__helper2 :  forall (y : MCCH_MessageType_r17__Type), MCCH_MessageType_r17__cond y -> choice_cond MCCH_MessageType_r17__list (MCCH_MessageType_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MCCH_MessageType_r17__helper3 :  forall (y : MCCH_MessageType_r17__Type), MCCH_MessageType_r17__F2 (MCCH_MessageType_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MCCH_MessageType_r17__helper4 : (forall b : choice MCCH_MessageType_r17__list, choice_cond MCCH_MessageType_r17__list b -> MCCH_MessageType_r17__cond (MCCH_MessageType_r17__F2 b) /\ MCCH_MessageType_r17__F1 (MCCH_MessageType_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MCCH_MessageType_r17__F1 MCCH_MessageType_r17__F2.
Definition MCCH_MessageType_r17__Format : T_Format MCCH_MessageType_r17__Type MCCH_MessageType_r17__cond :=
  (* Eval compute in *) proj2_format MCCH_MessageType_r17__cond MCCH_MessageType_r17__list__Format MCCH_MessageType_r17__F1 MCCH_MessageType_r17__F2 MCCH_MessageType_r17__helper2 MCCH_MessageType_r17__helper3 MCCH_MessageType_r17__helper4.
Opaque MCCH_MessageType_r17__cond MCCH_MessageType_r17__Format.

