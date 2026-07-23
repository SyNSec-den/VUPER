Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.MasterInformationBlockSidelink.

Opaque MasterInformationBlockSidelink__cond MasterInformationBlockSidelink__Format.


Inductive SBCCH_SL_BCH_MessageType__c1__Type : Set :=
  | SBCCH_SL_BCH_MessageType__c1__masterInformationBlockSidelink : MasterInformationBlockSidelink__Type -> SBCCH_SL_BCH_MessageType__c1__Type
  | SBCCH_SL_BCH_MessageType__c1__spare1 : unit -> SBCCH_SL_BCH_MessageType__c1__Type
.
Definition SBCCH_SL_BCH_MessageType__c1__list : list typ := (
typ_cons MasterInformationBlockSidelink__Type MasterInformationBlockSidelink__cond ::
typ_cons unit (fun _ => True) ::
 nil).
Definition SBCCH_SL_BCH_MessageType__c1__cond (c : SBCCH_SL_BCH_MessageType__c1__Type) := 
  match c with
  | SBCCH_SL_BCH_MessageType__c1__masterInformationBlockSidelink t => MasterInformationBlockSidelink__cond t 
  | SBCCH_SL_BCH_MessageType__c1__spare1 t => (fun _ => True) t 
  end.

Lemma SBCCH_SL_BCH_MessageType__c1__len_helper1 : to_bit_sz (length SBCCH_SL_BCH_MessageType__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SBCCH_SL_BCH_MessageType__c1__len_helper2 : 2 <= length2 SBCCH_SL_BCH_MessageType__c1__list.
 simpl. lia. Qed.
Record SBCCH_SL_BCH_MessageType__messageClassExtension__Type : Set := make__SBCCH_SL_BCH_MessageType__messageClassExtension__Type {}.
Definition SBCCH_SL_BCH_MessageType__messageClassExtension__cond (z : SBCCH_SL_BCH_MessageType__messageClassExtension__Type) := True.

Inductive SBCCH_SL_BCH_MessageType__Type : Set :=
  | SBCCH_SL_BCH_MessageType__c1 : SBCCH_SL_BCH_MessageType__c1__Type -> SBCCH_SL_BCH_MessageType__Type
  | SBCCH_SL_BCH_MessageType__messageClassExtension : SBCCH_SL_BCH_MessageType__messageClassExtension__Type -> SBCCH_SL_BCH_MessageType__Type
.
Definition SBCCH_SL_BCH_MessageType__list : list typ := (
typ_cons SBCCH_SL_BCH_MessageType__c1__Type SBCCH_SL_BCH_MessageType__c1__cond ::
typ_cons SBCCH_SL_BCH_MessageType__messageClassExtension__Type SBCCH_SL_BCH_MessageType__messageClassExtension__cond ::
 nil).
Definition SBCCH_SL_BCH_MessageType__cond (c : SBCCH_SL_BCH_MessageType__Type) := 
  match c with
  | SBCCH_SL_BCH_MessageType__c1 t => SBCCH_SL_BCH_MessageType__c1__cond t 
  | SBCCH_SL_BCH_MessageType__messageClassExtension t => SBCCH_SL_BCH_MessageType__messageClassExtension__cond t 
  end.

Lemma SBCCH_SL_BCH_MessageType__len_helper1 : to_bit_sz (length SBCCH_SL_BCH_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SBCCH_SL_BCH_MessageType__len_helper2 : 2 <= length2 SBCCH_SL_BCH_MessageType__list.
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

Definition SBCCH_SL_BCH_MessageType__c1__Format_Type := Eval cbn in get_formats SBCCH_SL_BCH_MessageType__c1__list.
Definition SBCCH_SL_BCH_MessageType__c1__Format_list : SBCCH_SL_BCH_MessageType__c1__Format_Type :=
  (MasterInformationBlockSidelink__Format, (unit__Format, unit__Format)).
Definition SBCCH_SL_BCH_MessageType__c1__list__Format := Eval compute in choice_format SBCCH_SL_BCH_MessageType__c1__list SBCCH_SL_BCH_MessageType__c1__len_helper1 SBCCH_SL_BCH_MessageType__c1__len_helper2  SBCCH_SL_BCH_MessageType__c1__Format_list.
Definition SBCCH_SL_BCH_MessageType__c1__F1 (z : SBCCH_SL_BCH_MessageType__c1__Type) : (choice SBCCH_SL_BCH_MessageType__c1__list) :=
  match z with
   | SBCCH_SL_BCH_MessageType__c1__masterInformationBlockSidelink t => existT _ 0 t
  | SBCCH_SL_BCH_MessageType__c1__spare1 t => existT _ 1 t
  end.
Definition SBCCH_SL_BCH_MessageType__c1__g := (fun n => typ_set (get_nth_typ SBCCH_SL_BCH_MessageType__c1__list n)).
Definition SBCCH_SL_BCH_MessageType__c1__F2 (y : choice SBCCH_SL_BCH_MessageType__c1__list) : SBCCH_SL_BCH_MessageType__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SBCCH_SL_BCH_MessageType__c1__g n -> SBCCH_SL_BCH_MessageType__c1__Type) with
    | 0 => fun (t : MasterInformationBlockSidelink__Type) => SBCCH_SL_BCH_MessageType__c1__masterInformationBlockSidelink t 
    | 1 => fun (t : unit) => SBCCH_SL_BCH_MessageType__c1__spare1 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SBCCH_SL_BCH_MessageType__c1__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SBCCH_SL_BCH_MessageType__c1__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SBCCH_SL_BCH_MessageType__c1__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SBCCH_SL_BCH_MessageType__c1__Type with end) n0
           end t0).

Lemma SBCCH_SL_BCH_MessageType__c1__helper2 :  forall (y : SBCCH_SL_BCH_MessageType__c1__Type), SBCCH_SL_BCH_MessageType__c1__cond y -> choice_cond SBCCH_SL_BCH_MessageType__c1__list (SBCCH_SL_BCH_MessageType__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SBCCH_SL_BCH_MessageType__c1__helper3 :  forall (y : SBCCH_SL_BCH_MessageType__c1__Type), SBCCH_SL_BCH_MessageType__c1__F2 (SBCCH_SL_BCH_MessageType__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SBCCH_SL_BCH_MessageType__c1__helper4 : (forall b : choice SBCCH_SL_BCH_MessageType__c1__list, choice_cond SBCCH_SL_BCH_MessageType__c1__list b -> SBCCH_SL_BCH_MessageType__c1__cond (SBCCH_SL_BCH_MessageType__c1__F2 b) /\ SBCCH_SL_BCH_MessageType__c1__F1 (SBCCH_SL_BCH_MessageType__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SBCCH_SL_BCH_MessageType__c1__F1 SBCCH_SL_BCH_MessageType__c1__F2.
Definition SBCCH_SL_BCH_MessageType__c1__Format : T_Format SBCCH_SL_BCH_MessageType__c1__Type SBCCH_SL_BCH_MessageType__c1__cond :=
  (* Eval compute in *) proj2_format SBCCH_SL_BCH_MessageType__c1__cond SBCCH_SL_BCH_MessageType__c1__list__Format SBCCH_SL_BCH_MessageType__c1__F1 SBCCH_SL_BCH_MessageType__c1__F2 SBCCH_SL_BCH_MessageType__c1__helper2 SBCCH_SL_BCH_MessageType__c1__helper3 SBCCH_SL_BCH_MessageType__c1__helper4.
Opaque SBCCH_SL_BCH_MessageType__c1__cond SBCCH_SL_BCH_MessageType__c1__Format.

Definition SBCCH_SL_BCH_MessageType__messageClassExtension__helper : forall a : SBCCH_SL_BCH_MessageType__messageClassExtension__Type, True -> True /\ make__SBCCH_SL_BCH_MessageType__messageClassExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition SBCCH_SL_BCH_MessageType__messageClassExtension__Format : T_Format SBCCH_SL_BCH_MessageType__messageClassExtension__Type SBCCH_SL_BCH_MessageType__messageClassExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SBCCH_SL_BCH_MessageType__messageClassExtension__Type)
    SBCCH_SL_BCH_MessageType__messageClassExtension__helper unit_unique (fun _ => left I).

Opaque SBCCH_SL_BCH_MessageType__messageClassExtension__cond SBCCH_SL_BCH_MessageType__messageClassExtension__Format.


Definition SBCCH_SL_BCH_MessageType__Format_Type := Eval cbn in get_formats SBCCH_SL_BCH_MessageType__list.
Definition SBCCH_SL_BCH_MessageType__Format_list : SBCCH_SL_BCH_MessageType__Format_Type :=
  (SBCCH_SL_BCH_MessageType__c1__Format, (SBCCH_SL_BCH_MessageType__messageClassExtension__Format, unit__Format)).
Definition SBCCH_SL_BCH_MessageType__list__Format := Eval compute in choice_format SBCCH_SL_BCH_MessageType__list SBCCH_SL_BCH_MessageType__len_helper1 SBCCH_SL_BCH_MessageType__len_helper2  SBCCH_SL_BCH_MessageType__Format_list.
Definition SBCCH_SL_BCH_MessageType__F1 (z : SBCCH_SL_BCH_MessageType__Type) : (choice SBCCH_SL_BCH_MessageType__list) :=
  match z with
   | SBCCH_SL_BCH_MessageType__c1 t => existT _ 0 t
  | SBCCH_SL_BCH_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition SBCCH_SL_BCH_MessageType__g := (fun n => typ_set (get_nth_typ SBCCH_SL_BCH_MessageType__list n)).
Definition SBCCH_SL_BCH_MessageType__F2 (y : choice SBCCH_SL_BCH_MessageType__list) : SBCCH_SL_BCH_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SBCCH_SL_BCH_MessageType__g n -> SBCCH_SL_BCH_MessageType__Type) with
    | 0 => fun (t : SBCCH_SL_BCH_MessageType__c1__Type) => SBCCH_SL_BCH_MessageType__c1 t 
    | 1 => fun (t : SBCCH_SL_BCH_MessageType__messageClassExtension__Type) => SBCCH_SL_BCH_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SBCCH_SL_BCH_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SBCCH_SL_BCH_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SBCCH_SL_BCH_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SBCCH_SL_BCH_MessageType__Type with end) n0
           end t0).

Lemma SBCCH_SL_BCH_MessageType__helper2 :  forall (y : SBCCH_SL_BCH_MessageType__Type), SBCCH_SL_BCH_MessageType__cond y -> choice_cond SBCCH_SL_BCH_MessageType__list (SBCCH_SL_BCH_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SBCCH_SL_BCH_MessageType__helper3 :  forall (y : SBCCH_SL_BCH_MessageType__Type), SBCCH_SL_BCH_MessageType__F2 (SBCCH_SL_BCH_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SBCCH_SL_BCH_MessageType__helper4 : (forall b : choice SBCCH_SL_BCH_MessageType__list, choice_cond SBCCH_SL_BCH_MessageType__list b -> SBCCH_SL_BCH_MessageType__cond (SBCCH_SL_BCH_MessageType__F2 b) /\ SBCCH_SL_BCH_MessageType__F1 (SBCCH_SL_BCH_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SBCCH_SL_BCH_MessageType__F1 SBCCH_SL_BCH_MessageType__F2.
Definition SBCCH_SL_BCH_MessageType__Format : T_Format SBCCH_SL_BCH_MessageType__Type SBCCH_SL_BCH_MessageType__cond :=
  (* Eval compute in *) proj2_format SBCCH_SL_BCH_MessageType__cond SBCCH_SL_BCH_MessageType__list__Format SBCCH_SL_BCH_MessageType__F1 SBCCH_SL_BCH_MessageType__F2 SBCCH_SL_BCH_MessageType__helper2 SBCCH_SL_BCH_MessageType__helper3 SBCCH_SL_BCH_MessageType__helper4.
Opaque SBCCH_SL_BCH_MessageType__cond SBCCH_SL_BCH_MessageType__Format.

