Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRCResumeRequest1.

Opaque RRCResumeRequest1__cond RRCResumeRequest1__Format.


Inductive UL_CCCH1_MessageType__c1__Type : Set :=
  | UL_CCCH1_MessageType__c1__rrcResumeRequest1 : RRCResumeRequest1__Type -> UL_CCCH1_MessageType__c1__Type
  | UL_CCCH1_MessageType__c1__spare3 : unit -> UL_CCCH1_MessageType__c1__Type
  | UL_CCCH1_MessageType__c1__spare2 : unit -> UL_CCCH1_MessageType__c1__Type
  | UL_CCCH1_MessageType__c1__spare1 : unit -> UL_CCCH1_MessageType__c1__Type
.
Definition UL_CCCH1_MessageType__c1__list : list typ := (
typ_cons RRCResumeRequest1__Type RRCResumeRequest1__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition UL_CCCH1_MessageType__c1__cond (c : UL_CCCH1_MessageType__c1__Type) := 
  match c with
  | UL_CCCH1_MessageType__c1__rrcResumeRequest1 t => RRCResumeRequest1__cond t 
  | UL_CCCH1_MessageType__c1__spare3 t => (fun _ => True) t 
  | UL_CCCH1_MessageType__c1__spare2 t => (fun _ => True) t 
  | UL_CCCH1_MessageType__c1__spare1 t => (fun _ => True) t 
  end.

Lemma UL_CCCH1_MessageType__c1__len_helper1 : to_bit_sz (length UL_CCCH1_MessageType__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UL_CCCH1_MessageType__c1__len_helper2 : 2 <= length2 UL_CCCH1_MessageType__c1__list.
 simpl. lia. Qed.
Record UL_CCCH1_MessageType__messageClassExtension__Type : Set := make__UL_CCCH1_MessageType__messageClassExtension__Type {}.
Definition UL_CCCH1_MessageType__messageClassExtension__cond (z : UL_CCCH1_MessageType__messageClassExtension__Type) := True.

Inductive UL_CCCH1_MessageType__Type : Set :=
  | UL_CCCH1_MessageType__c1 : UL_CCCH1_MessageType__c1__Type -> UL_CCCH1_MessageType__Type
  | UL_CCCH1_MessageType__messageClassExtension : UL_CCCH1_MessageType__messageClassExtension__Type -> UL_CCCH1_MessageType__Type
.
Definition UL_CCCH1_MessageType__list : list typ := (
typ_cons UL_CCCH1_MessageType__c1__Type UL_CCCH1_MessageType__c1__cond ::
typ_cons UL_CCCH1_MessageType__messageClassExtension__Type UL_CCCH1_MessageType__messageClassExtension__cond ::
 nil).
Definition UL_CCCH1_MessageType__cond (c : UL_CCCH1_MessageType__Type) := 
  match c with
  | UL_CCCH1_MessageType__c1 t => UL_CCCH1_MessageType__c1__cond t 
  | UL_CCCH1_MessageType__messageClassExtension t => UL_CCCH1_MessageType__messageClassExtension__cond t 
  end.

Lemma UL_CCCH1_MessageType__len_helper1 : to_bit_sz (length UL_CCCH1_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UL_CCCH1_MessageType__len_helper2 : 2 <= length2 UL_CCCH1_MessageType__list.
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

Definition UL_CCCH1_MessageType__c1__Format_Type := Eval cbn in get_formats UL_CCCH1_MessageType__c1__list.
Definition UL_CCCH1_MessageType__c1__Format_list : UL_CCCH1_MessageType__c1__Format_Type :=
  (RRCResumeRequest1__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition UL_CCCH1_MessageType__c1__list__Format := Eval compute in choice_format UL_CCCH1_MessageType__c1__list UL_CCCH1_MessageType__c1__len_helper1 UL_CCCH1_MessageType__c1__len_helper2  UL_CCCH1_MessageType__c1__Format_list.
Definition UL_CCCH1_MessageType__c1__F1 (z : UL_CCCH1_MessageType__c1__Type) : (choice UL_CCCH1_MessageType__c1__list) :=
  match z with
   | UL_CCCH1_MessageType__c1__rrcResumeRequest1 t => existT _ 0 t
  | UL_CCCH1_MessageType__c1__spare3 t => existT _ 1 t
  | UL_CCCH1_MessageType__c1__spare2 t => existT _ 2 t
  | UL_CCCH1_MessageType__c1__spare1 t => existT _ 3 t
  end.
Definition UL_CCCH1_MessageType__c1__g := (fun n => typ_set (get_nth_typ UL_CCCH1_MessageType__c1__list n)).
Definition UL_CCCH1_MessageType__c1__F2 (y : choice UL_CCCH1_MessageType__c1__list) : UL_CCCH1_MessageType__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UL_CCCH1_MessageType__c1__g n -> UL_CCCH1_MessageType__c1__Type) with
    | 0 => fun (t : RRCResumeRequest1__Type) => UL_CCCH1_MessageType__c1__rrcResumeRequest1 t 
    | 1 => fun (t : unit) => UL_CCCH1_MessageType__c1__spare3 t 
    | 2 => fun (t : unit) => UL_CCCH1_MessageType__c1__spare2 t 
    | 3 => fun (t : unit) => UL_CCCH1_MessageType__c1__spare1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : UL_CCCH1_MessageType__c1__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ UL_CCCH1_MessageType__c1__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UL_CCCH1_MessageType__c1__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return UL_CCCH1_MessageType__c1__Type with end) n0
           end t0).

Lemma UL_CCCH1_MessageType__c1__helper2 :  forall (y : UL_CCCH1_MessageType__c1__Type), UL_CCCH1_MessageType__c1__cond y -> choice_cond UL_CCCH1_MessageType__c1__list (UL_CCCH1_MessageType__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UL_CCCH1_MessageType__c1__helper3 :  forall (y : UL_CCCH1_MessageType__c1__Type), UL_CCCH1_MessageType__c1__F2 (UL_CCCH1_MessageType__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UL_CCCH1_MessageType__c1__helper4 : (forall b : choice UL_CCCH1_MessageType__c1__list, choice_cond UL_CCCH1_MessageType__c1__list b -> UL_CCCH1_MessageType__c1__cond (UL_CCCH1_MessageType__c1__F2 b) /\ UL_CCCH1_MessageType__c1__F1 (UL_CCCH1_MessageType__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UL_CCCH1_MessageType__c1__F1 UL_CCCH1_MessageType__c1__F2.
Definition UL_CCCH1_MessageType__c1__Format : T_Format UL_CCCH1_MessageType__c1__Type UL_CCCH1_MessageType__c1__cond :=
  (* Eval compute in *) proj2_format UL_CCCH1_MessageType__c1__cond UL_CCCH1_MessageType__c1__list__Format UL_CCCH1_MessageType__c1__F1 UL_CCCH1_MessageType__c1__F2 UL_CCCH1_MessageType__c1__helper2 UL_CCCH1_MessageType__c1__helper3 UL_CCCH1_MessageType__c1__helper4.
Opaque UL_CCCH1_MessageType__c1__cond UL_CCCH1_MessageType__c1__Format.

Definition UL_CCCH1_MessageType__messageClassExtension__helper : forall a : UL_CCCH1_MessageType__messageClassExtension__Type, True -> True /\ make__UL_CCCH1_MessageType__messageClassExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UL_CCCH1_MessageType__messageClassExtension__Format : T_Format UL_CCCH1_MessageType__messageClassExtension__Type UL_CCCH1_MessageType__messageClassExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UL_CCCH1_MessageType__messageClassExtension__Type)
    UL_CCCH1_MessageType__messageClassExtension__helper unit_unique (fun _ => left I).

Opaque UL_CCCH1_MessageType__messageClassExtension__cond UL_CCCH1_MessageType__messageClassExtension__Format.


Definition UL_CCCH1_MessageType__Format_Type := Eval cbn in get_formats UL_CCCH1_MessageType__list.
Definition UL_CCCH1_MessageType__Format_list : UL_CCCH1_MessageType__Format_Type :=
  (UL_CCCH1_MessageType__c1__Format, (UL_CCCH1_MessageType__messageClassExtension__Format, unit__Format)).
Definition UL_CCCH1_MessageType__list__Format := Eval compute in choice_format UL_CCCH1_MessageType__list UL_CCCH1_MessageType__len_helper1 UL_CCCH1_MessageType__len_helper2  UL_CCCH1_MessageType__Format_list.
Definition UL_CCCH1_MessageType__F1 (z : UL_CCCH1_MessageType__Type) : (choice UL_CCCH1_MessageType__list) :=
  match z with
   | UL_CCCH1_MessageType__c1 t => existT _ 0 t
  | UL_CCCH1_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition UL_CCCH1_MessageType__g := (fun n => typ_set (get_nth_typ UL_CCCH1_MessageType__list n)).
Definition UL_CCCH1_MessageType__F2 (y : choice UL_CCCH1_MessageType__list) : UL_CCCH1_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UL_CCCH1_MessageType__g n -> UL_CCCH1_MessageType__Type) with
    | 0 => fun (t : UL_CCCH1_MessageType__c1__Type) => UL_CCCH1_MessageType__c1 t 
    | 1 => fun (t : UL_CCCH1_MessageType__messageClassExtension__Type) => UL_CCCH1_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UL_CCCH1_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UL_CCCH1_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UL_CCCH1_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UL_CCCH1_MessageType__Type with end) n0
           end t0).

Lemma UL_CCCH1_MessageType__helper2 :  forall (y : UL_CCCH1_MessageType__Type), UL_CCCH1_MessageType__cond y -> choice_cond UL_CCCH1_MessageType__list (UL_CCCH1_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UL_CCCH1_MessageType__helper3 :  forall (y : UL_CCCH1_MessageType__Type), UL_CCCH1_MessageType__F2 (UL_CCCH1_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UL_CCCH1_MessageType__helper4 : (forall b : choice UL_CCCH1_MessageType__list, choice_cond UL_CCCH1_MessageType__list b -> UL_CCCH1_MessageType__cond (UL_CCCH1_MessageType__F2 b) /\ UL_CCCH1_MessageType__F1 (UL_CCCH1_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UL_CCCH1_MessageType__F1 UL_CCCH1_MessageType__F2.
Definition UL_CCCH1_MessageType__Format : T_Format UL_CCCH1_MessageType__Type UL_CCCH1_MessageType__cond :=
  (* Eval compute in *) proj2_format UL_CCCH1_MessageType__cond UL_CCCH1_MessageType__list__Format UL_CCCH1_MessageType__F1 UL_CCCH1_MessageType__F2 UL_CCCH1_MessageType__helper2 UL_CCCH1_MessageType__helper3 UL_CCCH1_MessageType__helper4.
Opaque UL_CCCH1_MessageType__cond UL_CCCH1_MessageType__Format.

