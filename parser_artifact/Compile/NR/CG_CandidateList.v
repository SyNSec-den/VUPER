Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.CG_CandidateList_r17_IEs.

Opaque CG_CandidateList_r17_IEs__cond CG_CandidateList_r17_IEs__Format.


Inductive CG_CandidateList__criticalExtensions__c1__Type : Set :=
  | CG_CandidateList__criticalExtensions__c1__cg_CandidateList_r17 : CG_CandidateList_r17_IEs__Type -> CG_CandidateList__criticalExtensions__c1__Type
  | CG_CandidateList__criticalExtensions__c1__spare3 : unit -> CG_CandidateList__criticalExtensions__c1__Type
  | CG_CandidateList__criticalExtensions__c1__spare2 : unit -> CG_CandidateList__criticalExtensions__c1__Type
  | CG_CandidateList__criticalExtensions__c1__spare1 : unit -> CG_CandidateList__criticalExtensions__c1__Type
.
Definition CG_CandidateList__criticalExtensions__c1__list : list typ := (
typ_cons CG_CandidateList_r17_IEs__Type CG_CandidateList_r17_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition CG_CandidateList__criticalExtensions__c1__cond (c : CG_CandidateList__criticalExtensions__c1__Type) := 
  match c with
  | CG_CandidateList__criticalExtensions__c1__cg_CandidateList_r17 t => CG_CandidateList_r17_IEs__cond t 
  | CG_CandidateList__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | CG_CandidateList__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | CG_CandidateList__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma CG_CandidateList__criticalExtensions__c1__len_helper1 : to_bit_sz (length CG_CandidateList__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CG_CandidateList__criticalExtensions__c1__len_helper2 : 2 <= length2 CG_CandidateList__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type : Set := make__CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition CG_CandidateList__criticalExtensions__criticalExtensionsFuture__cond (z : CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive CG_CandidateList__criticalExtensions__Type : Set :=
  | CG_CandidateList__criticalExtensions__c1 : CG_CandidateList__criticalExtensions__c1__Type -> CG_CandidateList__criticalExtensions__Type
  | CG_CandidateList__criticalExtensions__criticalExtensionsFuture : CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type -> CG_CandidateList__criticalExtensions__Type
.
Definition CG_CandidateList__criticalExtensions__list : list typ := (
typ_cons CG_CandidateList__criticalExtensions__c1__Type CG_CandidateList__criticalExtensions__c1__cond ::
typ_cons CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type CG_CandidateList__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition CG_CandidateList__criticalExtensions__cond (c : CG_CandidateList__criticalExtensions__Type) := 
  match c with
  | CG_CandidateList__criticalExtensions__c1 t => CG_CandidateList__criticalExtensions__c1__cond t 
  | CG_CandidateList__criticalExtensions__criticalExtensionsFuture t => CG_CandidateList__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma CG_CandidateList__criticalExtensions__len_helper1 : to_bit_sz (length CG_CandidateList__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CG_CandidateList__criticalExtensions__len_helper2 : 2 <= length2 CG_CandidateList__criticalExtensions__list.
 simpl. lia. Qed.
Record CG_CandidateList__Type : Set :=
  make__CG_CandidateList__Type {
    CG_CandidateList__criticalExtensions : CG_CandidateList__criticalExtensions__Type ;
}.
Definition CG_CandidateList__list := (
 Nor CG_CandidateList__criticalExtensions__Type CG_CandidateList__criticalExtensions__cond ::
 nil).
Definition CG_CandidateList__cond z := 
  CG_CandidateList__criticalExtensions__cond (CG_CandidateList__criticalExtensions z) /\
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

Definition CG_CandidateList__criticalExtensions__c1__Format_Type := Eval cbn in get_formats CG_CandidateList__criticalExtensions__c1__list.
Definition CG_CandidateList__criticalExtensions__c1__Format_list : CG_CandidateList__criticalExtensions__c1__Format_Type :=
  (CG_CandidateList_r17_IEs__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition CG_CandidateList__criticalExtensions__c1__list__Format := Eval compute in choice_format CG_CandidateList__criticalExtensions__c1__list CG_CandidateList__criticalExtensions__c1__len_helper1 CG_CandidateList__criticalExtensions__c1__len_helper2  CG_CandidateList__criticalExtensions__c1__Format_list.
Definition CG_CandidateList__criticalExtensions__c1__F1 (z : CG_CandidateList__criticalExtensions__c1__Type) : (choice CG_CandidateList__criticalExtensions__c1__list) :=
  match z with
   | CG_CandidateList__criticalExtensions__c1__cg_CandidateList_r17 t => existT _ 0 t
  | CG_CandidateList__criticalExtensions__c1__spare3 t => existT _ 1 t
  | CG_CandidateList__criticalExtensions__c1__spare2 t => existT _ 2 t
  | CG_CandidateList__criticalExtensions__c1__spare1 t => existT _ 3 t
  end.
Definition CG_CandidateList__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ CG_CandidateList__criticalExtensions__c1__list n)).
Definition CG_CandidateList__criticalExtensions__c1__F2 (y : choice CG_CandidateList__criticalExtensions__c1__list) : CG_CandidateList__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CG_CandidateList__criticalExtensions__c1__g n -> CG_CandidateList__criticalExtensions__c1__Type) with
    | 0 => fun (t : CG_CandidateList_r17_IEs__Type) => CG_CandidateList__criticalExtensions__c1__cg_CandidateList_r17 t 
    | 1 => fun (t : unit) => CG_CandidateList__criticalExtensions__c1__spare3 t 
    | 2 => fun (t : unit) => CG_CandidateList__criticalExtensions__c1__spare2 t 
    | 3 => fun (t : unit) => CG_CandidateList__criticalExtensions__c1__spare1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : CG_CandidateList__criticalExtensions__c1__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ CG_CandidateList__criticalExtensions__c1__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CG_CandidateList__criticalExtensions__c1__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return CG_CandidateList__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma CG_CandidateList__criticalExtensions__c1__helper2 :  forall (y : CG_CandidateList__criticalExtensions__c1__Type), CG_CandidateList__criticalExtensions__c1__cond y -> choice_cond CG_CandidateList__criticalExtensions__c1__list (CG_CandidateList__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CG_CandidateList__criticalExtensions__c1__helper3 :  forall (y : CG_CandidateList__criticalExtensions__c1__Type), CG_CandidateList__criticalExtensions__c1__F2 (CG_CandidateList__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CG_CandidateList__criticalExtensions__c1__helper4 : (forall b : choice CG_CandidateList__criticalExtensions__c1__list, choice_cond CG_CandidateList__criticalExtensions__c1__list b -> CG_CandidateList__criticalExtensions__c1__cond (CG_CandidateList__criticalExtensions__c1__F2 b) /\ CG_CandidateList__criticalExtensions__c1__F1 (CG_CandidateList__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CG_CandidateList__criticalExtensions__c1__F1 CG_CandidateList__criticalExtensions__c1__F2.
Definition CG_CandidateList__criticalExtensions__c1__Format : T_Format CG_CandidateList__criticalExtensions__c1__Type CG_CandidateList__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format CG_CandidateList__criticalExtensions__c1__cond CG_CandidateList__criticalExtensions__c1__list__Format CG_CandidateList__criticalExtensions__c1__F1 CG_CandidateList__criticalExtensions__c1__F2 CG_CandidateList__criticalExtensions__c1__helper2 CG_CandidateList__criticalExtensions__c1__helper3 CG_CandidateList__criticalExtensions__c1__helper4.
Opaque CG_CandidateList__criticalExtensions__c1__cond CG_CandidateList__criticalExtensions__c1__Format.

Definition CG_CandidateList__criticalExtensions__criticalExtensionsFuture__helper : forall a : CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Format : T_Format CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type CG_CandidateList__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type)
    CG_CandidateList__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque CG_CandidateList__criticalExtensions__criticalExtensionsFuture__cond CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Format.


Definition CG_CandidateList__criticalExtensions__Format_Type := Eval cbn in get_formats CG_CandidateList__criticalExtensions__list.
Definition CG_CandidateList__criticalExtensions__Format_list : CG_CandidateList__criticalExtensions__Format_Type :=
  (CG_CandidateList__criticalExtensions__c1__Format, (CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition CG_CandidateList__criticalExtensions__list__Format := Eval compute in choice_format CG_CandidateList__criticalExtensions__list CG_CandidateList__criticalExtensions__len_helper1 CG_CandidateList__criticalExtensions__len_helper2  CG_CandidateList__criticalExtensions__Format_list.
Definition CG_CandidateList__criticalExtensions__F1 (z : CG_CandidateList__criticalExtensions__Type) : (choice CG_CandidateList__criticalExtensions__list) :=
  match z with
   | CG_CandidateList__criticalExtensions__c1 t => existT _ 0 t
  | CG_CandidateList__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition CG_CandidateList__criticalExtensions__g := (fun n => typ_set (get_nth_typ CG_CandidateList__criticalExtensions__list n)).
Definition CG_CandidateList__criticalExtensions__F2 (y : choice CG_CandidateList__criticalExtensions__list) : CG_CandidateList__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CG_CandidateList__criticalExtensions__g n -> CG_CandidateList__criticalExtensions__Type) with
    | 0 => fun (t : CG_CandidateList__criticalExtensions__c1__Type) => CG_CandidateList__criticalExtensions__c1 t 
    | 1 => fun (t : CG_CandidateList__criticalExtensions__criticalExtensionsFuture__Type) => CG_CandidateList__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CG_CandidateList__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CG_CandidateList__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CG_CandidateList__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CG_CandidateList__criticalExtensions__Type with end) n0
           end t0).

Lemma CG_CandidateList__criticalExtensions__helper2 :  forall (y : CG_CandidateList__criticalExtensions__Type), CG_CandidateList__criticalExtensions__cond y -> choice_cond CG_CandidateList__criticalExtensions__list (CG_CandidateList__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CG_CandidateList__criticalExtensions__helper3 :  forall (y : CG_CandidateList__criticalExtensions__Type), CG_CandidateList__criticalExtensions__F2 (CG_CandidateList__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CG_CandidateList__criticalExtensions__helper4 : (forall b : choice CG_CandidateList__criticalExtensions__list, choice_cond CG_CandidateList__criticalExtensions__list b -> CG_CandidateList__criticalExtensions__cond (CG_CandidateList__criticalExtensions__F2 b) /\ CG_CandidateList__criticalExtensions__F1 (CG_CandidateList__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CG_CandidateList__criticalExtensions__F1 CG_CandidateList__criticalExtensions__F2.
Definition CG_CandidateList__criticalExtensions__Format : T_Format CG_CandidateList__criticalExtensions__Type CG_CandidateList__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format CG_CandidateList__criticalExtensions__cond CG_CandidateList__criticalExtensions__list__Format CG_CandidateList__criticalExtensions__F1 CG_CandidateList__criticalExtensions__F2 CG_CandidateList__criticalExtensions__helper2 CG_CandidateList__criticalExtensions__helper3 CG_CandidateList__criticalExtensions__helper4.
Opaque CG_CandidateList__criticalExtensions__cond CG_CandidateList__criticalExtensions__Format.


Definition CG_CandidateList__Format_Type := Eval cbn in seq_format_prod CG_CandidateList__list.
Definition CG_CandidateList__Format_list : CG_CandidateList__Format_Type :=
  (CG_CandidateList__criticalExtensions__Format, unit_format).
Definition CG_CandidateList__list__Format := (*Eval compute in *) seq_format CG_CandidateList__list CG_CandidateList__Format_list.
Definition CG_CandidateList__F1 z :=
  (CG_CandidateList__criticalExtensions z, tt).
Definition CG_CandidateList__F2 (y : seq_type CG_CandidateList__list) :=
  match y with
  | (i0, _)=>
    make__CG_CandidateList__Type i0
  end.
Lemma CG_CandidateList__F1F2_cond (z : CG_CandidateList__Type)
  : CG_CandidateList__cond z ->
  (seq_cond CG_CandidateList__list (CG_CandidateList__F1 z)).
intro H. unfold CG_CandidateList__cond in H. simpl. auto. Qed.
Lemma CG_CandidateList__F1F2_cond2 (z : CG_CandidateList__Type)
 : CG_CandidateList__F2 (CG_CandidateList__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_CandidateList__F2F1_cond (y : seq_type CG_CandidateList__list)
  : seq_cond CG_CandidateList__list y ->
 (CG_CandidateList__cond (CG_CandidateList__F2 y)) /\  CG_CandidateList__F1 (CG_CandidateList__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_CandidateList__cond. simpl in *. auto.
 - simpl. unfold CG_CandidateList__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_CandidateList__Format : T_Format CG_CandidateList__Type CG_CandidateList__cond :=
        proj2_format  CG_CandidateList__cond CG_CandidateList__list__Format
    CG_CandidateList__F1 CG_CandidateList__F2 CG_CandidateList__F1F2_cond  CG_CandidateList__F1F2_cond2 CG_CandidateList__F2F1_cond.
Opaque CG_CandidateList__cond CG_CandidateList__Format.

