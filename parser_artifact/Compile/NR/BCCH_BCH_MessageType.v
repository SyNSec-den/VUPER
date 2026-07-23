Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MIB.

Opaque MIB__cond MIB__Format.

Record BCCH_BCH_MessageType__messageClassExtension__Type : Set := make__BCCH_BCH_MessageType__messageClassExtension__Type {}.
Definition BCCH_BCH_MessageType__messageClassExtension__cond (z : BCCH_BCH_MessageType__messageClassExtension__Type) := True.

Inductive BCCH_BCH_MessageType__Type : Set :=
  | BCCH_BCH_MessageType__mib : MIB__Type -> BCCH_BCH_MessageType__Type
  | BCCH_BCH_MessageType__messageClassExtension : BCCH_BCH_MessageType__messageClassExtension__Type -> BCCH_BCH_MessageType__Type
.
Definition BCCH_BCH_MessageType__list : list typ := (
typ_cons MIB__Type MIB__cond ::
typ_cons BCCH_BCH_MessageType__messageClassExtension__Type BCCH_BCH_MessageType__messageClassExtension__cond ::
 nil).
Definition BCCH_BCH_MessageType__cond (c : BCCH_BCH_MessageType__Type) := 
  match c with
  | BCCH_BCH_MessageType__mib t => MIB__cond t 
  | BCCH_BCH_MessageType__messageClassExtension t => BCCH_BCH_MessageType__messageClassExtension__cond t 
  end.

Lemma BCCH_BCH_MessageType__len_helper1 : to_bit_sz (length BCCH_BCH_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BCCH_BCH_MessageType__len_helper2 : 2 <= length2 BCCH_BCH_MessageType__list.
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
Definition BCCH_BCH_MessageType__messageClassExtension__helper : forall a : BCCH_BCH_MessageType__messageClassExtension__Type, True -> True /\ make__BCCH_BCH_MessageType__messageClassExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition BCCH_BCH_MessageType__messageClassExtension__Format : T_Format BCCH_BCH_MessageType__messageClassExtension__Type BCCH_BCH_MessageType__messageClassExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__BCCH_BCH_MessageType__messageClassExtension__Type)
    BCCH_BCH_MessageType__messageClassExtension__helper unit_unique (fun _ => left I).

Opaque BCCH_BCH_MessageType__messageClassExtension__cond BCCH_BCH_MessageType__messageClassExtension__Format.


Definition BCCH_BCH_MessageType__Format_Type := Eval cbn in get_formats BCCH_BCH_MessageType__list.
Definition BCCH_BCH_MessageType__Format_list : BCCH_BCH_MessageType__Format_Type :=
  (MIB__Format, (BCCH_BCH_MessageType__messageClassExtension__Format, unit__Format)).
Definition BCCH_BCH_MessageType__list__Format := Eval compute in choice_format BCCH_BCH_MessageType__list BCCH_BCH_MessageType__len_helper1 BCCH_BCH_MessageType__len_helper2  BCCH_BCH_MessageType__Format_list.
Definition BCCH_BCH_MessageType__F1 (z : BCCH_BCH_MessageType__Type) : (choice BCCH_BCH_MessageType__list) :=
  match z with
   | BCCH_BCH_MessageType__mib t => existT _ 0 t
  | BCCH_BCH_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition BCCH_BCH_MessageType__g := (fun n => typ_set (get_nth_typ BCCH_BCH_MessageType__list n)).
Definition BCCH_BCH_MessageType__F2 (y : choice BCCH_BCH_MessageType__list) : BCCH_BCH_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BCCH_BCH_MessageType__g n -> BCCH_BCH_MessageType__Type) with
    | 0 => fun (t : MIB__Type) => BCCH_BCH_MessageType__mib t 
    | 1 => fun (t : BCCH_BCH_MessageType__messageClassExtension__Type) => BCCH_BCH_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BCCH_BCH_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BCCH_BCH_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BCCH_BCH_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BCCH_BCH_MessageType__Type with end) n0
           end t0).

Lemma BCCH_BCH_MessageType__helper2 :  forall (y : BCCH_BCH_MessageType__Type), BCCH_BCH_MessageType__cond y -> choice_cond BCCH_BCH_MessageType__list (BCCH_BCH_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BCCH_BCH_MessageType__helper3 :  forall (y : BCCH_BCH_MessageType__Type), BCCH_BCH_MessageType__F2 (BCCH_BCH_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BCCH_BCH_MessageType__helper4 : (forall b : choice BCCH_BCH_MessageType__list, choice_cond BCCH_BCH_MessageType__list b -> BCCH_BCH_MessageType__cond (BCCH_BCH_MessageType__F2 b) /\ BCCH_BCH_MessageType__F1 (BCCH_BCH_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BCCH_BCH_MessageType__F1 BCCH_BCH_MessageType__F2.
Definition BCCH_BCH_MessageType__Format : T_Format BCCH_BCH_MessageType__Type BCCH_BCH_MessageType__cond :=
  (* Eval compute in *) proj2_format BCCH_BCH_MessageType__cond BCCH_BCH_MessageType__list__Format BCCH_BCH_MessageType__F1 BCCH_BCH_MessageType__F2 BCCH_BCH_MessageType__helper2 BCCH_BCH_MessageType__helper3 BCCH_BCH_MessageType__helper4.
Opaque BCCH_BCH_MessageType__cond BCCH_BCH_MessageType__Format.

