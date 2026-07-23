Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BFR_SSB_Resource.

Opaque BFR_SSB_Resource__cond BFR_SSB_Resource__Format.

Require Import NR.BFR_CSIRS_Resource.

Opaque BFR_CSIRS_Resource__cond BFR_CSIRS_Resource__Format.


Inductive PRACH_ResourceDedicatedBFR__Type : Set :=
  | PRACH_ResourceDedicatedBFR__ssb : BFR_SSB_Resource__Type -> PRACH_ResourceDedicatedBFR__Type
  | PRACH_ResourceDedicatedBFR__csi_RS : BFR_CSIRS_Resource__Type -> PRACH_ResourceDedicatedBFR__Type
.
Definition PRACH_ResourceDedicatedBFR__list : list typ := (
typ_cons BFR_SSB_Resource__Type BFR_SSB_Resource__cond ::
typ_cons BFR_CSIRS_Resource__Type BFR_CSIRS_Resource__cond ::
 nil).
Definition PRACH_ResourceDedicatedBFR__cond (c : PRACH_ResourceDedicatedBFR__Type) := 
  match c with
  | PRACH_ResourceDedicatedBFR__ssb t => BFR_SSB_Resource__cond t 
  | PRACH_ResourceDedicatedBFR__csi_RS t => BFR_CSIRS_Resource__cond t 
  end.

Lemma PRACH_ResourceDedicatedBFR__len_helper1 : to_bit_sz (length PRACH_ResourceDedicatedBFR__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PRACH_ResourceDedicatedBFR__len_helper2 : 2 <= length2 PRACH_ResourceDedicatedBFR__list.
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

Definition PRACH_ResourceDedicatedBFR__Format_Type := Eval cbn in get_formats PRACH_ResourceDedicatedBFR__list.
Definition PRACH_ResourceDedicatedBFR__Format_list : PRACH_ResourceDedicatedBFR__Format_Type :=
  (BFR_SSB_Resource__Format, (BFR_CSIRS_Resource__Format, unit__Format)).
Definition PRACH_ResourceDedicatedBFR__list__Format := Eval compute in choice_format PRACH_ResourceDedicatedBFR__list PRACH_ResourceDedicatedBFR__len_helper1 PRACH_ResourceDedicatedBFR__len_helper2  PRACH_ResourceDedicatedBFR__Format_list.
Definition PRACH_ResourceDedicatedBFR__F1 (z : PRACH_ResourceDedicatedBFR__Type) : (choice PRACH_ResourceDedicatedBFR__list) :=
  match z with
   | PRACH_ResourceDedicatedBFR__ssb t => existT _ 0 t
  | PRACH_ResourceDedicatedBFR__csi_RS t => existT _ 1 t
  end.
Definition PRACH_ResourceDedicatedBFR__g := (fun n => typ_set (get_nth_typ PRACH_ResourceDedicatedBFR__list n)).
Definition PRACH_ResourceDedicatedBFR__F2 (y : choice PRACH_ResourceDedicatedBFR__list) : PRACH_ResourceDedicatedBFR__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PRACH_ResourceDedicatedBFR__g n -> PRACH_ResourceDedicatedBFR__Type) with
    | 0 => fun (t : BFR_SSB_Resource__Type) => PRACH_ResourceDedicatedBFR__ssb t 
    | 1 => fun (t : BFR_CSIRS_Resource__Type) => PRACH_ResourceDedicatedBFR__csi_RS t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PRACH_ResourceDedicatedBFR__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PRACH_ResourceDedicatedBFR__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PRACH_ResourceDedicatedBFR__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PRACH_ResourceDedicatedBFR__Type with end) n0
           end t0).

Lemma PRACH_ResourceDedicatedBFR__helper2 :  forall (y : PRACH_ResourceDedicatedBFR__Type), PRACH_ResourceDedicatedBFR__cond y -> choice_cond PRACH_ResourceDedicatedBFR__list (PRACH_ResourceDedicatedBFR__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PRACH_ResourceDedicatedBFR__helper3 :  forall (y : PRACH_ResourceDedicatedBFR__Type), PRACH_ResourceDedicatedBFR__F2 (PRACH_ResourceDedicatedBFR__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PRACH_ResourceDedicatedBFR__helper4 : (forall b : choice PRACH_ResourceDedicatedBFR__list, choice_cond PRACH_ResourceDedicatedBFR__list b -> PRACH_ResourceDedicatedBFR__cond (PRACH_ResourceDedicatedBFR__F2 b) /\ PRACH_ResourceDedicatedBFR__F1 (PRACH_ResourceDedicatedBFR__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PRACH_ResourceDedicatedBFR__F1 PRACH_ResourceDedicatedBFR__F2.
Definition PRACH_ResourceDedicatedBFR__Format : T_Format PRACH_ResourceDedicatedBFR__Type PRACH_ResourceDedicatedBFR__cond :=
  (* Eval compute in *) proj2_format PRACH_ResourceDedicatedBFR__cond PRACH_ResourceDedicatedBFR__list__Format PRACH_ResourceDedicatedBFR__F1 PRACH_ResourceDedicatedBFR__F2 PRACH_ResourceDedicatedBFR__helper2 PRACH_ResourceDedicatedBFR__helper3 PRACH_ResourceDedicatedBFR__helper4.
Opaque PRACH_ResourceDedicatedBFR__cond PRACH_ResourceDedicatedBFR__Format.

