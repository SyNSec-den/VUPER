Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandInformationEUTRA.

Opaque FreqBandInformationEUTRA__cond FreqBandInformationEUTRA__Format.

Require Import NR.FreqBandInformationNR.

Opaque FreqBandInformationNR__cond FreqBandInformationNR__Format.


Inductive FreqBandInformation__Type : Set :=
  | FreqBandInformation__bandInformationEUTRA : FreqBandInformationEUTRA__Type -> FreqBandInformation__Type
  | FreqBandInformation__bandInformationNR : FreqBandInformationNR__Type -> FreqBandInformation__Type
.
Definition FreqBandInformation__list : list typ := (
typ_cons FreqBandInformationEUTRA__Type FreqBandInformationEUTRA__cond ::
typ_cons FreqBandInformationNR__Type FreqBandInformationNR__cond ::
 nil).
Definition FreqBandInformation__cond (c : FreqBandInformation__Type) := 
  match c with
  | FreqBandInformation__bandInformationEUTRA t => FreqBandInformationEUTRA__cond t 
  | FreqBandInformation__bandInformationNR t => FreqBandInformationNR__cond t 
  end.

Lemma FreqBandInformation__len_helper1 : to_bit_sz (length FreqBandInformation__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma FreqBandInformation__len_helper2 : 2 <= length2 FreqBandInformation__list.
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

Definition FreqBandInformation__Format_Type := Eval cbn in get_formats FreqBandInformation__list.
Definition FreqBandInformation__Format_list : FreqBandInformation__Format_Type :=
  (FreqBandInformationEUTRA__Format, (FreqBandInformationNR__Format, unit__Format)).
Definition FreqBandInformation__list__Format := Eval compute in choice_format FreqBandInformation__list FreqBandInformation__len_helper1 FreqBandInformation__len_helper2  FreqBandInformation__Format_list.
Definition FreqBandInformation__F1 (z : FreqBandInformation__Type) : (choice FreqBandInformation__list) :=
  match z with
   | FreqBandInformation__bandInformationEUTRA t => existT _ 0 t
  | FreqBandInformation__bandInformationNR t => existT _ 1 t
  end.
Definition FreqBandInformation__g := (fun n => typ_set (get_nth_typ FreqBandInformation__list n)).
Definition FreqBandInformation__F2 (y : choice FreqBandInformation__list) : FreqBandInformation__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (FreqBandInformation__g n -> FreqBandInformation__Type) with
    | 0 => fun (t : FreqBandInformationEUTRA__Type) => FreqBandInformation__bandInformationEUTRA t 
    | 1 => fun (t : FreqBandInformationNR__Type) => FreqBandInformation__bandInformationNR t 
 | (S (S n0)) => (fun (x' : nat) (t'' : FreqBandInformation__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ FreqBandInformation__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len FreqBandInformation__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return FreqBandInformation__Type with end) n0
           end t0).

Lemma FreqBandInformation__helper2 :  forall (y : FreqBandInformation__Type), FreqBandInformation__cond y -> choice_cond FreqBandInformation__list (FreqBandInformation__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma FreqBandInformation__helper3 :  forall (y : FreqBandInformation__Type), FreqBandInformation__F2 (FreqBandInformation__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma FreqBandInformation__helper4 : (forall b : choice FreqBandInformation__list, choice_cond FreqBandInformation__list b -> FreqBandInformation__cond (FreqBandInformation__F2 b) /\ FreqBandInformation__F1 (FreqBandInformation__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length FreqBandInformation__F1 FreqBandInformation__F2.
Definition FreqBandInformation__Format : T_Format FreqBandInformation__Type FreqBandInformation__cond :=
  (* Eval compute in *) proj2_format FreqBandInformation__cond FreqBandInformation__list__Format FreqBandInformation__F1 FreqBandInformation__F2 FreqBandInformation__helper2 FreqBandInformation__helper3 FreqBandInformation__helper4.
Opaque FreqBandInformation__cond FreqBandInformation__Format.

