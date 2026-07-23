Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PositionVelocity_r17.

Opaque PositionVelocity_r17__cond PositionVelocity_r17__Format.

Require Import NR.Orbital_r17.

Opaque Orbital_r17__cond Orbital_r17__Format.


Inductive EphemerisInfo_r17__Type : Set :=
  | EphemerisInfo_r17__positionVelocity_r17 : PositionVelocity_r17__Type -> EphemerisInfo_r17__Type
  | EphemerisInfo_r17__orbital_r17 : Orbital_r17__Type -> EphemerisInfo_r17__Type
.
Definition EphemerisInfo_r17__list : list typ := (
typ_cons PositionVelocity_r17__Type PositionVelocity_r17__cond ::
typ_cons Orbital_r17__Type Orbital_r17__cond ::
 nil).
Definition EphemerisInfo_r17__cond (c : EphemerisInfo_r17__Type) := 
  match c with
  | EphemerisInfo_r17__positionVelocity_r17 t => PositionVelocity_r17__cond t 
  | EphemerisInfo_r17__orbital_r17 t => Orbital_r17__cond t 
  end.

Lemma EphemerisInfo_r17__len_helper1 : to_bit_sz (length EphemerisInfo_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EphemerisInfo_r17__len_helper2 : 2 <= length2 EphemerisInfo_r17__list.
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

Definition EphemerisInfo_r17__Format_Type := Eval cbn in get_formats EphemerisInfo_r17__list.
Definition EphemerisInfo_r17__Format_list : EphemerisInfo_r17__Format_Type :=
  (PositionVelocity_r17__Format, (Orbital_r17__Format, unit__Format)).
Definition EphemerisInfo_r17__list__Format := Eval compute in choice_format EphemerisInfo_r17__list EphemerisInfo_r17__len_helper1 EphemerisInfo_r17__len_helper2  EphemerisInfo_r17__Format_list.
Definition EphemerisInfo_r17__F1 (z : EphemerisInfo_r17__Type) : (choice EphemerisInfo_r17__list) :=
  match z with
   | EphemerisInfo_r17__positionVelocity_r17 t => existT _ 0 t
  | EphemerisInfo_r17__orbital_r17 t => existT _ 1 t
  end.
Definition EphemerisInfo_r17__g := (fun n => typ_set (get_nth_typ EphemerisInfo_r17__list n)).
Definition EphemerisInfo_r17__F2 (y : choice EphemerisInfo_r17__list) : EphemerisInfo_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EphemerisInfo_r17__g n -> EphemerisInfo_r17__Type) with
    | 0 => fun (t : PositionVelocity_r17__Type) => EphemerisInfo_r17__positionVelocity_r17 t 
    | 1 => fun (t : Orbital_r17__Type) => EphemerisInfo_r17__orbital_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : EphemerisInfo_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ EphemerisInfo_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EphemerisInfo_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return EphemerisInfo_r17__Type with end) n0
           end t0).

Lemma EphemerisInfo_r17__helper2 :  forall (y : EphemerisInfo_r17__Type), EphemerisInfo_r17__cond y -> choice_cond EphemerisInfo_r17__list (EphemerisInfo_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EphemerisInfo_r17__helper3 :  forall (y : EphemerisInfo_r17__Type), EphemerisInfo_r17__F2 (EphemerisInfo_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EphemerisInfo_r17__helper4 : (forall b : choice EphemerisInfo_r17__list, choice_cond EphemerisInfo_r17__list b -> EphemerisInfo_r17__cond (EphemerisInfo_r17__F2 b) /\ EphemerisInfo_r17__F1 (EphemerisInfo_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EphemerisInfo_r17__F1 EphemerisInfo_r17__F2.
Definition EphemerisInfo_r17__Format : T_Format EphemerisInfo_r17__Type EphemerisInfo_r17__cond :=
  (* Eval compute in *) proj2_format EphemerisInfo_r17__cond EphemerisInfo_r17__list__Format EphemerisInfo_r17__F1 EphemerisInfo_r17__F2 EphemerisInfo_r17__helper2 EphemerisInfo_r17__helper3 EphemerisInfo_r17__helper4.
Opaque EphemerisInfo_r17__cond EphemerisInfo_r17__Format.

