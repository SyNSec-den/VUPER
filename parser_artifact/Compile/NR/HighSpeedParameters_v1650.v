Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type : Set :=
 | HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__supported
.
Definition HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__cond := (fun (_ : HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type) => True).
Lemma HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__nat__helper.

Definition HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1 t :=
  match t with
  | HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__supported => 0
  end.
Definition HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F2 n :=
  match n with
  | 0 => HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__supported
  | _ => HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__supported
  end.
Lemma HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1F2 : forall x : HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type, (HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1 x <= 0) /\ HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F2 (HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F2F1 : forall (y : nat) (H : y <= 0), HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1 (HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F2 y) = y. enum_solve H y. Qed.

Inductive HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type : Set :=
 | HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__supported
.
Definition HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__cond := (fun (_ : HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type) => True).
Lemma HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__nat__helper.

Definition HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1 t :=
  match t with
  | HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__supported => 0
  end.
Definition HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F2 n :=
  match n with
  | 0 => HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__supported
  | _ => HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__supported
  end.
Lemma HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1F2 : forall x : HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type, (HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1 x <= 0) /\ HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F2 (HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F2F1 : forall (y : nat) (H : y <= 0), HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1 (HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F2 y) = y. enum_solve H y. Qed.


Inductive HighSpeedParameters_v1650__Type : Set :=
  | HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16 : HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type -> HighSpeedParameters_v1650__Type
  | HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16 : HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type -> HighSpeedParameters_v1650__Type
.
Definition HighSpeedParameters_v1650__list : list typ := (
typ_cons HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__cond ::
typ_cons HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__cond ::
 nil).
Definition HighSpeedParameters_v1650__cond (c : HighSpeedParameters_v1650__Type) := 
  match c with
  | HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16 t => HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__cond t 
  | HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16 t => HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__cond t 
  end.

Lemma HighSpeedParameters_v1650__len_helper1 : to_bit_sz (length HighSpeedParameters_v1650__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma HighSpeedParameters_v1650__len_helper2 : 2 <= length2 HighSpeedParameters_v1650__list.
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
Definition HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Format : T_Format HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__nat__Format HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1 HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F2 HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F1F2 HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__F2F1.

Opaque HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__cond HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Format.

Definition HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Format : T_Format HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__nat__Format HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1 HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F2 HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F1F2 HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__F2F1.

Opaque HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__cond HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Format.


Definition HighSpeedParameters_v1650__Format_Type := Eval cbn in get_formats HighSpeedParameters_v1650__list.
Definition HighSpeedParameters_v1650__Format_list : HighSpeedParameters_v1650__Format_Type :=
  (HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Format, (HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Format, unit__Format)).
Definition HighSpeedParameters_v1650__list__Format := Eval compute in choice_format HighSpeedParameters_v1650__list HighSpeedParameters_v1650__len_helper1 HighSpeedParameters_v1650__len_helper2  HighSpeedParameters_v1650__Format_list.
Definition HighSpeedParameters_v1650__F1 (z : HighSpeedParameters_v1650__Type) : (choice HighSpeedParameters_v1650__list) :=
  match z with
   | HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16 t => existT _ 0 t
  | HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16 t => existT _ 1 t
  end.
Definition HighSpeedParameters_v1650__g := (fun n => typ_set (get_nth_typ HighSpeedParameters_v1650__list n)).
Definition HighSpeedParameters_v1650__F2 (y : choice HighSpeedParameters_v1650__list) : HighSpeedParameters_v1650__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (HighSpeedParameters_v1650__g n -> HighSpeedParameters_v1650__Type) with
    | 0 => fun (t : HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16__Type) => HighSpeedParameters_v1650__intraNR_MeasurementEnhancement_r16 t 
    | 1 => fun (t : HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16__Type) => HighSpeedParameters_v1650__interRAT_MeasurementEnhancement_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : HighSpeedParameters_v1650__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ HighSpeedParameters_v1650__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len HighSpeedParameters_v1650__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return HighSpeedParameters_v1650__Type with end) n0
           end t0).

Lemma HighSpeedParameters_v1650__helper2 :  forall (y : HighSpeedParameters_v1650__Type), HighSpeedParameters_v1650__cond y -> choice_cond HighSpeedParameters_v1650__list (HighSpeedParameters_v1650__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma HighSpeedParameters_v1650__helper3 :  forall (y : HighSpeedParameters_v1650__Type), HighSpeedParameters_v1650__F2 (HighSpeedParameters_v1650__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma HighSpeedParameters_v1650__helper4 : (forall b : choice HighSpeedParameters_v1650__list, choice_cond HighSpeedParameters_v1650__list b -> HighSpeedParameters_v1650__cond (HighSpeedParameters_v1650__F2 b) /\ HighSpeedParameters_v1650__F1 (HighSpeedParameters_v1650__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length HighSpeedParameters_v1650__F1 HighSpeedParameters_v1650__F2.
Definition HighSpeedParameters_v1650__Format : T_Format HighSpeedParameters_v1650__Type HighSpeedParameters_v1650__cond :=
  (* Eval compute in *) proj2_format HighSpeedParameters_v1650__cond HighSpeedParameters_v1650__list__Format HighSpeedParameters_v1650__F1 HighSpeedParameters_v1650__F2 HighSpeedParameters_v1650__helper2 HighSpeedParameters_v1650__helper3 HighSpeedParameters_v1650__helper4.
Opaque HighSpeedParameters_v1650__cond HighSpeedParameters_v1650__Format.

