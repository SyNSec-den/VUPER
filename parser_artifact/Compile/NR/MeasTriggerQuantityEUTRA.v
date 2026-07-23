Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_RangeEUTRA.

Opaque RSRP_RangeEUTRA__cond RSRP_RangeEUTRA__Format.

Require Import NR.RSRQ_RangeEUTRA.

Opaque RSRQ_RangeEUTRA__cond RSRQ_RangeEUTRA__Format.

Require Import NR.SINR_RangeEUTRA.

Opaque SINR_RangeEUTRA__cond SINR_RangeEUTRA__Format.


Inductive MeasTriggerQuantityEUTRA__Type : Set :=
  | MeasTriggerQuantityEUTRA__rsrp : RSRP_RangeEUTRA__Type -> MeasTriggerQuantityEUTRA__Type
  | MeasTriggerQuantityEUTRA__rsrq : RSRQ_RangeEUTRA__Type -> MeasTriggerQuantityEUTRA__Type
  | MeasTriggerQuantityEUTRA__sinr : SINR_RangeEUTRA__Type -> MeasTriggerQuantityEUTRA__Type
.
Definition MeasTriggerQuantityEUTRA__list : list typ := (
typ_cons RSRP_RangeEUTRA__Type RSRP_RangeEUTRA__cond ::
typ_cons RSRQ_RangeEUTRA__Type RSRQ_RangeEUTRA__cond ::
typ_cons SINR_RangeEUTRA__Type SINR_RangeEUTRA__cond ::
 nil).
Definition MeasTriggerQuantityEUTRA__cond (c : MeasTriggerQuantityEUTRA__Type) := 
  match c with
  | MeasTriggerQuantityEUTRA__rsrp t => RSRP_RangeEUTRA__cond t 
  | MeasTriggerQuantityEUTRA__rsrq t => RSRQ_RangeEUTRA__cond t 
  | MeasTriggerQuantityEUTRA__sinr t => SINR_RangeEUTRA__cond t 
  end.

Lemma MeasTriggerQuantityEUTRA__len_helper1 : to_bit_sz (length MeasTriggerQuantityEUTRA__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasTriggerQuantityEUTRA__len_helper2 : 2 <= length2 MeasTriggerQuantityEUTRA__list.
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

Definition MeasTriggerQuantityEUTRA__Format_Type := Eval cbn in get_formats MeasTriggerQuantityEUTRA__list.
Definition MeasTriggerQuantityEUTRA__Format_list : MeasTriggerQuantityEUTRA__Format_Type :=
  (RSRP_RangeEUTRA__Format, (RSRQ_RangeEUTRA__Format, (SINR_RangeEUTRA__Format, unit__Format))).
Definition MeasTriggerQuantityEUTRA__list__Format := Eval compute in choice_format MeasTriggerQuantityEUTRA__list MeasTriggerQuantityEUTRA__len_helper1 MeasTriggerQuantityEUTRA__len_helper2  MeasTriggerQuantityEUTRA__Format_list.
Definition MeasTriggerQuantityEUTRA__F1 (z : MeasTriggerQuantityEUTRA__Type) : (choice MeasTriggerQuantityEUTRA__list) :=
  match z with
   | MeasTriggerQuantityEUTRA__rsrp t => existT _ 0 t
  | MeasTriggerQuantityEUTRA__rsrq t => existT _ 1 t
  | MeasTriggerQuantityEUTRA__sinr t => existT _ 2 t
  end.
Definition MeasTriggerQuantityEUTRA__g := (fun n => typ_set (get_nth_typ MeasTriggerQuantityEUTRA__list n)).
Definition MeasTriggerQuantityEUTRA__F2 (y : choice MeasTriggerQuantityEUTRA__list) : MeasTriggerQuantityEUTRA__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasTriggerQuantityEUTRA__g n -> MeasTriggerQuantityEUTRA__Type) with
    | 0 => fun (t : RSRP_RangeEUTRA__Type) => MeasTriggerQuantityEUTRA__rsrp t 
    | 1 => fun (t : RSRQ_RangeEUTRA__Type) => MeasTriggerQuantityEUTRA__rsrq t 
    | 2 => fun (t : SINR_RangeEUTRA__Type) => MeasTriggerQuantityEUTRA__sinr t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : MeasTriggerQuantityEUTRA__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ MeasTriggerQuantityEUTRA__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasTriggerQuantityEUTRA__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return MeasTriggerQuantityEUTRA__Type with end) n0
           end t0).

Lemma MeasTriggerQuantityEUTRA__helper2 :  forall (y : MeasTriggerQuantityEUTRA__Type), MeasTriggerQuantityEUTRA__cond y -> choice_cond MeasTriggerQuantityEUTRA__list (MeasTriggerQuantityEUTRA__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasTriggerQuantityEUTRA__helper3 :  forall (y : MeasTriggerQuantityEUTRA__Type), MeasTriggerQuantityEUTRA__F2 (MeasTriggerQuantityEUTRA__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasTriggerQuantityEUTRA__helper4 : (forall b : choice MeasTriggerQuantityEUTRA__list, choice_cond MeasTriggerQuantityEUTRA__list b -> MeasTriggerQuantityEUTRA__cond (MeasTriggerQuantityEUTRA__F2 b) /\ MeasTriggerQuantityEUTRA__F1 (MeasTriggerQuantityEUTRA__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasTriggerQuantityEUTRA__F1 MeasTriggerQuantityEUTRA__F2.
Definition MeasTriggerQuantityEUTRA__Format : T_Format MeasTriggerQuantityEUTRA__Type MeasTriggerQuantityEUTRA__cond :=
  (* Eval compute in *) proj2_format MeasTriggerQuantityEUTRA__cond MeasTriggerQuantityEUTRA__list__Format MeasTriggerQuantityEUTRA__F1 MeasTriggerQuantityEUTRA__F2 MeasTriggerQuantityEUTRA__helper2 MeasTriggerQuantityEUTRA__helper3 MeasTriggerQuantityEUTRA__helper4.
Opaque MeasTriggerQuantityEUTRA__cond MeasTriggerQuantityEUTRA__Format.

