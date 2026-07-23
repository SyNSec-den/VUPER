Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRQ_Range.

Opaque RSRQ_Range__cond RSRQ_Range__Format.

Require Import NR.SINR_Range.

Opaque SINR_Range__cond SINR_Range__Format.


Inductive MeasTriggerQuantity__Type : Set :=
  | MeasTriggerQuantity__rsrp : RSRP_Range__Type -> MeasTriggerQuantity__Type
  | MeasTriggerQuantity__rsrq : RSRQ_Range__Type -> MeasTriggerQuantity__Type
  | MeasTriggerQuantity__sinr : SINR_Range__Type -> MeasTriggerQuantity__Type
.
Definition MeasTriggerQuantity__list : list typ := (
typ_cons RSRP_Range__Type RSRP_Range__cond ::
typ_cons RSRQ_Range__Type RSRQ_Range__cond ::
typ_cons SINR_Range__Type SINR_Range__cond ::
 nil).
Definition MeasTriggerQuantity__cond (c : MeasTriggerQuantity__Type) := 
  match c with
  | MeasTriggerQuantity__rsrp t => RSRP_Range__cond t 
  | MeasTriggerQuantity__rsrq t => RSRQ_Range__cond t 
  | MeasTriggerQuantity__sinr t => SINR_Range__cond t 
  end.

Lemma MeasTriggerQuantity__len_helper1 : to_bit_sz (length MeasTriggerQuantity__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasTriggerQuantity__len_helper2 : 2 <= length2 MeasTriggerQuantity__list.
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

Definition MeasTriggerQuantity__Format_Type := Eval cbn in get_formats MeasTriggerQuantity__list.
Definition MeasTriggerQuantity__Format_list : MeasTriggerQuantity__Format_Type :=
  (RSRP_Range__Format, (RSRQ_Range__Format, (SINR_Range__Format, unit__Format))).
Definition MeasTriggerQuantity__list__Format := Eval compute in choice_format MeasTriggerQuantity__list MeasTriggerQuantity__len_helper1 MeasTriggerQuantity__len_helper2  MeasTriggerQuantity__Format_list.
Definition MeasTriggerQuantity__F1 (z : MeasTriggerQuantity__Type) : (choice MeasTriggerQuantity__list) :=
  match z with
   | MeasTriggerQuantity__rsrp t => existT _ 0 t
  | MeasTriggerQuantity__rsrq t => existT _ 1 t
  | MeasTriggerQuantity__sinr t => existT _ 2 t
  end.
Definition MeasTriggerQuantity__g := (fun n => typ_set (get_nth_typ MeasTriggerQuantity__list n)).
Definition MeasTriggerQuantity__F2 (y : choice MeasTriggerQuantity__list) : MeasTriggerQuantity__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasTriggerQuantity__g n -> MeasTriggerQuantity__Type) with
    | 0 => fun (t : RSRP_Range__Type) => MeasTriggerQuantity__rsrp t 
    | 1 => fun (t : RSRQ_Range__Type) => MeasTriggerQuantity__rsrq t 
    | 2 => fun (t : SINR_Range__Type) => MeasTriggerQuantity__sinr t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : MeasTriggerQuantity__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ MeasTriggerQuantity__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasTriggerQuantity__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return MeasTriggerQuantity__Type with end) n0
           end t0).

Lemma MeasTriggerQuantity__helper2 :  forall (y : MeasTriggerQuantity__Type), MeasTriggerQuantity__cond y -> choice_cond MeasTriggerQuantity__list (MeasTriggerQuantity__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasTriggerQuantity__helper3 :  forall (y : MeasTriggerQuantity__Type), MeasTriggerQuantity__F2 (MeasTriggerQuantity__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasTriggerQuantity__helper4 : (forall b : choice MeasTriggerQuantity__list, choice_cond MeasTriggerQuantity__list b -> MeasTriggerQuantity__cond (MeasTriggerQuantity__F2 b) /\ MeasTriggerQuantity__F1 (MeasTriggerQuantity__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasTriggerQuantity__F1 MeasTriggerQuantity__F2.
Definition MeasTriggerQuantity__Format : T_Format MeasTriggerQuantity__Type MeasTriggerQuantity__cond :=
  (* Eval compute in *) proj2_format MeasTriggerQuantity__cond MeasTriggerQuantity__list__Format MeasTriggerQuantity__F1 MeasTriggerQuantity__F2 MeasTriggerQuantity__helper2 MeasTriggerQuantity__helper3 MeasTriggerQuantity__helper4.
Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

