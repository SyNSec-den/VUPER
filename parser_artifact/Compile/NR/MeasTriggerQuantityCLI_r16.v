Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_RSRP_Range_r16.

Opaque SRS_RSRP_Range_r16__cond SRS_RSRP_Range_r16__Format.

Require Import NR.CLI_RSSI_Range_r16.

Opaque CLI_RSSI_Range_r16__cond CLI_RSSI_Range_r16__Format.


Inductive MeasTriggerQuantityCLI_r16__Type : Set :=
  | MeasTriggerQuantityCLI_r16__srs_RSRP_r16 : SRS_RSRP_Range_r16__Type -> MeasTriggerQuantityCLI_r16__Type
  | MeasTriggerQuantityCLI_r16__cli_RSSI_r16 : CLI_RSSI_Range_r16__Type -> MeasTriggerQuantityCLI_r16__Type
.
Definition MeasTriggerQuantityCLI_r16__list : list typ := (
typ_cons SRS_RSRP_Range_r16__Type SRS_RSRP_Range_r16__cond ::
typ_cons CLI_RSSI_Range_r16__Type CLI_RSSI_Range_r16__cond ::
 nil).
Definition MeasTriggerQuantityCLI_r16__cond (c : MeasTriggerQuantityCLI_r16__Type) := 
  match c with
  | MeasTriggerQuantityCLI_r16__srs_RSRP_r16 t => SRS_RSRP_Range_r16__cond t 
  | MeasTriggerQuantityCLI_r16__cli_RSSI_r16 t => CLI_RSSI_Range_r16__cond t 
  end.

Lemma MeasTriggerQuantityCLI_r16__len_helper1 : to_bit_sz (length MeasTriggerQuantityCLI_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasTriggerQuantityCLI_r16__len_helper2 : 2 <= length2 MeasTriggerQuantityCLI_r16__list.
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

Definition MeasTriggerQuantityCLI_r16__Format_Type := Eval cbn in get_formats MeasTriggerQuantityCLI_r16__list.
Definition MeasTriggerQuantityCLI_r16__Format_list : MeasTriggerQuantityCLI_r16__Format_Type :=
  (SRS_RSRP_Range_r16__Format, (CLI_RSSI_Range_r16__Format, unit__Format)).
Definition MeasTriggerQuantityCLI_r16__list__Format := Eval compute in choice_format MeasTriggerQuantityCLI_r16__list MeasTriggerQuantityCLI_r16__len_helper1 MeasTriggerQuantityCLI_r16__len_helper2  MeasTriggerQuantityCLI_r16__Format_list.
Definition MeasTriggerQuantityCLI_r16__F1 (z : MeasTriggerQuantityCLI_r16__Type) : (choice MeasTriggerQuantityCLI_r16__list) :=
  match z with
   | MeasTriggerQuantityCLI_r16__srs_RSRP_r16 t => existT _ 0 t
  | MeasTriggerQuantityCLI_r16__cli_RSSI_r16 t => existT _ 1 t
  end.
Definition MeasTriggerQuantityCLI_r16__g := (fun n => typ_set (get_nth_typ MeasTriggerQuantityCLI_r16__list n)).
Definition MeasTriggerQuantityCLI_r16__F2 (y : choice MeasTriggerQuantityCLI_r16__list) : MeasTriggerQuantityCLI_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasTriggerQuantityCLI_r16__g n -> MeasTriggerQuantityCLI_r16__Type) with
    | 0 => fun (t : SRS_RSRP_Range_r16__Type) => MeasTriggerQuantityCLI_r16__srs_RSRP_r16 t 
    | 1 => fun (t : CLI_RSSI_Range_r16__Type) => MeasTriggerQuantityCLI_r16__cli_RSSI_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasTriggerQuantityCLI_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasTriggerQuantityCLI_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasTriggerQuantityCLI_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasTriggerQuantityCLI_r16__Type with end) n0
           end t0).

Lemma MeasTriggerQuantityCLI_r16__helper2 :  forall (y : MeasTriggerQuantityCLI_r16__Type), MeasTriggerQuantityCLI_r16__cond y -> choice_cond MeasTriggerQuantityCLI_r16__list (MeasTriggerQuantityCLI_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasTriggerQuantityCLI_r16__helper3 :  forall (y : MeasTriggerQuantityCLI_r16__Type), MeasTriggerQuantityCLI_r16__F2 (MeasTriggerQuantityCLI_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasTriggerQuantityCLI_r16__helper4 : (forall b : choice MeasTriggerQuantityCLI_r16__list, choice_cond MeasTriggerQuantityCLI_r16__list b -> MeasTriggerQuantityCLI_r16__cond (MeasTriggerQuantityCLI_r16__F2 b) /\ MeasTriggerQuantityCLI_r16__F1 (MeasTriggerQuantityCLI_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasTriggerQuantityCLI_r16__F1 MeasTriggerQuantityCLI_r16__F2.
Definition MeasTriggerQuantityCLI_r16__Format : T_Format MeasTriggerQuantityCLI_r16__Type MeasTriggerQuantityCLI_r16__cond :=
  (* Eval compute in *) proj2_format MeasTriggerQuantityCLI_r16__cond MeasTriggerQuantityCLI_r16__list__Format MeasTriggerQuantityCLI_r16__F1 MeasTriggerQuantityCLI_r16__F2 MeasTriggerQuantityCLI_r16__helper2 MeasTriggerQuantityCLI_r16__helper3 MeasTriggerQuantityCLI_r16__helper4.
Opaque MeasTriggerQuantityCLI_r16__cond MeasTriggerQuantityCLI_r16__Format.

