Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_RSTD_InfoList.

Opaque EUTRA_RSTD_InfoList__cond EUTRA_RSTD_InfoList__Format.


Inductive LocationMeasurementInfo__root__Type : Set := | LocationMeasurementInfo__root__eutra_RSTD : EUTRA_RSTD_InfoList__Type -> LocationMeasurementInfo__root__Type.
Definition LocationMeasurementInfo__root__cond (c : LocationMeasurementInfo__root__Type) := 
  match c with
  | LocationMeasurementInfo__root__eutra_RSTD t => EUTRA_RSTD_InfoList__cond t 
  end.

Require Import NR.NR_PRS_MeasurementInfoList_r16.

Opaque NR_PRS_MeasurementInfoList_r16__cond NR_PRS_MeasurementInfoList_r16__Format.


Inductive LocationMeasurementInfo__ext__Type : Set :=
  | LocationMeasurementInfo__ext__eutra_FineTimingDetection : unit -> LocationMeasurementInfo__ext__Type
  | LocationMeasurementInfo__ext__nr_PRS_Measurement_r16 : NR_PRS_MeasurementInfoList_r16__Type -> LocationMeasurementInfo__ext__Type
.
Definition LocationMeasurementInfo__ext__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons NR_PRS_MeasurementInfoList_r16__Type NR_PRS_MeasurementInfoList_r16__cond ::
 nil).
Definition LocationMeasurementInfo__ext__cond (c : LocationMeasurementInfo__ext__Type) := 
  match c with
  | LocationMeasurementInfo__ext__eutra_FineTimingDetection t => (fun _ => True) t 
  | LocationMeasurementInfo__ext__nr_PRS_Measurement_r16 t => NR_PRS_MeasurementInfoList_r16__cond t 
  end.

Lemma LocationMeasurementInfo__ext__len_helper1 : to_bit_sz (length LocationMeasurementInfo__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition LocationMeasurementInfo__Type : Set := LocationMeasurementInfo__root__Type + LocationMeasurementInfo__ext__Type.
Definition LocationMeasurementInfo__cond :=
  sum_cond LocationMeasurementInfo__root__cond LocationMeasurementInfo__ext__cond.

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
Definition LocationMeasurementInfo__root__F1 (z : LocationMeasurementInfo__root__Type) : EUTRA_RSTD_InfoList__Type := 
  match z with
  | LocationMeasurementInfo__root__eutra_RSTD t => t
  end.
Definition LocationMeasurementInfo__root__F2 (y : EUTRA_RSTD_InfoList__Type) : LocationMeasurementInfo__root__Type := LocationMeasurementInfo__root__eutra_RSTD y.

Definition LocationMeasurementInfo__root__helper2 : (forall z : LocationMeasurementInfo__root__Type, LocationMeasurementInfo__root__cond z -> EUTRA_RSTD_InfoList__cond (LocationMeasurementInfo__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition LocationMeasurementInfo__root__helper3 : (forall z : LocationMeasurementInfo__root__Type, LocationMeasurementInfo__root__F2 (LocationMeasurementInfo__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition LocationMeasurementInfo__root__helper4 : (forall y : EUTRA_RSTD_InfoList__Type, EUTRA_RSTD_InfoList__cond y -> LocationMeasurementInfo__root__cond (LocationMeasurementInfo__root__F2 y) /\  LocationMeasurementInfo__root__F1 (LocationMeasurementInfo__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition LocationMeasurementInfo__root__Format : T_Format LocationMeasurementInfo__root__Type LocationMeasurementInfo__root__cond :=
  proj2_format LocationMeasurementInfo__root__cond EUTRA_RSTD_InfoList__Format LocationMeasurementInfo__root__F1 LocationMeasurementInfo__root__F2 LocationMeasurementInfo__root__helper2 LocationMeasurementInfo__root__helper3 LocationMeasurementInfo__root__helper4.
Opaque LocationMeasurementInfo__root__cond LocationMeasurementInfo__root__Format.


Definition LocationMeasurementInfo__ext__Format_Type := Eval cbn in get_formats LocationMeasurementInfo__ext__list.
Definition LocationMeasurementInfo__ext__Format_list : LocationMeasurementInfo__ext__Format_Type :=
  (unit__Format, (NR_PRS_MeasurementInfoList_r16__Format, unit__Format)).
Definition LocationMeasurementInfo__ext__list__Format := Eval compute in choice_ext_format LocationMeasurementInfo__ext__list LocationMeasurementInfo__ext__Format_list.
Definition LocationMeasurementInfo__ext__F1 (z : LocationMeasurementInfo__ext__Type) : (choice LocationMeasurementInfo__ext__list) :=
  match z with
   | LocationMeasurementInfo__ext__eutra_FineTimingDetection t => existT _ 0 t
  | LocationMeasurementInfo__ext__nr_PRS_Measurement_r16 t => existT _ 1 t
  end.
Definition LocationMeasurementInfo__ext__g := (fun n => typ_set (get_nth_typ LocationMeasurementInfo__ext__list n)).
Definition LocationMeasurementInfo__ext__F2 (y : choice LocationMeasurementInfo__ext__list) : LocationMeasurementInfo__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (LocationMeasurementInfo__ext__g n -> LocationMeasurementInfo__ext__Type) with
    | 0 => fun (t : unit) => LocationMeasurementInfo__ext__eutra_FineTimingDetection t 
    | 1 => fun (t : NR_PRS_MeasurementInfoList_r16__Type) => LocationMeasurementInfo__ext__nr_PRS_Measurement_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : LocationMeasurementInfo__ext__g (S (S x'))) =>let t' :=
                       eq_rect (get_nth_typ LocationMeasurementInfo__ext__list (S (S x')))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len LocationMeasurementInfo__ext__list (S (S x'))
                       (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return LocationMeasurementInfo__ext__Type with end) n0
                       end t0).

Lemma LocationMeasurementInfo__ext__helper2 :  forall (y : LocationMeasurementInfo__ext__Type), LocationMeasurementInfo__ext__cond y -> choice_cond LocationMeasurementInfo__ext__list (LocationMeasurementInfo__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma LocationMeasurementInfo__ext__helper3 :  forall (y : LocationMeasurementInfo__ext__Type), LocationMeasurementInfo__ext__F2 (LocationMeasurementInfo__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma LocationMeasurementInfo__ext__helper4 : (forall b : choice LocationMeasurementInfo__ext__list, choice_cond LocationMeasurementInfo__ext__list b -> LocationMeasurementInfo__ext__cond (LocationMeasurementInfo__ext__F2 b) /\ LocationMeasurementInfo__ext__F1 (LocationMeasurementInfo__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length LocationMeasurementInfo__ext__F1 LocationMeasurementInfo__ext__F2.
Definition LocationMeasurementInfo__ext__Format : T_Format LocationMeasurementInfo__ext__Type LocationMeasurementInfo__ext__cond :=
          proj2_format LocationMeasurementInfo__ext__cond LocationMeasurementInfo__ext__list__Format LocationMeasurementInfo__ext__F1 LocationMeasurementInfo__ext__F2 LocationMeasurementInfo__ext__helper2 LocationMeasurementInfo__ext__helper3 LocationMeasurementInfo__ext__helper4.
Opaque LocationMeasurementInfo__ext__cond LocationMeasurementInfo__ext__Format.

Definition LocationMeasurementInfo__Format : T_Format LocationMeasurementInfo__Type LocationMeasurementInfo__cond := sum_format LocationMeasurementInfo__root__Format LocationMeasurementInfo__ext__Format.
Opaque LocationMeasurementInfo__cond LocationMeasurementInfo__Format.

