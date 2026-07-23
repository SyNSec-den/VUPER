Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Type : Set :=
 | RRCResume_v1610_IEs__idleModeMeasurementReq_r16__true
.
Definition RRCResume_v1610_IEs__idleModeMeasurementReq_r16__cond := (fun (_ : RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Type) => True).
Lemma RRCResume_v1610_IEs__idleModeMeasurementReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResume_v1610_IEs__idleModeMeasurementReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResume_v1610_IEs__idleModeMeasurementReq_r16__nat__helper.

Definition RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1 t :=
  match t with
  | RRCResume_v1610_IEs__idleModeMeasurementReq_r16__true => 0
  end.
Definition RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F2 n :=
  match n with
  | 0 => RRCResume_v1610_IEs__idleModeMeasurementReq_r16__true
  | _ => RRCResume_v1610_IEs__idleModeMeasurementReq_r16__true
  end.
Lemma RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1F2 : forall x : RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Type, (RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1 x <= 0) /\ RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F2 (RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1 (RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RRCResume_v1610_IEs__restoreMCG_SCells_r16__Type : Set :=
 | RRCResume_v1610_IEs__restoreMCG_SCells_r16__true
.
Definition RRCResume_v1610_IEs__restoreMCG_SCells_r16__cond := (fun (_ : RRCResume_v1610_IEs__restoreMCG_SCells_r16__Type) => True).
Lemma RRCResume_v1610_IEs__restoreMCG_SCells_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResume_v1610_IEs__restoreMCG_SCells_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResume_v1610_IEs__restoreMCG_SCells_r16__nat__helper.

Definition RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1 t :=
  match t with
  | RRCResume_v1610_IEs__restoreMCG_SCells_r16__true => 0
  end.
Definition RRCResume_v1610_IEs__restoreMCG_SCells_r16__F2 n :=
  match n with
  | 0 => RRCResume_v1610_IEs__restoreMCG_SCells_r16__true
  | _ => RRCResume_v1610_IEs__restoreMCG_SCells_r16__true
  end.
Lemma RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1F2 : forall x : RRCResume_v1610_IEs__restoreMCG_SCells_r16__Type, (RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1 x <= 0) /\ RRCResume_v1610_IEs__restoreMCG_SCells_r16__F2 (RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCResume_v1610_IEs__restoreMCG_SCells_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1 (RRCResume_v1610_IEs__restoreMCG_SCells_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RRCResume_v1610_IEs__restoreSCG_r16__Type : Set :=
 | RRCResume_v1610_IEs__restoreSCG_r16__true
.
Definition RRCResume_v1610_IEs__restoreSCG_r16__cond := (fun (_ : RRCResume_v1610_IEs__restoreSCG_r16__Type) => True).
Lemma RRCResume_v1610_IEs__restoreSCG_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResume_v1610_IEs__restoreSCG_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResume_v1610_IEs__restoreSCG_r16__nat__helper.

Definition RRCResume_v1610_IEs__restoreSCG_r16__F1 t :=
  match t with
  | RRCResume_v1610_IEs__restoreSCG_r16__true => 0
  end.
Definition RRCResume_v1610_IEs__restoreSCG_r16__F2 n :=
  match n with
  | 0 => RRCResume_v1610_IEs__restoreSCG_r16__true
  | _ => RRCResume_v1610_IEs__restoreSCG_r16__true
  end.
Lemma RRCResume_v1610_IEs__restoreSCG_r16__F1F2 : forall x : RRCResume_v1610_IEs__restoreSCG_r16__Type, (RRCResume_v1610_IEs__restoreSCG_r16__F1 x <= 0) /\ RRCResume_v1610_IEs__restoreSCG_r16__F2 (RRCResume_v1610_IEs__restoreSCG_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCResume_v1610_IEs__restoreSCG_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCResume_v1610_IEs__restoreSCG_r16__F1 (RRCResume_v1610_IEs__restoreSCG_r16__F2 y) = y. enum_solve H y. Qed.


Inductive RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type : Set :=
  | RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__nr_SCG_r16 : octet_string -> RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type
  | RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__eutra_SCG_r16 : octet_string -> RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type
.
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list : list typ := (
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond (c : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type) := 
  match c with
  | RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__nr_SCG_r16 t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  | RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__eutra_SCG_r16 t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  end.

Lemma RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__len_helper1 : to_bit_sz (length RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__len_helper2 : 2 <= length2 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list.
 simpl. lia. Qed.
Require Import NR.SetupRelease.
Require Import NR.NeedForGapsConfigNR_r16.
Definition RRCResume_v1610_IEs__needForGapsConfigNR_r16__Type := SetupRelease__Type NeedForGapsConfigNR_r16__Type.
Definition RRCResume_v1610_IEs__needForGapsConfigNR_r16__cond := SetupRelease__cond _ NeedForGapsConfigNR_r16__cond.
Definition RRCResume_v1610_IEs__needForGapsConfigNR_r16__Format : T_Format RRCResume_v1610_IEs__needForGapsConfigNR_r16__Type RRCResume_v1610_IEs__needForGapsConfigNR_r16__cond := SetupRelease__Format _ _ NeedForGapsConfigNR_r16__Format.
Opaque RRCResume_v1610_IEs__needForGapsConfigNR_r16__cond RRCResume_v1610_IEs__needForGapsConfigNR_r16__Format.

Require Import NR.RRCResume_v1700_IEs.

Opaque RRCResume_v1700_IEs__cond RRCResume_v1700_IEs__Format.

Record RRCResume_v1610_IEs__Type : Set :=
  make__RRCResume_v1610_IEs__Type {
    RRCResume_v1610_IEs__idleModeMeasurementReq_r16 : option RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Type ;
    RRCResume_v1610_IEs__restoreMCG_SCells_r16 : option RRCResume_v1610_IEs__restoreMCG_SCells_r16__Type ;
    RRCResume_v1610_IEs__restoreSCG_r16 : option RRCResume_v1610_IEs__restoreSCG_r16__Type ;
    RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16 : option RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type ;
    RRCResume_v1610_IEs__needForGapsConfigNR_r16 : option RRCResume_v1610_IEs__needForGapsConfigNR_r16__Type ;
    RRCResume_v1610_IEs__nonCriticalExtension : option RRCResume_v1700_IEs__Type ;
}.
Definition RRCResume_v1610_IEs__list := (
 Opt RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Type RRCResume_v1610_IEs__idleModeMeasurementReq_r16__cond ::
 Opt RRCResume_v1610_IEs__restoreMCG_SCells_r16__Type RRCResume_v1610_IEs__restoreMCG_SCells_r16__cond ::
 Opt RRCResume_v1610_IEs__restoreSCG_r16__Type RRCResume_v1610_IEs__restoreSCG_r16__cond ::
 Opt RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond ::
 Opt RRCResume_v1610_IEs__needForGapsConfigNR_r16__Type RRCResume_v1610_IEs__needForGapsConfigNR_r16__cond ::
 Opt RRCResume_v1700_IEs__Type RRCResume_v1700_IEs__cond ::
 nil).
Definition RRCResume_v1610_IEs__cond z := 
  opt_cond RRCResume_v1610_IEs__idleModeMeasurementReq_r16__cond (RRCResume_v1610_IEs__idleModeMeasurementReq_r16 z) /\
  opt_cond RRCResume_v1610_IEs__restoreMCG_SCells_r16__cond (RRCResume_v1610_IEs__restoreMCG_SCells_r16 z) /\
  opt_cond RRCResume_v1610_IEs__restoreSCG_r16__cond (RRCResume_v1610_IEs__restoreSCG_r16 z) /\
  opt_cond RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16 z) /\
  opt_cond RRCResume_v1610_IEs__needForGapsConfigNR_r16__cond (RRCResume_v1610_IEs__needForGapsConfigNR_r16 z) /\
  opt_cond RRCResume_v1700_IEs__cond (RRCResume_v1610_IEs__nonCriticalExtension z) /\
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
Definition RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Format : T_Format RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResume_v1610_IEs__idleModeMeasurementReq_r16__nat__Format RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1 RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F2 RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F1F2 RRCResume_v1610_IEs__idleModeMeasurementReq_r16__F2F1.

Opaque RRCResume_v1610_IEs__idleModeMeasurementReq_r16__cond RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Format.

Definition RRCResume_v1610_IEs__restoreMCG_SCells_r16__Format : T_Format RRCResume_v1610_IEs__restoreMCG_SCells_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResume_v1610_IEs__restoreMCG_SCells_r16__nat__Format RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1 RRCResume_v1610_IEs__restoreMCG_SCells_r16__F2 RRCResume_v1610_IEs__restoreMCG_SCells_r16__F1F2 RRCResume_v1610_IEs__restoreMCG_SCells_r16__F2F1.

Opaque RRCResume_v1610_IEs__restoreMCG_SCells_r16__cond RRCResume_v1610_IEs__restoreMCG_SCells_r16__Format.

Definition RRCResume_v1610_IEs__restoreSCG_r16__Format : T_Format RRCResume_v1610_IEs__restoreSCG_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResume_v1610_IEs__restoreSCG_r16__nat__Format RRCResume_v1610_IEs__restoreSCG_r16__F1 RRCResume_v1610_IEs__restoreSCG_r16__F2 RRCResume_v1610_IEs__restoreSCG_r16__F1F2 RRCResume_v1610_IEs__restoreSCG_r16__F2F1.

Opaque RRCResume_v1610_IEs__restoreSCG_r16__cond RRCResume_v1610_IEs__restoreSCG_r16__Format.


Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format_Type := Eval cbn in get_formats RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list.
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format_list : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, unit__Format)).
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list__Format := Eval compute in choice_format RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__len_helper1 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__len_helper2  RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format_list.
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F1 (z : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type) : (choice RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list) :=
  match z with
   | RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__nr_SCG_r16 t => existT _ 0 t
  | RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__eutra_SCG_r16 t => existT _ 1 t
  end.
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__g := (fun n => typ_set (get_nth_typ RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list n)).
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F2 (y : choice RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list) : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__g n -> RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type) with
    | 0 => fun (t : octet_string) => RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__nr_SCG_r16 t 
    | 1 => fun (t : octet_string) => RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__eutra_SCG_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type with end) n0
           end t0).

Lemma RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__helper2 :  forall (y : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type), RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond y -> choice_cond RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__helper3 :  forall (y : RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type), RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F2 (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__helper4 : (forall b : choice RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list, choice_cond RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list b -> RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F2 b) /\ RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F1 (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F1 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F2.
Definition RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format : T_Format RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Type RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond :=
  (* Eval compute in *) proj2_format RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__list__Format RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F1 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__F2 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__helper2 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__helper3 RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__helper4.
Opaque RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__cond RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format.

Opaque RRCResume_v1610_IEs__needForGapsConfigNR_r16__cond RRCResume_v1610_IEs__needForGapsConfigNR_r16__Format.


Definition RRCResume_v1610_IEs__Format_Type := Eval cbn in seq_format_prod RRCResume_v1610_IEs__list.
Definition RRCResume_v1610_IEs__Format_list : RRCResume_v1610_IEs__Format_Type :=
  (RRCResume_v1610_IEs__idleModeMeasurementReq_r16__Format, (RRCResume_v1610_IEs__restoreMCG_SCells_r16__Format, (RRCResume_v1610_IEs__restoreSCG_r16__Format, (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16__Format, (RRCResume_v1610_IEs__needForGapsConfigNR_r16__Format, (RRCResume_v1700_IEs__Format, unit_format)))))).
Definition RRCResume_v1610_IEs__list__Format := (*Eval compute in *) seq_format RRCResume_v1610_IEs__list RRCResume_v1610_IEs__Format_list.
Definition RRCResume_v1610_IEs__F1 z :=
  (RRCResume_v1610_IEs__idleModeMeasurementReq_r16 z, (RRCResume_v1610_IEs__restoreMCG_SCells_r16 z, (RRCResume_v1610_IEs__restoreSCG_r16 z, (RRCResume_v1610_IEs__mrdc_SecondaryCellGroup_r16 z, (RRCResume_v1610_IEs__needForGapsConfigNR_r16 z, (RRCResume_v1610_IEs__nonCriticalExtension z, tt)))))).
Definition RRCResume_v1610_IEs__F2 (y : seq_type RRCResume_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__RRCResume_v1610_IEs__Type i0 i1 i2 i3 i4 i5
  end.
Lemma RRCResume_v1610_IEs__F1F2_cond (z : RRCResume_v1610_IEs__Type)
  : RRCResume_v1610_IEs__cond z ->
  (seq_cond RRCResume_v1610_IEs__list (RRCResume_v1610_IEs__F1 z)).
intro H. unfold RRCResume_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma RRCResume_v1610_IEs__F1F2_cond2 (z : RRCResume_v1610_IEs__Type)
 : RRCResume_v1610_IEs__F2 (RRCResume_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResume_v1610_IEs__F2F1_cond (y : seq_type RRCResume_v1610_IEs__list)
  : seq_cond RRCResume_v1610_IEs__list y ->
 (RRCResume_v1610_IEs__cond (RRCResume_v1610_IEs__F2 y)) /\  RRCResume_v1610_IEs__F1 (RRCResume_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResume_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCResume_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResume_v1610_IEs__Format : T_Format RRCResume_v1610_IEs__Type RRCResume_v1610_IEs__cond :=
        proj2_format  RRCResume_v1610_IEs__cond RRCResume_v1610_IEs__list__Format
    RRCResume_v1610_IEs__F1 RRCResume_v1610_IEs__F2 RRCResume_v1610_IEs__F1F2_cond  RRCResume_v1610_IEs__F1F2_cond2 RRCResume_v1610_IEs__F2F1_cond.
Opaque RRCResume_v1610_IEs__cond RRCResume_v1610_IEs__Format.

