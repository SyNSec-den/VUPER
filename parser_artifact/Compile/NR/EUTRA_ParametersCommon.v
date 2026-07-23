Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EUTRA_ParametersCommon__mfbi_EUTRA__Type : Set :=
 | EUTRA_ParametersCommon__mfbi_EUTRA__supported
.
Definition EUTRA_ParametersCommon__mfbi_EUTRA__cond := (fun (_ : EUTRA_ParametersCommon__mfbi_EUTRA__Type) => True).
Lemma EUTRA_ParametersCommon__mfbi_EUTRA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_ParametersCommon__mfbi_EUTRA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EUTRA_ParametersCommon__mfbi_EUTRA__nat__helper.

Definition EUTRA_ParametersCommon__mfbi_EUTRA__F1 t :=
  match t with
  | EUTRA_ParametersCommon__mfbi_EUTRA__supported => 0
  end.
Definition EUTRA_ParametersCommon__mfbi_EUTRA__F2 n :=
  match n with
  | 0 => EUTRA_ParametersCommon__mfbi_EUTRA__supported
  | _ => EUTRA_ParametersCommon__mfbi_EUTRA__supported
  end.
Lemma EUTRA_ParametersCommon__mfbi_EUTRA__F1F2 : forall x : EUTRA_ParametersCommon__mfbi_EUTRA__Type, (EUTRA_ParametersCommon__mfbi_EUTRA__F1 x <= 0) /\ EUTRA_ParametersCommon__mfbi_EUTRA__F2 (EUTRA_ParametersCommon__mfbi_EUTRA__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_ParametersCommon__mfbi_EUTRA__F2F1 : forall (y : nat) (H : y <= 0), EUTRA_ParametersCommon__mfbi_EUTRA__F1 (EUTRA_ParametersCommon__mfbi_EUTRA__F2 y) = y. enum_solve H y. Qed.

Definition EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Type := bit_string_fixed.
Definition EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 32 /\ bit_string_len_prop (fst z) (snd z)).
Inductive EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Type : Set :=
 | EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__supported
.
Definition EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__cond := (fun (_ : EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Type) => True).
Lemma EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__nat__helper.

Definition EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1 t :=
  match t with
  | EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__supported => 0
  end.
Definition EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F2 n :=
  match n with
  | 0 => EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__supported
  | _ => EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__supported
  end.
Lemma EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1F2 : forall x : EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Type, (EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1 x <= 0) /\ EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F2 (EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F2F1 : forall (y : nat) (H : y <= 0), EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1 (EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F2 y) = y. enum_solve H y. Qed.

Inductive EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Type : Set :=
 | EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__supported
.
Definition EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__cond := (fun (_ : EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Type) => True).
Lemma EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__nat__helper.

Definition EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1 t :=
  match t with
  | EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__supported => 0
  end.
Definition EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F2 n :=
  match n with
  | 0 => EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__supported
  | _ => EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__supported
  end.
Lemma EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1F2 : forall x : EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Type, (EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1 x <= 0) /\ EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F2 (EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F2F1 : forall (y : nat) (H : y <= 0), EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1 (EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F2 y) = y. enum_solve H y. Qed.

Inductive EUTRA_ParametersCommon__ext0O__ne_DC__Type : Set :=
 | EUTRA_ParametersCommon__ext0O__ne_DC__supported
.
Definition EUTRA_ParametersCommon__ext0O__ne_DC__cond := (fun (_ : EUTRA_ParametersCommon__ext0O__ne_DC__Type) => True).
Lemma EUTRA_ParametersCommon__ext0O__ne_DC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_ParametersCommon__ext0O__ne_DC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EUTRA_ParametersCommon__ext0O__ne_DC__nat__helper.

Definition EUTRA_ParametersCommon__ext0O__ne_DC__F1 t :=
  match t with
  | EUTRA_ParametersCommon__ext0O__ne_DC__supported => 0
  end.
Definition EUTRA_ParametersCommon__ext0O__ne_DC__F2 n :=
  match n with
  | 0 => EUTRA_ParametersCommon__ext0O__ne_DC__supported
  | _ => EUTRA_ParametersCommon__ext0O__ne_DC__supported
  end.
Lemma EUTRA_ParametersCommon__ext0O__ne_DC__F1F2 : forall x : EUTRA_ParametersCommon__ext0O__ne_DC__Type, (EUTRA_ParametersCommon__ext0O__ne_DC__F1 x <= 0) /\ EUTRA_ParametersCommon__ext0O__ne_DC__F2 (EUTRA_ParametersCommon__ext0O__ne_DC__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_ParametersCommon__ext0O__ne_DC__F2F1 : forall (y : nat) (H : y <= 0), EUTRA_ParametersCommon__ext0O__ne_DC__F1 (EUTRA_ParametersCommon__ext0O__ne_DC__F2 y) = y. enum_solve H y. Qed.

Record EUTRA_ParametersCommon__ext0O__Type : Set :=
  make__EUTRA_ParametersCommon__ext0O__Type {
    EUTRA_ParametersCommon__ext0O__ne_DC : option EUTRA_ParametersCommon__ext0O__ne_DC__Type ;
}.
Definition EUTRA_ParametersCommon__ext0O__list := (
 Opt EUTRA_ParametersCommon__ext0O__ne_DC__Type EUTRA_ParametersCommon__ext0O__ne_DC__cond ::
 nil).
Definition EUTRA_ParametersCommon__ext0O__cond z := 
  opt_cond EUTRA_ParametersCommon__ext0O__ne_DC__cond (EUTRA_ParametersCommon__ext0O__ne_DC z) /\
  True.

Definition EUTRA_ParametersCommon__ext0__Type := EUTRA_ParametersCommon__ext0O__Type.
Definition EUTRA_ParametersCommon__ext0__cond := EUTRA_ParametersCommon__ext0O__cond.

Inductive EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Type : Set :=
 | EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__supported
.
Definition EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__cond := (fun (_ : EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Type) => True).
Lemma EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__nat__helper.

Definition EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1 t :=
  match t with
  | EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__supported => 0
  end.
Definition EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F2 n :=
  match n with
  | 0 => EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__supported
  | _ => EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__supported
  end.
Lemma EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1F2 : forall x : EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Type, (EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1 x <= 0) /\ EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F2 (EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F2F1 : forall (y : nat) (H : y <= 0), EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1 (EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F2 y) = y. enum_solve H y. Qed.

Record EUTRA_ParametersCommon__ext1O__Type : Set :=
  make__EUTRA_ParametersCommon__ext1O__Type {
    EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16 : option EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Type ;
}.
Definition EUTRA_ParametersCommon__ext1O__list := (
 Opt EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Type EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__cond ::
 nil).
Definition EUTRA_ParametersCommon__ext1O__cond z := 
  opt_cond EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__cond (EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16 z) /\
  True.

Definition EUTRA_ParametersCommon__ext1__Type := EUTRA_ParametersCommon__ext1O__Type.
Definition EUTRA_ParametersCommon__ext1__cond := EUTRA_ParametersCommon__ext1O__cond.

Record EUTRA_ParametersCommon__Type : Set :=
  make__EUTRA_ParametersCommon__Type {
    EUTRA_ParametersCommon__mfbi_EUTRA : option EUTRA_ParametersCommon__mfbi_EUTRA__Type ;
    EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA : option EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Type ;
    EUTRA_ParametersCommon__multiNS_Pmax_EUTRA : option EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Type ;
    EUTRA_ParametersCommon__rs_SINR_MeasEUTRA : option EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Type ;
    EUTRA_ParametersCommon__ext0 : option EUTRA_ParametersCommon__ext0__Type ;
    EUTRA_ParametersCommon__ext1 : option EUTRA_ParametersCommon__ext1__Type ;
}.
Definition EUTRA_ParametersCommon__root_list : list seq_elem := (
 Opt EUTRA_ParametersCommon__mfbi_EUTRA__Type EUTRA_ParametersCommon__mfbi_EUTRA__cond ::
 Opt EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Type EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__cond ::
 Opt EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Type EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__cond ::
 Opt EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Type EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__cond ::
 nil).
Definition EUTRA_ParametersCommon__ext_list : list typ := (
  typ_cons EUTRA_ParametersCommon__ext0__Type EUTRA_ParametersCommon__ext0__cond ::
  typ_cons EUTRA_ParametersCommon__ext1__Type EUTRA_ParametersCommon__ext1__cond ::
  nil).
Definition EUTRA_ParametersCommon__cond (z : EUTRA_ParametersCommon__Type) := 
(  opt_cond EUTRA_ParametersCommon__mfbi_EUTRA__cond (EUTRA_ParametersCommon__mfbi_EUTRA z) /\
  opt_cond EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__cond (EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA z) /\
  opt_cond EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__cond (EUTRA_ParametersCommon__multiNS_Pmax_EUTRA z) /\
  opt_cond EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__cond (EUTRA_ParametersCommon__rs_SINR_MeasEUTRA z) /\
  True) /\ 
(  opt_cond EUTRA_ParametersCommon__ext0__cond (EUTRA_ParametersCommon__ext0 z) /\
  opt_cond EUTRA_ParametersCommon__ext1__cond (EUTRA_ParametersCommon__ext1 z) /\
  True).


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
Definition EUTRA_ParametersCommon__mfbi_EUTRA__Format : T_Format EUTRA_ParametersCommon__mfbi_EUTRA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_ParametersCommon__mfbi_EUTRA__nat__Format EUTRA_ParametersCommon__mfbi_EUTRA__F1 EUTRA_ParametersCommon__mfbi_EUTRA__F2 EUTRA_ParametersCommon__mfbi_EUTRA__F1F2 EUTRA_ParametersCommon__mfbi_EUTRA__F2F1.

Opaque EUTRA_ParametersCommon__mfbi_EUTRA__cond EUTRA_ParametersCommon__mfbi_EUTRA__Format.

Definition EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Format : T_Format EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Type EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__cond := (* Eval compute in *) bit_string_fixed_format 32.
Opaque EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__cond EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Format.

Definition EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Format : T_Format EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__nat__Format EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1 EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F2 EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F1F2 EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__F2F1.

Opaque EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__cond EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Format.

Definition EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Format : T_Format EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__nat__Format EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1 EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F2 EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F1F2 EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__F2F1.

Opaque EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__cond EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Format.

Definition EUTRA_ParametersCommon__ext0O__ne_DC__Format : T_Format EUTRA_ParametersCommon__ext0O__ne_DC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_ParametersCommon__ext0O__ne_DC__nat__Format EUTRA_ParametersCommon__ext0O__ne_DC__F1 EUTRA_ParametersCommon__ext0O__ne_DC__F2 EUTRA_ParametersCommon__ext0O__ne_DC__F1F2 EUTRA_ParametersCommon__ext0O__ne_DC__F2F1.

Opaque EUTRA_ParametersCommon__ext0O__ne_DC__cond EUTRA_ParametersCommon__ext0O__ne_DC__Format.


Definition EUTRA_ParametersCommon__ext0O__Format_Type := Eval cbn in seq_format_prod EUTRA_ParametersCommon__ext0O__list.
Definition EUTRA_ParametersCommon__ext0O__Format_list : EUTRA_ParametersCommon__ext0O__Format_Type :=
  (EUTRA_ParametersCommon__ext0O__ne_DC__Format, unit_format).
Definition EUTRA_ParametersCommon__ext0O__list__Format := (*Eval compute in *) seq_format EUTRA_ParametersCommon__ext0O__list EUTRA_ParametersCommon__ext0O__Format_list.
Definition EUTRA_ParametersCommon__ext0O__F1 z :=
  (EUTRA_ParametersCommon__ext0O__ne_DC z, tt).
Definition EUTRA_ParametersCommon__ext0O__F2 (y : seq_type EUTRA_ParametersCommon__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__EUTRA_ParametersCommon__ext0O__Type i0
  end.
Lemma EUTRA_ParametersCommon__ext0O__F1F2_cond (z : EUTRA_ParametersCommon__ext0O__Type)
  : EUTRA_ParametersCommon__ext0O__cond z ->
  (seq_cond EUTRA_ParametersCommon__ext0O__list (EUTRA_ParametersCommon__ext0O__F1 z)).
intro H. unfold EUTRA_ParametersCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma EUTRA_ParametersCommon__ext0O__F1F2_cond2 (z : EUTRA_ParametersCommon__ext0O__Type)
 : EUTRA_ParametersCommon__ext0O__F2 (EUTRA_ParametersCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EUTRA_ParametersCommon__ext0O__F2F1_cond (y : seq_type EUTRA_ParametersCommon__ext0O__list)
  : seq_cond EUTRA_ParametersCommon__ext0O__list y ->
 (EUTRA_ParametersCommon__ext0O__cond (EUTRA_ParametersCommon__ext0O__F2 y)) /\  EUTRA_ParametersCommon__ext0O__F1 (EUTRA_ParametersCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EUTRA_ParametersCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold EUTRA_ParametersCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EUTRA_ParametersCommon__ext0O__Format : T_Format EUTRA_ParametersCommon__ext0O__Type EUTRA_ParametersCommon__ext0O__cond :=
        proj2_format  EUTRA_ParametersCommon__ext0O__cond EUTRA_ParametersCommon__ext0O__list__Format
    EUTRA_ParametersCommon__ext0O__F1 EUTRA_ParametersCommon__ext0O__F2 EUTRA_ParametersCommon__ext0O__F1F2_cond  EUTRA_ParametersCommon__ext0O__F1F2_cond2 EUTRA_ParametersCommon__ext0O__F2F1_cond.
Opaque EUTRA_ParametersCommon__ext0O__cond EUTRA_ParametersCommon__ext0O__Format.

Definition EUTRA_ParametersCommon__ext0__check_all_none (b : EUTRA_ParametersCommon__ext0O__Type) : bool :=
match b with 
  | make__EUTRA_ParametersCommon__ext0O__Type None  => false 
  | _ => true 
 end.
Definition EUTRA_ParametersCommon__ext0__Format : T_Format EUTRA_ParametersCommon__ext0__Type EUTRA_ParametersCommon__ext0__cond :=
  restrict_add_format EUTRA_ParametersCommon__ext0__check_all_none EUTRA_ParametersCommon__ext0O__Format.

Opaque EUTRA_ParametersCommon__ext0__cond EUTRA_ParametersCommon__ext0__Format.

Definition EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Format : T_Format EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__nat__Format EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1 EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F2 EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F1F2 EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__F2F1.

Opaque EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__cond EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Format.


Definition EUTRA_ParametersCommon__ext1O__Format_Type := Eval cbn in seq_format_prod EUTRA_ParametersCommon__ext1O__list.
Definition EUTRA_ParametersCommon__ext1O__Format_list : EUTRA_ParametersCommon__ext1O__Format_Type :=
  (EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16__Format, unit_format).
Definition EUTRA_ParametersCommon__ext1O__list__Format := (*Eval compute in *) seq_format EUTRA_ParametersCommon__ext1O__list EUTRA_ParametersCommon__ext1O__Format_list.
Definition EUTRA_ParametersCommon__ext1O__F1 z :=
  (EUTRA_ParametersCommon__ext1O__nr_HO_ToEN_DC_r16 z, tt).
Definition EUTRA_ParametersCommon__ext1O__F2 (y : seq_type EUTRA_ParametersCommon__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__EUTRA_ParametersCommon__ext1O__Type i0
  end.
Lemma EUTRA_ParametersCommon__ext1O__F1F2_cond (z : EUTRA_ParametersCommon__ext1O__Type)
  : EUTRA_ParametersCommon__ext1O__cond z ->
  (seq_cond EUTRA_ParametersCommon__ext1O__list (EUTRA_ParametersCommon__ext1O__F1 z)).
intro H. unfold EUTRA_ParametersCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma EUTRA_ParametersCommon__ext1O__F1F2_cond2 (z : EUTRA_ParametersCommon__ext1O__Type)
 : EUTRA_ParametersCommon__ext1O__F2 (EUTRA_ParametersCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EUTRA_ParametersCommon__ext1O__F2F1_cond (y : seq_type EUTRA_ParametersCommon__ext1O__list)
  : seq_cond EUTRA_ParametersCommon__ext1O__list y ->
 (EUTRA_ParametersCommon__ext1O__cond (EUTRA_ParametersCommon__ext1O__F2 y)) /\  EUTRA_ParametersCommon__ext1O__F1 (EUTRA_ParametersCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EUTRA_ParametersCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold EUTRA_ParametersCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EUTRA_ParametersCommon__ext1O__Format : T_Format EUTRA_ParametersCommon__ext1O__Type EUTRA_ParametersCommon__ext1O__cond :=
        proj2_format  EUTRA_ParametersCommon__ext1O__cond EUTRA_ParametersCommon__ext1O__list__Format
    EUTRA_ParametersCommon__ext1O__F1 EUTRA_ParametersCommon__ext1O__F2 EUTRA_ParametersCommon__ext1O__F1F2_cond  EUTRA_ParametersCommon__ext1O__F1F2_cond2 EUTRA_ParametersCommon__ext1O__F2F1_cond.
Opaque EUTRA_ParametersCommon__ext1O__cond EUTRA_ParametersCommon__ext1O__Format.

Definition EUTRA_ParametersCommon__ext1__check_all_none (b : EUTRA_ParametersCommon__ext1O__Type) : bool :=
match b with 
  | make__EUTRA_ParametersCommon__ext1O__Type None  => false 
  | _ => true 
 end.
Definition EUTRA_ParametersCommon__ext1__Format : T_Format EUTRA_ParametersCommon__ext1__Type EUTRA_ParametersCommon__ext1__cond :=
  restrict_add_format EUTRA_ParametersCommon__ext1__check_all_none EUTRA_ParametersCommon__ext1O__Format.

Opaque EUTRA_ParametersCommon__ext1__cond EUTRA_ParametersCommon__ext1__Format.


Definition EUTRA_ParametersCommon__root_Format_Type := Eval cbn in seq_format_prod EUTRA_ParametersCommon__root_list.
Definition EUTRA_ParametersCommon__root_Format_list : EUTRA_ParametersCommon__root_Format_Type :=
  (EUTRA_ParametersCommon__mfbi_EUTRA__Format, (EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA__Format, (EUTRA_ParametersCommon__multiNS_Pmax_EUTRA__Format, (EUTRA_ParametersCommon__rs_SINR_MeasEUTRA__Format, unit_format)))).

Definition EUTRA_ParametersCommon__ext_Format_Type := Eval cbn in get_formats EUTRA_ParametersCommon__ext_list.
Definition EUTRA_ParametersCommon__ext_Format_list : EUTRA_ParametersCommon__ext_Format_Type :=
  (EUTRA_ParametersCommon__ext0__Format, (EUTRA_ParametersCommon__ext1__Format, unit__Format)).

Definition EUTRA_ParametersCommon__list_type : Set := (seq_type EUTRA_ParametersCommon__root_list) * (seq_ext_type EUTRA_ParametersCommon__ext_list).
Definition EUTRA_ParametersCommon__list_cond (z : EUTRA_ParametersCommon__list_type) : Prop :=
        (seq_cond EUTRA_ParametersCommon__root_list (fst z)) /\ (seq_ext_cond EUTRA_ParametersCommon__ext_list (snd z)).
Definition EUTRA_ParametersCommon__list_format : T_Format EUTRA_ParametersCommon__list_type EUTRA_ParametersCommon__list_cond :=
 (* Eval compute in *) seq_ext_format EUTRA_ParametersCommon__root_list EUTRA_ParametersCommon__root_Format_list EUTRA_ParametersCommon__ext_list EUTRA_ParametersCommon__ext_Format_list.

Opaque EUTRA_ParametersCommon__list_format.
Definition EUTRA_ParametersCommon__F1 (z : EUTRA_ParametersCommon__Type) : EUTRA_ParametersCommon__list_type :=
  (((EUTRA_ParametersCommon__mfbi_EUTRA z, (EUTRA_ParametersCommon__modifiedMPR_BehaviorEUTRA z, (EUTRA_ParametersCommon__multiNS_Pmax_EUTRA z, (EUTRA_ParametersCommon__rs_SINR_MeasEUTRA z, tt))))), (
(EUTRA_ParametersCommon__ext0 z, (EUTRA_ParametersCommon__ext1 z, tt)))).
Definition EUTRA_ParametersCommon__F2 (y : EUTRA_ParametersCommon__list_type) : EUTRA_ParametersCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__EUTRA_ParametersCommon__Type j0 j1 j2 j3 i0 i1
  end.
Definition EUTRA_ParametersCommon__helper1 : (forall a : EUTRA_ParametersCommon__Type, EUTRA_ParametersCommon__cond a -> EUTRA_ParametersCommon__list_cond (EUTRA_ParametersCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EUTRA_ParametersCommon__helper2 : (forall a : EUTRA_ParametersCommon__Type, EUTRA_ParametersCommon__F2 (EUTRA_ParametersCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EUTRA_ParametersCommon__helper3 : (forall b : EUTRA_ParametersCommon__list_type, EUTRA_ParametersCommon__list_cond b -> EUTRA_ParametersCommon__cond (EUTRA_ParametersCommon__F2 b) /\ EUTRA_ParametersCommon__F1 (EUTRA_ParametersCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EUTRA_ParametersCommon__cond, EUTRA_ParametersCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EUTRA_ParametersCommon__Format : T_Format EUTRA_ParametersCommon__Type EUTRA_ParametersCommon__cond :=
 proj2_format EUTRA_ParametersCommon__cond EUTRA_ParametersCommon__list_format  EUTRA_ParametersCommon__F1 EUTRA_ParametersCommon__F2 EUTRA_ParametersCommon__helper1 EUTRA_ParametersCommon__helper2 EUTRA_ParametersCommon__helper3.

Opaque EUTRA_ParametersCommon__cond EUTRA_ParametersCommon__Format.

