Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CA_ParametersNR__dummy__Type : Set :=
 | CA_ParametersNR__dummy__supported
.
Definition CA_ParametersNR__dummy__cond := (fun (_ : CA_ParametersNR__dummy__Type) => True).
Lemma CA_ParametersNR__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__dummy__nat__helper.

Definition CA_ParametersNR__dummy__F1 t :=
  match t with
  | CA_ParametersNR__dummy__supported => 0
  end.
Definition CA_ParametersNR__dummy__F2 n :=
  match n with
  | 0 => CA_ParametersNR__dummy__supported
  | _ => CA_ParametersNR__dummy__supported
  end.
Lemma CA_ParametersNR__dummy__F1F2 : forall x : CA_ParametersNR__dummy__Type, (CA_ParametersNR__dummy__F1 x <= 0) /\ CA_ParametersNR__dummy__F2 (CA_ParametersNR__dummy__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__dummy__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__dummy__F1 (CA_ParametersNR__dummy__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Type : Set :=
 | CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__supported
.
Definition CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__cond := (fun (_ : CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Type) => True).
Lemma CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__nat__helper.

Definition CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1 t :=
  match t with
  | CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__supported => 0
  end.
Definition CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F2 n :=
  match n with
  | 0 => CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__supported
  | _ => CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__supported
  end.
Lemma CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1F2 : forall x : CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Type, (CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1 x <= 0) /\ CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F2 (CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1 (CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Type : Set :=
 | CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__supported
.
Definition CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__cond := (fun (_ : CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Type) => True).
Lemma CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__nat__helper.

Definition CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1 t :=
  match t with
  | CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__supported => 0
  end.
Definition CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F2 n :=
  match n with
  | 0 => CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__supported
  | _ => CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__supported
  end.
Lemma CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1F2 : forall x : CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Type, (CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1 x <= 0) /\ CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F2 (CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1 (CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__simultaneousRxTxInterBandCA__Type : Set :=
 | CA_ParametersNR__simultaneousRxTxInterBandCA__supported
.
Definition CA_ParametersNR__simultaneousRxTxInterBandCA__cond := (fun (_ : CA_ParametersNR__simultaneousRxTxInterBandCA__Type) => True).
Lemma CA_ParametersNR__simultaneousRxTxInterBandCA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__simultaneousRxTxInterBandCA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__simultaneousRxTxInterBandCA__nat__helper.

Definition CA_ParametersNR__simultaneousRxTxInterBandCA__F1 t :=
  match t with
  | CA_ParametersNR__simultaneousRxTxInterBandCA__supported => 0
  end.
Definition CA_ParametersNR__simultaneousRxTxInterBandCA__F2 n :=
  match n with
  | 0 => CA_ParametersNR__simultaneousRxTxInterBandCA__supported
  | _ => CA_ParametersNR__simultaneousRxTxInterBandCA__supported
  end.
Lemma CA_ParametersNR__simultaneousRxTxInterBandCA__F1F2 : forall x : CA_ParametersNR__simultaneousRxTxInterBandCA__Type, (CA_ParametersNR__simultaneousRxTxInterBandCA__F1 x <= 0) /\ CA_ParametersNR__simultaneousRxTxInterBandCA__F2 (CA_ParametersNR__simultaneousRxTxInterBandCA__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__simultaneousRxTxInterBandCA__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__simultaneousRxTxInterBandCA__F1 (CA_ParametersNR__simultaneousRxTxInterBandCA__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__simultaneousRxTxSUL__Type : Set :=
 | CA_ParametersNR__simultaneousRxTxSUL__supported
.
Definition CA_ParametersNR__simultaneousRxTxSUL__cond := (fun (_ : CA_ParametersNR__simultaneousRxTxSUL__Type) => True).
Lemma CA_ParametersNR__simultaneousRxTxSUL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__simultaneousRxTxSUL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__simultaneousRxTxSUL__nat__helper.

Definition CA_ParametersNR__simultaneousRxTxSUL__F1 t :=
  match t with
  | CA_ParametersNR__simultaneousRxTxSUL__supported => 0
  end.
Definition CA_ParametersNR__simultaneousRxTxSUL__F2 n :=
  match n with
  | 0 => CA_ParametersNR__simultaneousRxTxSUL__supported
  | _ => CA_ParametersNR__simultaneousRxTxSUL__supported
  end.
Lemma CA_ParametersNR__simultaneousRxTxSUL__F1F2 : forall x : CA_ParametersNR__simultaneousRxTxSUL__Type, (CA_ParametersNR__simultaneousRxTxSUL__F1 x <= 0) /\ CA_ParametersNR__simultaneousRxTxSUL__F2 (CA_ParametersNR__simultaneousRxTxSUL__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__simultaneousRxTxSUL__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__simultaneousRxTxSUL__F1 (CA_ParametersNR__simultaneousRxTxSUL__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Type : Set :=
 | CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__supported
.
Definition CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__cond := (fun (_ : CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Type) => True).
Lemma CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__nat__helper.

Definition CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1 t :=
  match t with
  | CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__supported => 0
  end.
Definition CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F2 n :=
  match n with
  | 0 => CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__supported
  | _ => CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__supported
  end.
Lemma CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1F2 : forall x : CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Type, (CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1 x <= 0) /\ CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F2 (CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1 (CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Type : Set :=
 | CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__supported
.
Definition CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__cond := (fun (_ : CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Type) => True).
Lemma CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__nat__helper.

Definition CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1 t :=
  match t with
  | CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__supported => 0
  end.
Definition CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F2 n :=
  match n with
  | 0 => CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__supported
  | _ => CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__supported
  end.
Lemma CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1F2 : forall x : CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Type, (CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1 x <= 0) /\ CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F2 (CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1 (CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR__supportedNumberTAG__Type : Set :=
 | CA_ParametersNR__supportedNumberTAG__n2
 | CA_ParametersNR__supportedNumberTAG__n3
 | CA_ParametersNR__supportedNumberTAG__n4
.
Definition CA_ParametersNR__supportedNumberTAG__cond := (fun (_ : CA_ParametersNR__supportedNumberTAG__Type) => True).
Lemma CA_ParametersNR__supportedNumberTAG__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR__supportedNumberTAG__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR__supportedNumberTAG__nat__helper.

Definition CA_ParametersNR__supportedNumberTAG__F1 t :=
  match t with
  | CA_ParametersNR__supportedNumberTAG__n2 => 0
  | CA_ParametersNR__supportedNumberTAG__n3 => 1
  | CA_ParametersNR__supportedNumberTAG__n4 => 2
  end.
Definition CA_ParametersNR__supportedNumberTAG__F2 n :=
  match n with
  | 0 => CA_ParametersNR__supportedNumberTAG__n2
  | 1 => CA_ParametersNR__supportedNumberTAG__n3
  | 2 => CA_ParametersNR__supportedNumberTAG__n4
  | _ => CA_ParametersNR__supportedNumberTAG__n2
  end.
Lemma CA_ParametersNR__supportedNumberTAG__F1F2 : forall x : CA_ParametersNR__supportedNumberTAG__Type, (CA_ParametersNR__supportedNumberTAG__F1 x <= 2) /\ CA_ParametersNR__supportedNumberTAG__F2 (CA_ParametersNR__supportedNumberTAG__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR__supportedNumberTAG__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR__supportedNumberTAG__F1 (CA_ParametersNR__supportedNumberTAG__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR__Type : Set :=
  make__CA_ParametersNR__Type {
    CA_ParametersNR__dummy : option CA_ParametersNR__dummy__Type ;
    CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH : option CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Type ;
    CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH : option CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Type ;
    CA_ParametersNR__simultaneousRxTxInterBandCA : option CA_ParametersNR__simultaneousRxTxInterBandCA__Type ;
    CA_ParametersNR__simultaneousRxTxSUL : option CA_ParametersNR__simultaneousRxTxSUL__Type ;
    CA_ParametersNR__diffNumerologyAcrossPUCCH_Group : option CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Type ;
    CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS : option CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Type ;
    CA_ParametersNR__supportedNumberTAG : option CA_ParametersNR__supportedNumberTAG__Type ;
}.
Definition CA_ParametersNR__root_list : list seq_elem := (
 Opt CA_ParametersNR__dummy__Type CA_ParametersNR__dummy__cond ::
 Opt CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Type CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__cond ::
 Opt CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Type CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__cond ::
 Opt CA_ParametersNR__simultaneousRxTxInterBandCA__Type CA_ParametersNR__simultaneousRxTxInterBandCA__cond ::
 Opt CA_ParametersNR__simultaneousRxTxSUL__Type CA_ParametersNR__simultaneousRxTxSUL__cond ::
 Opt CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Type CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__cond ::
 Opt CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Type CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__cond ::
 Opt CA_ParametersNR__supportedNumberTAG__Type CA_ParametersNR__supportedNumberTAG__cond ::
 nil).
Definition CA_ParametersNR__ext_list : list typ := (
  nil).
Definition CA_ParametersNR__cond (z : CA_ParametersNR__Type) := 
(  opt_cond CA_ParametersNR__dummy__cond (CA_ParametersNR__dummy z) /\
  opt_cond CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__cond (CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH z) /\
  opt_cond CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__cond (CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH z) /\
  opt_cond CA_ParametersNR__simultaneousRxTxInterBandCA__cond (CA_ParametersNR__simultaneousRxTxInterBandCA z) /\
  opt_cond CA_ParametersNR__simultaneousRxTxSUL__cond (CA_ParametersNR__simultaneousRxTxSUL z) /\
  opt_cond CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__cond (CA_ParametersNR__diffNumerologyAcrossPUCCH_Group z) /\
  opt_cond CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__cond (CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS z) /\
  opt_cond CA_ParametersNR__supportedNumberTAG__cond (CA_ParametersNR__supportedNumberTAG z) /\
  True) /\ 
(  True).


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
Definition CA_ParametersNR__dummy__Format : T_Format CA_ParametersNR__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__dummy__nat__Format CA_ParametersNR__dummy__F1 CA_ParametersNR__dummy__F2 CA_ParametersNR__dummy__F1F2 CA_ParametersNR__dummy__F2F1.

Opaque CA_ParametersNR__dummy__cond CA_ParametersNR__dummy__Format.

Definition CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Format : T_Format CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__nat__Format CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1 CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F2 CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F1F2 CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__F2F1.

Opaque CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__cond CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Format.

Definition CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Format : T_Format CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__nat__Format CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1 CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F2 CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F1F2 CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__F2F1.

Opaque CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__cond CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Format.

Definition CA_ParametersNR__simultaneousRxTxInterBandCA__Format : T_Format CA_ParametersNR__simultaneousRxTxInterBandCA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__simultaneousRxTxInterBandCA__nat__Format CA_ParametersNR__simultaneousRxTxInterBandCA__F1 CA_ParametersNR__simultaneousRxTxInterBandCA__F2 CA_ParametersNR__simultaneousRxTxInterBandCA__F1F2 CA_ParametersNR__simultaneousRxTxInterBandCA__F2F1.

Opaque CA_ParametersNR__simultaneousRxTxInterBandCA__cond CA_ParametersNR__simultaneousRxTxInterBandCA__Format.

Definition CA_ParametersNR__simultaneousRxTxSUL__Format : T_Format CA_ParametersNR__simultaneousRxTxSUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__simultaneousRxTxSUL__nat__Format CA_ParametersNR__simultaneousRxTxSUL__F1 CA_ParametersNR__simultaneousRxTxSUL__F2 CA_ParametersNR__simultaneousRxTxSUL__F1F2 CA_ParametersNR__simultaneousRxTxSUL__F2F1.

Opaque CA_ParametersNR__simultaneousRxTxSUL__cond CA_ParametersNR__simultaneousRxTxSUL__Format.

Definition CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Format : T_Format CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__nat__Format CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1 CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F2 CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F1F2 CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__F2F1.

Opaque CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__cond CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Format.

Definition CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Format : T_Format CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__nat__Format CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1 CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F2 CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F1F2 CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__F2F1.

Opaque CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__cond CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Format.

Definition CA_ParametersNR__supportedNumberTAG__Format : T_Format CA_ParametersNR__supportedNumberTAG__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR__supportedNumberTAG__nat__Format CA_ParametersNR__supportedNumberTAG__F1 CA_ParametersNR__supportedNumberTAG__F2 CA_ParametersNR__supportedNumberTAG__F1F2 CA_ParametersNR__supportedNumberTAG__F2F1.

Opaque CA_ParametersNR__supportedNumberTAG__cond CA_ParametersNR__supportedNumberTAG__Format.


Definition CA_ParametersNR__root_Format_Type := Eval cbn in seq_format_prod CA_ParametersNR__root_list.
Definition CA_ParametersNR__root_Format_list : CA_ParametersNR__root_Format_Type :=
  (CA_ParametersNR__dummy__Format, (CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH__Format, (CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH__Format, (CA_ParametersNR__simultaneousRxTxInterBandCA__Format, (CA_ParametersNR__simultaneousRxTxSUL__Format, (CA_ParametersNR__diffNumerologyAcrossPUCCH_Group__Format, (CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS__Format, (CA_ParametersNR__supportedNumberTAG__Format, unit_format)))))))).

Definition CA_ParametersNR__ext_Format_Type := Eval cbn in get_formats CA_ParametersNR__ext_list.
Definition CA_ParametersNR__ext_Format_list : CA_ParametersNR__ext_Format_Type :=
  unit__Format.

Definition CA_ParametersNR__list_type : Set := (seq_type CA_ParametersNR__root_list) * (seq_ext_type CA_ParametersNR__ext_list).
Definition CA_ParametersNR__list_cond (z : CA_ParametersNR__list_type) : Prop :=
        (seq_cond CA_ParametersNR__root_list (fst z)) /\ (seq_ext_cond CA_ParametersNR__ext_list (snd z)).
Definition CA_ParametersNR__list_format : T_Format CA_ParametersNR__list_type CA_ParametersNR__list_cond :=
 (* Eval compute in *) seq_ext_format CA_ParametersNR__root_list CA_ParametersNR__root_Format_list CA_ParametersNR__ext_list CA_ParametersNR__ext_Format_list.

Opaque CA_ParametersNR__list_format.
Definition CA_ParametersNR__F1 (z : CA_ParametersNR__Type) : CA_ParametersNR__list_type :=
  (((CA_ParametersNR__dummy z, (CA_ParametersNR__parallelTxSRS_PUCCH_PUSCH z, (CA_ParametersNR__parallelTxPRACH_SRS_PUCCH_PUSCH z, (CA_ParametersNR__simultaneousRxTxInterBandCA z, (CA_ParametersNR__simultaneousRxTxSUL z, (CA_ParametersNR__diffNumerologyAcrossPUCCH_Group z, (CA_ParametersNR__diffNumerologyWithinPUCCH_GroupSmallerSCS z, (CA_ParametersNR__supportedNumberTAG z, tt))))))))), (
tt)).
Definition CA_ParametersNR__F2 (y : CA_ParametersNR__list_type) : CA_ParametersNR__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), _)=>
    make__CA_ParametersNR__Type j0 j1 j2 j3 j4 j5 j6 j7
  end.
Definition CA_ParametersNR__helper1 : (forall a : CA_ParametersNR__Type, CA_ParametersNR__cond a -> CA_ParametersNR__list_cond (CA_ParametersNR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CA_ParametersNR__helper2 : (forall a : CA_ParametersNR__Type, CA_ParametersNR__F2 (CA_ParametersNR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CA_ParametersNR__helper3 : (forall b : CA_ParametersNR__list_type, CA_ParametersNR__list_cond b -> CA_ParametersNR__cond (CA_ParametersNR__F2 b) /\ CA_ParametersNR__F1 (CA_ParametersNR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CA_ParametersNR__cond, CA_ParametersNR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CA_ParametersNR__Format : T_Format CA_ParametersNR__Type CA_ParametersNR__cond :=
 proj2_format CA_ParametersNR__cond CA_ParametersNR__list_format  CA_ParametersNR__F1 CA_ParametersNR__F2 CA_ParametersNR__helper1 CA_ParametersNR__helper2 CA_ParametersNR__helper3.

Opaque CA_ParametersNR__cond CA_ParametersNR__Format.

