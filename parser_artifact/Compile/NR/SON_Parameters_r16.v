Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SON_Parameters_r16__rach_Report_r16__Type : Set :=
 | SON_Parameters_r16__rach_Report_r16__supported
.
Definition SON_Parameters_r16__rach_Report_r16__cond := (fun (_ : SON_Parameters_r16__rach_Report_r16__Type) => True).
Lemma SON_Parameters_r16__rach_Report_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__rach_Report_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__rach_Report_r16__nat__helper.

Definition SON_Parameters_r16__rach_Report_r16__F1 t :=
  match t with
  | SON_Parameters_r16__rach_Report_r16__supported => 0
  end.
Definition SON_Parameters_r16__rach_Report_r16__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__rach_Report_r16__supported
  | _ => SON_Parameters_r16__rach_Report_r16__supported
  end.
Lemma SON_Parameters_r16__rach_Report_r16__F1F2 : forall x : SON_Parameters_r16__rach_Report_r16__Type, (SON_Parameters_r16__rach_Report_r16__F1 x <= 0) /\ SON_Parameters_r16__rach_Report_r16__F2 (SON_Parameters_r16__rach_Report_r16__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__rach_Report_r16__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__rach_Report_r16__F1 (SON_Parameters_r16__rach_Report_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SON_Parameters_r16__ext0O__rlfReportCHO_r17__Type : Set :=
 | SON_Parameters_r16__ext0O__rlfReportCHO_r17__supported
.
Definition SON_Parameters_r16__ext0O__rlfReportCHO_r17__cond := (fun (_ : SON_Parameters_r16__ext0O__rlfReportCHO_r17__Type) => True).
Lemma SON_Parameters_r16__ext0O__rlfReportCHO_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__ext0O__rlfReportCHO_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__ext0O__rlfReportCHO_r17__nat__helper.

Definition SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1 t :=
  match t with
  | SON_Parameters_r16__ext0O__rlfReportCHO_r17__supported => 0
  end.
Definition SON_Parameters_r16__ext0O__rlfReportCHO_r17__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__ext0O__rlfReportCHO_r17__supported
  | _ => SON_Parameters_r16__ext0O__rlfReportCHO_r17__supported
  end.
Lemma SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1F2 : forall x : SON_Parameters_r16__ext0O__rlfReportCHO_r17__Type, (SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1 x <= 0) /\ SON_Parameters_r16__ext0O__rlfReportCHO_r17__F2 (SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__ext0O__rlfReportCHO_r17__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1 (SON_Parameters_r16__ext0O__rlfReportCHO_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Type : Set :=
 | SON_Parameters_r16__ext0O__rlfReportDAPS_r17__supported
.
Definition SON_Parameters_r16__ext0O__rlfReportDAPS_r17__cond := (fun (_ : SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Type) => True).
Lemma SON_Parameters_r16__ext0O__rlfReportDAPS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__ext0O__rlfReportDAPS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__ext0O__rlfReportDAPS_r17__nat__helper.

Definition SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1 t :=
  match t with
  | SON_Parameters_r16__ext0O__rlfReportDAPS_r17__supported => 0
  end.
Definition SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__ext0O__rlfReportDAPS_r17__supported
  | _ => SON_Parameters_r16__ext0O__rlfReportDAPS_r17__supported
  end.
Lemma SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1F2 : forall x : SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Type, (SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1 x <= 0) /\ SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F2 (SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1 (SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SON_Parameters_r16__ext0O__success_HO_Report_r17__Type : Set :=
 | SON_Parameters_r16__ext0O__success_HO_Report_r17__supported
.
Definition SON_Parameters_r16__ext0O__success_HO_Report_r17__cond := (fun (_ : SON_Parameters_r16__ext0O__success_HO_Report_r17__Type) => True).
Lemma SON_Parameters_r16__ext0O__success_HO_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__ext0O__success_HO_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__ext0O__success_HO_Report_r17__nat__helper.

Definition SON_Parameters_r16__ext0O__success_HO_Report_r17__F1 t :=
  match t with
  | SON_Parameters_r16__ext0O__success_HO_Report_r17__supported => 0
  end.
Definition SON_Parameters_r16__ext0O__success_HO_Report_r17__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__ext0O__success_HO_Report_r17__supported
  | _ => SON_Parameters_r16__ext0O__success_HO_Report_r17__supported
  end.
Lemma SON_Parameters_r16__ext0O__success_HO_Report_r17__F1F2 : forall x : SON_Parameters_r16__ext0O__success_HO_Report_r17__Type, (SON_Parameters_r16__ext0O__success_HO_Report_r17__F1 x <= 0) /\ SON_Parameters_r16__ext0O__success_HO_Report_r17__F2 (SON_Parameters_r16__ext0O__success_HO_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__ext0O__success_HO_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__ext0O__success_HO_Report_r17__F1 (SON_Parameters_r16__ext0O__success_HO_Report_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Type : Set :=
 | SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__supported
.
Definition SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__cond := (fun (_ : SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Type) => True).
Lemma SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__nat__helper.

Definition SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1 t :=
  match t with
  | SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__supported => 0
  end.
Definition SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__supported
  | _ => SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__supported
  end.
Lemma SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1F2 : forall x : SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Type, (SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1 x <= 0) /\ SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F2 (SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1 (SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Type : Set :=
 | SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__supported
.
Definition SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__cond := (fun (_ : SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Type) => True).
Lemma SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__nat__helper.

Definition SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1 t :=
  match t with
  | SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__supported => 0
  end.
Definition SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__supported
  | _ => SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__supported
  end.
Lemma SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1F2 : forall x : SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Type, (SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1 x <= 0) /\ SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F2 (SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1 (SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Type : Set :=
 | SON_Parameters_r16__ext0O__onDemandSI_Report_r17__supported
.
Definition SON_Parameters_r16__ext0O__onDemandSI_Report_r17__cond := (fun (_ : SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Type) => True).
Lemma SON_Parameters_r16__ext0O__onDemandSI_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SON_Parameters_r16__ext0O__onDemandSI_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SON_Parameters_r16__ext0O__onDemandSI_Report_r17__nat__helper.

Definition SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1 t :=
  match t with
  | SON_Parameters_r16__ext0O__onDemandSI_Report_r17__supported => 0
  end.
Definition SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F2 n :=
  match n with
  | 0 => SON_Parameters_r16__ext0O__onDemandSI_Report_r17__supported
  | _ => SON_Parameters_r16__ext0O__onDemandSI_Report_r17__supported
  end.
Lemma SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1F2 : forall x : SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Type, (SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1 x <= 0) /\ SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F2 (SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1 (SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F2 y) = y. enum_solve H y. Qed.

Record SON_Parameters_r16__ext0O__Type : Set :=
  make__SON_Parameters_r16__ext0O__Type {
    SON_Parameters_r16__ext0O__rlfReportCHO_r17 : option SON_Parameters_r16__ext0O__rlfReportCHO_r17__Type ;
    SON_Parameters_r16__ext0O__rlfReportDAPS_r17 : option SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Type ;
    SON_Parameters_r16__ext0O__success_HO_Report_r17 : option SON_Parameters_r16__ext0O__success_HO_Report_r17__Type ;
    SON_Parameters_r16__ext0O__twoStepRACH_Report_r17 : option SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Type ;
    SON_Parameters_r16__ext0O__pscell_MHI_Report_r17 : option SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Type ;
    SON_Parameters_r16__ext0O__onDemandSI_Report_r17 : option SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Type ;
}.
Definition SON_Parameters_r16__ext0O__list := (
 Opt SON_Parameters_r16__ext0O__rlfReportCHO_r17__Type SON_Parameters_r16__ext0O__rlfReportCHO_r17__cond ::
 Opt SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Type SON_Parameters_r16__ext0O__rlfReportDAPS_r17__cond ::
 Opt SON_Parameters_r16__ext0O__success_HO_Report_r17__Type SON_Parameters_r16__ext0O__success_HO_Report_r17__cond ::
 Opt SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Type SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__cond ::
 Opt SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Type SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__cond ::
 Opt SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Type SON_Parameters_r16__ext0O__onDemandSI_Report_r17__cond ::
 nil).
Definition SON_Parameters_r16__ext0O__cond z := 
  opt_cond SON_Parameters_r16__ext0O__rlfReportCHO_r17__cond (SON_Parameters_r16__ext0O__rlfReportCHO_r17 z) /\
  opt_cond SON_Parameters_r16__ext0O__rlfReportDAPS_r17__cond (SON_Parameters_r16__ext0O__rlfReportDAPS_r17 z) /\
  opt_cond SON_Parameters_r16__ext0O__success_HO_Report_r17__cond (SON_Parameters_r16__ext0O__success_HO_Report_r17 z) /\
  opt_cond SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__cond (SON_Parameters_r16__ext0O__twoStepRACH_Report_r17 z) /\
  opt_cond SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__cond (SON_Parameters_r16__ext0O__pscell_MHI_Report_r17 z) /\
  opt_cond SON_Parameters_r16__ext0O__onDemandSI_Report_r17__cond (SON_Parameters_r16__ext0O__onDemandSI_Report_r17 z) /\
  True.

Definition SON_Parameters_r16__ext0__Type := SON_Parameters_r16__ext0O__Type.
Definition SON_Parameters_r16__ext0__cond := SON_Parameters_r16__ext0O__cond.

Record SON_Parameters_r16__Type : Set :=
  make__SON_Parameters_r16__Type {
    SON_Parameters_r16__rach_Report_r16 : option SON_Parameters_r16__rach_Report_r16__Type ;
    SON_Parameters_r16__ext0 : option SON_Parameters_r16__ext0__Type ;
}.
Definition SON_Parameters_r16__root_list : list seq_elem := (
 Opt SON_Parameters_r16__rach_Report_r16__Type SON_Parameters_r16__rach_Report_r16__cond ::
 nil).
Definition SON_Parameters_r16__ext_list : list typ := (
  typ_cons SON_Parameters_r16__ext0__Type SON_Parameters_r16__ext0__cond ::
  nil).
Definition SON_Parameters_r16__cond (z : SON_Parameters_r16__Type) := 
(  opt_cond SON_Parameters_r16__rach_Report_r16__cond (SON_Parameters_r16__rach_Report_r16 z) /\
  True) /\ 
(  opt_cond SON_Parameters_r16__ext0__cond (SON_Parameters_r16__ext0 z) /\
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
Definition SON_Parameters_r16__rach_Report_r16__Format : T_Format SON_Parameters_r16__rach_Report_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__rach_Report_r16__nat__Format SON_Parameters_r16__rach_Report_r16__F1 SON_Parameters_r16__rach_Report_r16__F2 SON_Parameters_r16__rach_Report_r16__F1F2 SON_Parameters_r16__rach_Report_r16__F2F1.

Opaque SON_Parameters_r16__rach_Report_r16__cond SON_Parameters_r16__rach_Report_r16__Format.

Definition SON_Parameters_r16__ext0O__rlfReportCHO_r17__Format : T_Format SON_Parameters_r16__ext0O__rlfReportCHO_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__ext0O__rlfReportCHO_r17__nat__Format SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1 SON_Parameters_r16__ext0O__rlfReportCHO_r17__F2 SON_Parameters_r16__ext0O__rlfReportCHO_r17__F1F2 SON_Parameters_r16__ext0O__rlfReportCHO_r17__F2F1.

Opaque SON_Parameters_r16__ext0O__rlfReportCHO_r17__cond SON_Parameters_r16__ext0O__rlfReportCHO_r17__Format.

Definition SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Format : T_Format SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__ext0O__rlfReportDAPS_r17__nat__Format SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1 SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F2 SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F1F2 SON_Parameters_r16__ext0O__rlfReportDAPS_r17__F2F1.

Opaque SON_Parameters_r16__ext0O__rlfReportDAPS_r17__cond SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Format.

Definition SON_Parameters_r16__ext0O__success_HO_Report_r17__Format : T_Format SON_Parameters_r16__ext0O__success_HO_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__ext0O__success_HO_Report_r17__nat__Format SON_Parameters_r16__ext0O__success_HO_Report_r17__F1 SON_Parameters_r16__ext0O__success_HO_Report_r17__F2 SON_Parameters_r16__ext0O__success_HO_Report_r17__F1F2 SON_Parameters_r16__ext0O__success_HO_Report_r17__F2F1.

Opaque SON_Parameters_r16__ext0O__success_HO_Report_r17__cond SON_Parameters_r16__ext0O__success_HO_Report_r17__Format.

Definition SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Format : T_Format SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__nat__Format SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1 SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F2 SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F1F2 SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__F2F1.

Opaque SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__cond SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Format.

Definition SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Format : T_Format SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__nat__Format SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1 SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F2 SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F1F2 SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__F2F1.

Opaque SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__cond SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Format.

Definition SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Format : T_Format SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SON_Parameters_r16__ext0O__onDemandSI_Report_r17__nat__Format SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1 SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F2 SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F1F2 SON_Parameters_r16__ext0O__onDemandSI_Report_r17__F2F1.

Opaque SON_Parameters_r16__ext0O__onDemandSI_Report_r17__cond SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Format.


Definition SON_Parameters_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SON_Parameters_r16__ext0O__list.
Definition SON_Parameters_r16__ext0O__Format_list : SON_Parameters_r16__ext0O__Format_Type :=
  (SON_Parameters_r16__ext0O__rlfReportCHO_r17__Format, (SON_Parameters_r16__ext0O__rlfReportDAPS_r17__Format, (SON_Parameters_r16__ext0O__success_HO_Report_r17__Format, (SON_Parameters_r16__ext0O__twoStepRACH_Report_r17__Format, (SON_Parameters_r16__ext0O__pscell_MHI_Report_r17__Format, (SON_Parameters_r16__ext0O__onDemandSI_Report_r17__Format, unit_format)))))).
Definition SON_Parameters_r16__ext0O__list__Format := (*Eval compute in *) seq_format SON_Parameters_r16__ext0O__list SON_Parameters_r16__ext0O__Format_list.
Definition SON_Parameters_r16__ext0O__F1 z :=
  (SON_Parameters_r16__ext0O__rlfReportCHO_r17 z, (SON_Parameters_r16__ext0O__rlfReportDAPS_r17 z, (SON_Parameters_r16__ext0O__success_HO_Report_r17 z, (SON_Parameters_r16__ext0O__twoStepRACH_Report_r17 z, (SON_Parameters_r16__ext0O__pscell_MHI_Report_r17 z, (SON_Parameters_r16__ext0O__onDemandSI_Report_r17 z, tt)))))).
Definition SON_Parameters_r16__ext0O__F2 (y : seq_type SON_Parameters_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__SON_Parameters_r16__ext0O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma SON_Parameters_r16__ext0O__F1F2_cond (z : SON_Parameters_r16__ext0O__Type)
  : SON_Parameters_r16__ext0O__cond z ->
  (seq_cond SON_Parameters_r16__ext0O__list (SON_Parameters_r16__ext0O__F1 z)).
intro H. unfold SON_Parameters_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SON_Parameters_r16__ext0O__F1F2_cond2 (z : SON_Parameters_r16__ext0O__Type)
 : SON_Parameters_r16__ext0O__F2 (SON_Parameters_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SON_Parameters_r16__ext0O__F2F1_cond (y : seq_type SON_Parameters_r16__ext0O__list)
  : seq_cond SON_Parameters_r16__ext0O__list y ->
 (SON_Parameters_r16__ext0O__cond (SON_Parameters_r16__ext0O__F2 y)) /\  SON_Parameters_r16__ext0O__F1 (SON_Parameters_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SON_Parameters_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SON_Parameters_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SON_Parameters_r16__ext0O__Format : T_Format SON_Parameters_r16__ext0O__Type SON_Parameters_r16__ext0O__cond :=
        proj2_format  SON_Parameters_r16__ext0O__cond SON_Parameters_r16__ext0O__list__Format
    SON_Parameters_r16__ext0O__F1 SON_Parameters_r16__ext0O__F2 SON_Parameters_r16__ext0O__F1F2_cond  SON_Parameters_r16__ext0O__F1F2_cond2 SON_Parameters_r16__ext0O__F2F1_cond.
Opaque SON_Parameters_r16__ext0O__cond SON_Parameters_r16__ext0O__Format.

Definition SON_Parameters_r16__ext0__check_all_none (b : SON_Parameters_r16__ext0O__Type) : bool :=
match b with 
  | make__SON_Parameters_r16__ext0O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition SON_Parameters_r16__ext0__Format : T_Format SON_Parameters_r16__ext0__Type SON_Parameters_r16__ext0__cond :=
  restrict_add_format SON_Parameters_r16__ext0__check_all_none SON_Parameters_r16__ext0O__Format.

Opaque SON_Parameters_r16__ext0__cond SON_Parameters_r16__ext0__Format.


Definition SON_Parameters_r16__root_Format_Type := Eval cbn in seq_format_prod SON_Parameters_r16__root_list.
Definition SON_Parameters_r16__root_Format_list : SON_Parameters_r16__root_Format_Type :=
  (SON_Parameters_r16__rach_Report_r16__Format, unit_format).

Definition SON_Parameters_r16__ext_Format_Type := Eval cbn in get_formats SON_Parameters_r16__ext_list.
Definition SON_Parameters_r16__ext_Format_list : SON_Parameters_r16__ext_Format_Type :=
  (SON_Parameters_r16__ext0__Format, unit__Format).

Definition SON_Parameters_r16__list_type : Set := (seq_type SON_Parameters_r16__root_list) * (seq_ext_type SON_Parameters_r16__ext_list).
Definition SON_Parameters_r16__list_cond (z : SON_Parameters_r16__list_type) : Prop :=
        (seq_cond SON_Parameters_r16__root_list (fst z)) /\ (seq_ext_cond SON_Parameters_r16__ext_list (snd z)).
Definition SON_Parameters_r16__list_format : T_Format SON_Parameters_r16__list_type SON_Parameters_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SON_Parameters_r16__root_list SON_Parameters_r16__root_Format_list SON_Parameters_r16__ext_list SON_Parameters_r16__ext_Format_list.

Opaque SON_Parameters_r16__list_format.
Definition SON_Parameters_r16__F1 (z : SON_Parameters_r16__Type) : SON_Parameters_r16__list_type :=
  (((SON_Parameters_r16__rach_Report_r16 z, tt)), (
(SON_Parameters_r16__ext0 z, tt))).
Definition SON_Parameters_r16__F2 (y : SON_Parameters_r16__list_type) : SON_Parameters_r16__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__SON_Parameters_r16__Type j0 i0
  end.
Definition SON_Parameters_r16__helper1 : (forall a : SON_Parameters_r16__Type, SON_Parameters_r16__cond a -> SON_Parameters_r16__list_cond (SON_Parameters_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SON_Parameters_r16__helper2 : (forall a : SON_Parameters_r16__Type, SON_Parameters_r16__F2 (SON_Parameters_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SON_Parameters_r16__helper3 : (forall b : SON_Parameters_r16__list_type, SON_Parameters_r16__list_cond b -> SON_Parameters_r16__cond (SON_Parameters_r16__F2 b) /\ SON_Parameters_r16__F1 (SON_Parameters_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SON_Parameters_r16__cond, SON_Parameters_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SON_Parameters_r16__Format : T_Format SON_Parameters_r16__Type SON_Parameters_r16__cond :=
 proj2_format SON_Parameters_r16__cond SON_Parameters_r16__list_format  SON_Parameters_r16__F1 SON_Parameters_r16__F2 SON_Parameters_r16__helper1 SON_Parameters_r16__helper2 SON_Parameters_r16__helper3.

Opaque SON_Parameters_r16__cond SON_Parameters_r16__Format.

