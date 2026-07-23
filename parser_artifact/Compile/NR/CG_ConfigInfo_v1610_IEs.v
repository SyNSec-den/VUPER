Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.DRX_Info2.

Opaque DRX_Info2__cond DRX_Info2__Format.

Inductive CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Type : Set :=
 | CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__true
.
Definition CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__cond := (fun (_ : CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Type) => True).
Lemma CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__nat__helper.

Definition CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1 t :=
  match t with
  | CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__true => 0
  end.
Definition CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F2 n :=
  match n with
  | 0 => CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__true
  | _ => CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__true
  end.
Lemma CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1F2 : forall x : CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Type, (CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1 x <= 0) /\ CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F2 (CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1 x) = x. imp_solve. Qed.
Lemma CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F2F1 : forall (y : nat) (H : y <= 0), CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1 (CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F2 y) = y. enum_solve H y. Qed.

Inductive CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Type : Set :=
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__scg_lbtFailure_r16
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__beamFailureRecoveryFailure_r16
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__t312_Expiry_r16
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__bh_RLF_r16
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__beamFailure_r17
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare3
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare2
 | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare1
.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__cond := (fun (_ : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Type) => True).
Lemma CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__nat__helper.

Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1 t :=
  match t with
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__scg_lbtFailure_r16 => 0
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__beamFailureRecoveryFailure_r16 => 1
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__t312_Expiry_r16 => 2
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__bh_RLF_r16 => 3
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__beamFailure_r17 => 4
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare3 => 5
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare2 => 6
  | CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare1 => 7
  end.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F2 n :=
  match n with
  | 0 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__scg_lbtFailure_r16
  | 1 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__beamFailureRecoveryFailure_r16
  | 2 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__t312_Expiry_r16
  | 3 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__bh_RLF_r16
  | 4 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__beamFailure_r17
  | 5 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare3
  | 6 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare2
  | 7 => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__spare1
  | _ => CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__scg_lbtFailure_r16
  end.
Lemma CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1F2 : forall x : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Type, (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1 x <= 7) /\ CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F2 (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1 x) = x. imp_solve. Qed.
Lemma CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F2F1 : forall (y : nat) (H : y <= 7), CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1 (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F2 y) = y. enum_solve H y. Qed.

Record CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type : Set :=
  make__CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type {
    CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16 : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Type ;
    CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__measResultSCG_r16 : octet_string ;
}.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list := (
 Nor CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Type CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond z := 
  CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__cond (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__measResultSCG_r16 z) /\
  True.

Inductive CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Type : Set :=
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__scg_lbtFailure_r16
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__beamFailureRecoveryFailure_r16
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__t312_Expiry_r16
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare5
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare4
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare3
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare2
 | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare1
.
Definition CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__cond := (fun (_ : CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Type) => True).
Lemma CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__nat__helper.

Definition CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1 t :=
  match t with
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__scg_lbtFailure_r16 => 0
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__beamFailureRecoveryFailure_r16 => 1
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__t312_Expiry_r16 => 2
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare5 => 3
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare4 => 4
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare3 => 5
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare2 => 6
  | CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare1 => 7
  end.
Definition CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F2 n :=
  match n with
  | 0 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__scg_lbtFailure_r16
  | 1 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__beamFailureRecoveryFailure_r16
  | 2 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__t312_Expiry_r16
  | 3 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare5
  | 4 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare4
  | 5 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare3
  | 6 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare2
  | 7 => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__spare1
  | _ => CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__scg_lbtFailure_r16
  end.
Lemma CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1F2 : forall x : CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Type, (CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1 x <= 7) /\ CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F2 (CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1 x) = x. imp_solve. Qed.
Lemma CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F2F1 : forall (y : nat) (H : y <= 7), CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1 (CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F2 y) = y. enum_solve H y. Qed.

Record CG_ConfigInfo_v1610_IEs__dummy1__Type : Set :=
  make__CG_ConfigInfo_v1610_IEs__dummy1__Type {
    CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16 : CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Type ;
    CG_ConfigInfo_v1610_IEs__dummy1__measResultSCG_EUTRA_r16 : octet_string ;
}.
Definition CG_ConfigInfo_v1610_IEs__dummy1__list := (
 Nor CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Type CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CG_ConfigInfo_v1610_IEs__dummy1__cond z := 
  CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__cond (CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1610_IEs__dummy1__measResultSCG_EUTRA_r16 z) /\
  True.

Require Import NR.CG_ConfigInfo_v1620_IEs.

Opaque CG_ConfigInfo_v1620_IEs__cond CG_ConfigInfo_v1620_IEs__Format.

Record CG_ConfigInfo_v1610_IEs__Type : Set :=
  make__CG_ConfigInfo_v1610_IEs__Type {
    CG_ConfigInfo_v1610_IEs__drx_InfoMCG2 : option DRX_Info2__Type ;
    CG_ConfigInfo_v1610_IEs__alignedDRX_Indication : option CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Type ;
    CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16 : option CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type ;
    CG_ConfigInfo_v1610_IEs__dummy1 : option CG_ConfigInfo_v1610_IEs__dummy1__Type ;
    CG_ConfigInfo_v1610_IEs__sidelinkUEInformationNR_r16 : option octet_string ;
    CG_ConfigInfo_v1610_IEs__sidelinkUEInformationEUTRA_r16 : option octet_string ;
    CG_ConfigInfo_v1610_IEs__nonCriticalExtension : option CG_ConfigInfo_v1620_IEs__Type ;
}.
Definition CG_ConfigInfo_v1610_IEs__list := (
 Opt DRX_Info2__Type DRX_Info2__cond ::
 Opt CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Type CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__cond ::
 Opt CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond ::
 Opt CG_ConfigInfo_v1610_IEs__dummy1__Type CG_ConfigInfo_v1610_IEs__dummy1__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt CG_ConfigInfo_v1620_IEs__Type CG_ConfigInfo_v1620_IEs__cond ::
 nil).
Definition CG_ConfigInfo_v1610_IEs__cond z := 
  opt_cond DRX_Info2__cond (CG_ConfigInfo_v1610_IEs__drx_InfoMCG2 z) /\
  opt_cond CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__cond (CG_ConfigInfo_v1610_IEs__alignedDRX_Indication z) /\
  opt_cond CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16 z) /\
  opt_cond CG_ConfigInfo_v1610_IEs__dummy1__cond (CG_ConfigInfo_v1610_IEs__dummy1 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1610_IEs__sidelinkUEInformationNR_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1610_IEs__sidelinkUEInformationEUTRA_r16 z) /\
  opt_cond CG_ConfigInfo_v1620_IEs__cond (CG_ConfigInfo_v1610_IEs__nonCriticalExtension z) /\
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
Definition CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Format : T_Format CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__nat__Format CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1 CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F2 CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F1F2 CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__F2F1.

Opaque CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__cond CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Format.

Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Format : T_Format CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__nat__Format CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F2 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F1F2 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__F2F1.

Opaque CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__cond CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Format.


Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format_list : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format_Type :=
  (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16__Format, (octet_string_nc__Format, unit_format)).
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format_list.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1 z :=
  (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__failureType_r16 z, (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__measResultSCG_r16 z, tt)).
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2 (y : seq_type CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type i0 i1
  end.
Lemma CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1F2_cond (z : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type)
  : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond z ->
  (seq_cond CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1 z)).
intro H. unfold CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1F2_cond2 (z : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type)
 : CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2 (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2F1_cond (y : seq_type CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list)
  : seq_cond CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list y ->
 (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2 y)) /\  CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1 (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format : T_Format CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Type CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond :=
        proj2_format  CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__list__Format
    CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1F2_cond  CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F1F2_cond2 CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__F2F1_cond.
Opaque CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__cond CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format.

Definition CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Format : T_Format CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__nat__Format CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1 CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F2 CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F1F2 CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__F2F1.

Opaque CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__cond CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Format.


Definition CG_ConfigInfo_v1610_IEs__dummy1__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1610_IEs__dummy1__list.
Definition CG_ConfigInfo_v1610_IEs__dummy1__Format_list : CG_ConfigInfo_v1610_IEs__dummy1__Format_Type :=
  (CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16__Format, (octet_string_nc__Format, unit_format)).
Definition CG_ConfigInfo_v1610_IEs__dummy1__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1610_IEs__dummy1__list CG_ConfigInfo_v1610_IEs__dummy1__Format_list.
Definition CG_ConfigInfo_v1610_IEs__dummy1__F1 z :=
  (CG_ConfigInfo_v1610_IEs__dummy1__failureTypeEUTRA_r16 z, (CG_ConfigInfo_v1610_IEs__dummy1__measResultSCG_EUTRA_r16 z, tt)).
Definition CG_ConfigInfo_v1610_IEs__dummy1__F2 (y : seq_type CG_ConfigInfo_v1610_IEs__dummy1__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_ConfigInfo_v1610_IEs__dummy1__Type i0 i1
  end.
Lemma CG_ConfigInfo_v1610_IEs__dummy1__F1F2_cond (z : CG_ConfigInfo_v1610_IEs__dummy1__Type)
  : CG_ConfigInfo_v1610_IEs__dummy1__cond z ->
  (seq_cond CG_ConfigInfo_v1610_IEs__dummy1__list (CG_ConfigInfo_v1610_IEs__dummy1__F1 z)).
intro H. unfold CG_ConfigInfo_v1610_IEs__dummy1__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1610_IEs__dummy1__F1F2_cond2 (z : CG_ConfigInfo_v1610_IEs__dummy1__Type)
 : CG_ConfigInfo_v1610_IEs__dummy1__F2 (CG_ConfigInfo_v1610_IEs__dummy1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1610_IEs__dummy1__F2F1_cond (y : seq_type CG_ConfigInfo_v1610_IEs__dummy1__list)
  : seq_cond CG_ConfigInfo_v1610_IEs__dummy1__list y ->
 (CG_ConfigInfo_v1610_IEs__dummy1__cond (CG_ConfigInfo_v1610_IEs__dummy1__F2 y)) /\  CG_ConfigInfo_v1610_IEs__dummy1__F1 (CG_ConfigInfo_v1610_IEs__dummy1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1610_IEs__dummy1__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1610_IEs__dummy1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1610_IEs__dummy1__Format : T_Format CG_ConfigInfo_v1610_IEs__dummy1__Type CG_ConfigInfo_v1610_IEs__dummy1__cond :=
        proj2_format  CG_ConfigInfo_v1610_IEs__dummy1__cond CG_ConfigInfo_v1610_IEs__dummy1__list__Format
    CG_ConfigInfo_v1610_IEs__dummy1__F1 CG_ConfigInfo_v1610_IEs__dummy1__F2 CG_ConfigInfo_v1610_IEs__dummy1__F1F2_cond  CG_ConfigInfo_v1610_IEs__dummy1__F1F2_cond2 CG_ConfigInfo_v1610_IEs__dummy1__F2F1_cond.
Opaque CG_ConfigInfo_v1610_IEs__dummy1__cond CG_ConfigInfo_v1610_IEs__dummy1__Format.


Definition CG_ConfigInfo_v1610_IEs__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1610_IEs__list.
Definition CG_ConfigInfo_v1610_IEs__Format_list : CG_ConfigInfo_v1610_IEs__Format_Type :=
  (DRX_Info2__Format, (CG_ConfigInfo_v1610_IEs__alignedDRX_Indication__Format, (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16__Format, (CG_ConfigInfo_v1610_IEs__dummy1__Format, (octet_string_nc__Format, (octet_string_nc__Format, (CG_ConfigInfo_v1620_IEs__Format, unit_format))))))).
Definition CG_ConfigInfo_v1610_IEs__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1610_IEs__list CG_ConfigInfo_v1610_IEs__Format_list.
Definition CG_ConfigInfo_v1610_IEs__F1 z :=
  (CG_ConfigInfo_v1610_IEs__drx_InfoMCG2 z, (CG_ConfigInfo_v1610_IEs__alignedDRX_Indication z, (CG_ConfigInfo_v1610_IEs__scgFailureInfo_r16 z, (CG_ConfigInfo_v1610_IEs__dummy1 z, (CG_ConfigInfo_v1610_IEs__sidelinkUEInformationNR_r16 z, (CG_ConfigInfo_v1610_IEs__sidelinkUEInformationEUTRA_r16 z, (CG_ConfigInfo_v1610_IEs__nonCriticalExtension z, tt))))))).
Definition CG_ConfigInfo_v1610_IEs__F2 (y : seq_type CG_ConfigInfo_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__CG_ConfigInfo_v1610_IEs__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma CG_ConfigInfo_v1610_IEs__F1F2_cond (z : CG_ConfigInfo_v1610_IEs__Type)
  : CG_ConfigInfo_v1610_IEs__cond z ->
  (seq_cond CG_ConfigInfo_v1610_IEs__list (CG_ConfigInfo_v1610_IEs__F1 z)).
intro H. unfold CG_ConfigInfo_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1610_IEs__F1F2_cond2 (z : CG_ConfigInfo_v1610_IEs__Type)
 : CG_ConfigInfo_v1610_IEs__F2 (CG_ConfigInfo_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1610_IEs__F2F1_cond (y : seq_type CG_ConfigInfo_v1610_IEs__list)
  : seq_cond CG_ConfigInfo_v1610_IEs__list y ->
 (CG_ConfigInfo_v1610_IEs__cond (CG_ConfigInfo_v1610_IEs__F2 y)) /\  CG_ConfigInfo_v1610_IEs__F1 (CG_ConfigInfo_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1610_IEs__Format : T_Format CG_ConfigInfo_v1610_IEs__Type CG_ConfigInfo_v1610_IEs__cond :=
        proj2_format  CG_ConfigInfo_v1610_IEs__cond CG_ConfigInfo_v1610_IEs__list__Format
    CG_ConfigInfo_v1610_IEs__F1 CG_ConfigInfo_v1610_IEs__F2 CG_ConfigInfo_v1610_IEs__F1F2_cond  CG_ConfigInfo_v1610_IEs__F1F2_cond2 CG_ConfigInfo_v1610_IEs__F2F1_cond.
Opaque CG_ConfigInfo_v1610_IEs__cond CG_ConfigInfo_v1610_IEs__Format.

