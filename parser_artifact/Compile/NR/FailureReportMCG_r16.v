Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FailureReportMCG_r16__failureType_r16__Type : Set :=
 | FailureReportMCG_r16__failureType_r16__t310_Expiry
 | FailureReportMCG_r16__failureType_r16__randomAccessProblem
 | FailureReportMCG_r16__failureType_r16__rlc_MaxNumRetx
 | FailureReportMCG_r16__failureType_r16__t312_Expiry_r16
 | FailureReportMCG_r16__failureType_r16__lbt_Failure_r16
 | FailureReportMCG_r16__failureType_r16__beamFailureRecoveryFailure_r16
 | FailureReportMCG_r16__failureType_r16__bh_RLF_r16
 | FailureReportMCG_r16__failureType_r16__spare1
.
Definition FailureReportMCG_r16__failureType_r16__cond := (fun (_ : FailureReportMCG_r16__failureType_r16__Type) => True).
Lemma FailureReportMCG_r16__failureType_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FailureReportMCG_r16__failureType_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 FailureReportMCG_r16__failureType_r16__nat__helper.

Definition FailureReportMCG_r16__failureType_r16__F1 t :=
  match t with
  | FailureReportMCG_r16__failureType_r16__t310_Expiry => 0
  | FailureReportMCG_r16__failureType_r16__randomAccessProblem => 1
  | FailureReportMCG_r16__failureType_r16__rlc_MaxNumRetx => 2
  | FailureReportMCG_r16__failureType_r16__t312_Expiry_r16 => 3
  | FailureReportMCG_r16__failureType_r16__lbt_Failure_r16 => 4
  | FailureReportMCG_r16__failureType_r16__beamFailureRecoveryFailure_r16 => 5
  | FailureReportMCG_r16__failureType_r16__bh_RLF_r16 => 6
  | FailureReportMCG_r16__failureType_r16__spare1 => 7
  end.
Definition FailureReportMCG_r16__failureType_r16__F2 n :=
  match n with
  | 0 => FailureReportMCG_r16__failureType_r16__t310_Expiry
  | 1 => FailureReportMCG_r16__failureType_r16__randomAccessProblem
  | 2 => FailureReportMCG_r16__failureType_r16__rlc_MaxNumRetx
  | 3 => FailureReportMCG_r16__failureType_r16__t312_Expiry_r16
  | 4 => FailureReportMCG_r16__failureType_r16__lbt_Failure_r16
  | 5 => FailureReportMCG_r16__failureType_r16__beamFailureRecoveryFailure_r16
  | 6 => FailureReportMCG_r16__failureType_r16__bh_RLF_r16
  | 7 => FailureReportMCG_r16__failureType_r16__spare1
  | _ => FailureReportMCG_r16__failureType_r16__t310_Expiry
  end.
Lemma FailureReportMCG_r16__failureType_r16__F1F2 : forall x : FailureReportMCG_r16__failureType_r16__Type, (FailureReportMCG_r16__failureType_r16__F1 x <= 7) /\ FailureReportMCG_r16__failureType_r16__F2 (FailureReportMCG_r16__failureType_r16__F1 x) = x. imp_solve. Qed.
Lemma FailureReportMCG_r16__failureType_r16__F2F1 : forall (y : nat) (H : y <= 7), FailureReportMCG_r16__failureType_r16__F1 (FailureReportMCG_r16__failureType_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasResultList2NR.

Opaque MeasResultList2NR__cond MeasResultList2NR__Format.

Require Import NR.MeasResultList2EUTRA.

Opaque MeasResultList2EUTRA__cond MeasResultList2EUTRA__Format.

Require Import NR.MeasResultList2UTRA.

Opaque MeasResultList2UTRA__cond MeasResultList2UTRA__Format.

Record FailureReportMCG_r16__Type : Set :=
  make__FailureReportMCG_r16__Type {
    FailureReportMCG_r16__failureType_r16 : option FailureReportMCG_r16__failureType_r16__Type ;
    FailureReportMCG_r16__measResultFreqList_r16 : option MeasResultList2NR__Type ;
    FailureReportMCG_r16__measResultFreqListEUTRA_r16 : option MeasResultList2EUTRA__Type ;
    FailureReportMCG_r16__measResultSCG_r16 : option octet_string ;
    FailureReportMCG_r16__measResultSCG_EUTRA_r16 : option octet_string ;
    FailureReportMCG_r16__measResultFreqListUTRA_FDD_r16 : option MeasResultList2UTRA__Type ;
}.
Definition FailureReportMCG_r16__root_list : list seq_elem := (
 Opt FailureReportMCG_r16__failureType_r16__Type FailureReportMCG_r16__failureType_r16__cond ::
 Opt MeasResultList2NR__Type MeasResultList2NR__cond ::
 Opt MeasResultList2EUTRA__Type MeasResultList2EUTRA__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasResultList2UTRA__Type MeasResultList2UTRA__cond ::
 nil).
Definition FailureReportMCG_r16__ext_list : list typ := (
  nil).
Definition FailureReportMCG_r16__cond (z : FailureReportMCG_r16__Type) := 
(  opt_cond FailureReportMCG_r16__failureType_r16__cond (FailureReportMCG_r16__failureType_r16 z) /\
  opt_cond MeasResultList2NR__cond (FailureReportMCG_r16__measResultFreqList_r16 z) /\
  opt_cond MeasResultList2EUTRA__cond (FailureReportMCG_r16__measResultFreqListEUTRA_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (FailureReportMCG_r16__measResultSCG_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (FailureReportMCG_r16__measResultSCG_EUTRA_r16 z) /\
  opt_cond MeasResultList2UTRA__cond (FailureReportMCG_r16__measResultFreqListUTRA_FDD_r16 z) /\
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
Definition FailureReportMCG_r16__failureType_r16__Format : T_Format FailureReportMCG_r16__failureType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FailureReportMCG_r16__failureType_r16__nat__Format FailureReportMCG_r16__failureType_r16__F1 FailureReportMCG_r16__failureType_r16__F2 FailureReportMCG_r16__failureType_r16__F1F2 FailureReportMCG_r16__failureType_r16__F2F1.

Opaque FailureReportMCG_r16__failureType_r16__cond FailureReportMCG_r16__failureType_r16__Format.


Definition FailureReportMCG_r16__root_Format_Type := Eval cbn in seq_format_prod FailureReportMCG_r16__root_list.
Definition FailureReportMCG_r16__root_Format_list : FailureReportMCG_r16__root_Format_Type :=
  (FailureReportMCG_r16__failureType_r16__Format, (MeasResultList2NR__Format, (MeasResultList2EUTRA__Format, (octet_string_nc__Format, (octet_string_nc__Format, (MeasResultList2UTRA__Format, unit_format)))))).

Definition FailureReportMCG_r16__ext_Format_Type := Eval cbn in get_formats FailureReportMCG_r16__ext_list.
Definition FailureReportMCG_r16__ext_Format_list : FailureReportMCG_r16__ext_Format_Type :=
  unit__Format.

Definition FailureReportMCG_r16__list_type : Set := (seq_type FailureReportMCG_r16__root_list) * (seq_ext_type FailureReportMCG_r16__ext_list).
Definition FailureReportMCG_r16__list_cond (z : FailureReportMCG_r16__list_type) : Prop :=
        (seq_cond FailureReportMCG_r16__root_list (fst z)) /\ (seq_ext_cond FailureReportMCG_r16__ext_list (snd z)).
Definition FailureReportMCG_r16__list_format : T_Format FailureReportMCG_r16__list_type FailureReportMCG_r16__list_cond :=
 (* Eval compute in *) seq_ext_format FailureReportMCG_r16__root_list FailureReportMCG_r16__root_Format_list FailureReportMCG_r16__ext_list FailureReportMCG_r16__ext_Format_list.

Opaque FailureReportMCG_r16__list_format.
Definition FailureReportMCG_r16__F1 (z : FailureReportMCG_r16__Type) : FailureReportMCG_r16__list_type :=
  (((FailureReportMCG_r16__failureType_r16 z, (FailureReportMCG_r16__measResultFreqList_r16 z, (FailureReportMCG_r16__measResultFreqListEUTRA_r16 z, (FailureReportMCG_r16__measResultSCG_r16 z, (FailureReportMCG_r16__measResultSCG_EUTRA_r16 z, (FailureReportMCG_r16__measResultFreqListUTRA_FDD_r16 z, tt))))))), (
tt)).
Definition FailureReportMCG_r16__F2 (y : FailureReportMCG_r16__list_type) : FailureReportMCG_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__FailureReportMCG_r16__Type j0 j1 j2 j3 j4 j5
  end.
Definition FailureReportMCG_r16__helper1 : (forall a : FailureReportMCG_r16__Type, FailureReportMCG_r16__cond a -> FailureReportMCG_r16__list_cond (FailureReportMCG_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FailureReportMCG_r16__helper2 : (forall a : FailureReportMCG_r16__Type, FailureReportMCG_r16__F2 (FailureReportMCG_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FailureReportMCG_r16__helper3 : (forall b : FailureReportMCG_r16__list_type, FailureReportMCG_r16__list_cond b -> FailureReportMCG_r16__cond (FailureReportMCG_r16__F2 b) /\ FailureReportMCG_r16__F1 (FailureReportMCG_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FailureReportMCG_r16__cond, FailureReportMCG_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FailureReportMCG_r16__Format : T_Format FailureReportMCG_r16__Type FailureReportMCG_r16__cond :=
 proj2_format FailureReportMCG_r16__cond FailureReportMCG_r16__list_format  FailureReportMCG_r16__F1 FailureReportMCG_r16__F2 FailureReportMCG_r16__helper1 FailureReportMCG_r16__helper2 FailureReportMCG_r16__helper3.

Opaque FailureReportMCG_r16__cond FailureReportMCG_r16__Format.

