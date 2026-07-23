Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FailureReportSCG_EUTRA__failureType__Type : Set :=
 | FailureReportSCG_EUTRA__failureType__t313_Expiry
 | FailureReportSCG_EUTRA__failureType__randomAccessProblem
 | FailureReportSCG_EUTRA__failureType__rlc_MaxNumRetx
 | FailureReportSCG_EUTRA__failureType__scg_ChangeFailure
 | FailureReportSCG_EUTRA__failureType__spare4
 | FailureReportSCG_EUTRA__failureType__spare3
 | FailureReportSCG_EUTRA__failureType__spare2
 | FailureReportSCG_EUTRA__failureType__spare1
.
Definition FailureReportSCG_EUTRA__failureType__cond := (fun (_ : FailureReportSCG_EUTRA__failureType__Type) => True).
Lemma FailureReportSCG_EUTRA__failureType__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FailureReportSCG_EUTRA__failureType__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 FailureReportSCG_EUTRA__failureType__nat__helper.

Definition FailureReportSCG_EUTRA__failureType__F1 t :=
  match t with
  | FailureReportSCG_EUTRA__failureType__t313_Expiry => 0
  | FailureReportSCG_EUTRA__failureType__randomAccessProblem => 1
  | FailureReportSCG_EUTRA__failureType__rlc_MaxNumRetx => 2
  | FailureReportSCG_EUTRA__failureType__scg_ChangeFailure => 3
  | FailureReportSCG_EUTRA__failureType__spare4 => 4
  | FailureReportSCG_EUTRA__failureType__spare3 => 5
  | FailureReportSCG_EUTRA__failureType__spare2 => 6
  | FailureReportSCG_EUTRA__failureType__spare1 => 7
  end.
Definition FailureReportSCG_EUTRA__failureType__F2 n :=
  match n with
  | 0 => FailureReportSCG_EUTRA__failureType__t313_Expiry
  | 1 => FailureReportSCG_EUTRA__failureType__randomAccessProblem
  | 2 => FailureReportSCG_EUTRA__failureType__rlc_MaxNumRetx
  | 3 => FailureReportSCG_EUTRA__failureType__scg_ChangeFailure
  | 4 => FailureReportSCG_EUTRA__failureType__spare4
  | 5 => FailureReportSCG_EUTRA__failureType__spare3
  | 6 => FailureReportSCG_EUTRA__failureType__spare2
  | 7 => FailureReportSCG_EUTRA__failureType__spare1
  | _ => FailureReportSCG_EUTRA__failureType__t313_Expiry
  end.
Lemma FailureReportSCG_EUTRA__failureType__F1F2 : forall x : FailureReportSCG_EUTRA__failureType__Type, (FailureReportSCG_EUTRA__failureType__F1 x <= 7) /\ FailureReportSCG_EUTRA__failureType__F2 (FailureReportSCG_EUTRA__failureType__F1 x) = x. imp_solve. Qed.
Lemma FailureReportSCG_EUTRA__failureType__F2F1 : forall (y : nat) (H : y <= 7), FailureReportSCG_EUTRA__failureType__F1 (FailureReportSCG_EUTRA__failureType__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasResultFreqListFailMRDC.

Opaque MeasResultFreqListFailMRDC__cond MeasResultFreqListFailMRDC__Format.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Record FailureReportSCG_EUTRA__ext0O__Type : Set :=
  make__FailureReportSCG_EUTRA__ext0O__Type {
    FailureReportSCG_EUTRA__ext0O__locationInfo_r16 : option LocationInfo_r16__Type ;
}.
Definition FailureReportSCG_EUTRA__ext0O__list := (
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 nil).
Definition FailureReportSCG_EUTRA__ext0O__cond z := 
  opt_cond LocationInfo_r16__cond (FailureReportSCG_EUTRA__ext0O__locationInfo_r16 z) /\
  True.

Definition FailureReportSCG_EUTRA__ext0__Type := FailureReportSCG_EUTRA__ext0O__Type.
Definition FailureReportSCG_EUTRA__ext0__cond := FailureReportSCG_EUTRA__ext0O__cond.

Record FailureReportSCG_EUTRA__Type : Set :=
  make__FailureReportSCG_EUTRA__Type {
    FailureReportSCG_EUTRA__failureType : FailureReportSCG_EUTRA__failureType__Type ;
    FailureReportSCG_EUTRA__measResultFreqListMRDC : option MeasResultFreqListFailMRDC__Type ;
    FailureReportSCG_EUTRA__measResultSCG_FailureMRDC : option octet_string ;
    FailureReportSCG_EUTRA__ext0 : option FailureReportSCG_EUTRA__ext0__Type ;
}.
Definition FailureReportSCG_EUTRA__root_list : list seq_elem := (
 Nor FailureReportSCG_EUTRA__failureType__Type FailureReportSCG_EUTRA__failureType__cond ::
 Opt MeasResultFreqListFailMRDC__Type MeasResultFreqListFailMRDC__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition FailureReportSCG_EUTRA__ext_list : list typ := (
  typ_cons FailureReportSCG_EUTRA__ext0__Type FailureReportSCG_EUTRA__ext0__cond ::
  nil).
Definition FailureReportSCG_EUTRA__cond (z : FailureReportSCG_EUTRA__Type) := 
(  FailureReportSCG_EUTRA__failureType__cond (FailureReportSCG_EUTRA__failureType z) /\
  opt_cond MeasResultFreqListFailMRDC__cond (FailureReportSCG_EUTRA__measResultFreqListMRDC z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (FailureReportSCG_EUTRA__measResultSCG_FailureMRDC z) /\
  True) /\ 
(  opt_cond FailureReportSCG_EUTRA__ext0__cond (FailureReportSCG_EUTRA__ext0 z) /\
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
Definition FailureReportSCG_EUTRA__failureType__Format : T_Format FailureReportSCG_EUTRA__failureType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FailureReportSCG_EUTRA__failureType__nat__Format FailureReportSCG_EUTRA__failureType__F1 FailureReportSCG_EUTRA__failureType__F2 FailureReportSCG_EUTRA__failureType__F1F2 FailureReportSCG_EUTRA__failureType__F2F1.

Opaque FailureReportSCG_EUTRA__failureType__cond FailureReportSCG_EUTRA__failureType__Format.


Definition FailureReportSCG_EUTRA__ext0O__Format_Type := Eval cbn in seq_format_prod FailureReportSCG_EUTRA__ext0O__list.
Definition FailureReportSCG_EUTRA__ext0O__Format_list : FailureReportSCG_EUTRA__ext0O__Format_Type :=
  (LocationInfo_r16__Format, unit_format).
Definition FailureReportSCG_EUTRA__ext0O__list__Format := (*Eval compute in *) seq_format FailureReportSCG_EUTRA__ext0O__list FailureReportSCG_EUTRA__ext0O__Format_list.
Definition FailureReportSCG_EUTRA__ext0O__F1 z :=
  (FailureReportSCG_EUTRA__ext0O__locationInfo_r16 z, tt).
Definition FailureReportSCG_EUTRA__ext0O__F2 (y : seq_type FailureReportSCG_EUTRA__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__FailureReportSCG_EUTRA__ext0O__Type i0
  end.
Lemma FailureReportSCG_EUTRA__ext0O__F1F2_cond (z : FailureReportSCG_EUTRA__ext0O__Type)
  : FailureReportSCG_EUTRA__ext0O__cond z ->
  (seq_cond FailureReportSCG_EUTRA__ext0O__list (FailureReportSCG_EUTRA__ext0O__F1 z)).
intro H. unfold FailureReportSCG_EUTRA__ext0O__cond in H. simpl. auto. Qed.
Lemma FailureReportSCG_EUTRA__ext0O__F1F2_cond2 (z : FailureReportSCG_EUTRA__ext0O__Type)
 : FailureReportSCG_EUTRA__ext0O__F2 (FailureReportSCG_EUTRA__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureReportSCG_EUTRA__ext0O__F2F1_cond (y : seq_type FailureReportSCG_EUTRA__ext0O__list)
  : seq_cond FailureReportSCG_EUTRA__ext0O__list y ->
 (FailureReportSCG_EUTRA__ext0O__cond (FailureReportSCG_EUTRA__ext0O__F2 y)) /\  FailureReportSCG_EUTRA__ext0O__F1 (FailureReportSCG_EUTRA__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureReportSCG_EUTRA__ext0O__cond. simpl in *. auto.
 - simpl. unfold FailureReportSCG_EUTRA__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureReportSCG_EUTRA__ext0O__Format : T_Format FailureReportSCG_EUTRA__ext0O__Type FailureReportSCG_EUTRA__ext0O__cond :=
        proj2_format  FailureReportSCG_EUTRA__ext0O__cond FailureReportSCG_EUTRA__ext0O__list__Format
    FailureReportSCG_EUTRA__ext0O__F1 FailureReportSCG_EUTRA__ext0O__F2 FailureReportSCG_EUTRA__ext0O__F1F2_cond  FailureReportSCG_EUTRA__ext0O__F1F2_cond2 FailureReportSCG_EUTRA__ext0O__F2F1_cond.
Opaque FailureReportSCG_EUTRA__ext0O__cond FailureReportSCG_EUTRA__ext0O__Format.

Definition FailureReportSCG_EUTRA__ext0__check_all_none (b : FailureReportSCG_EUTRA__ext0O__Type) : bool :=
match b with 
  | make__FailureReportSCG_EUTRA__ext0O__Type None  => false 
  | _ => true 
 end.
Definition FailureReportSCG_EUTRA__ext0__Format : T_Format FailureReportSCG_EUTRA__ext0__Type FailureReportSCG_EUTRA__ext0__cond :=
  restrict_add_format FailureReportSCG_EUTRA__ext0__check_all_none FailureReportSCG_EUTRA__ext0O__Format.

Opaque FailureReportSCG_EUTRA__ext0__cond FailureReportSCG_EUTRA__ext0__Format.


Definition FailureReportSCG_EUTRA__root_Format_Type := Eval cbn in seq_format_prod FailureReportSCG_EUTRA__root_list.
Definition FailureReportSCG_EUTRA__root_Format_list : FailureReportSCG_EUTRA__root_Format_Type :=
  (FailureReportSCG_EUTRA__failureType__Format, (MeasResultFreqListFailMRDC__Format, (octet_string_nc__Format, unit_format))).

Definition FailureReportSCG_EUTRA__ext_Format_Type := Eval cbn in get_formats FailureReportSCG_EUTRA__ext_list.
Definition FailureReportSCG_EUTRA__ext_Format_list : FailureReportSCG_EUTRA__ext_Format_Type :=
  (FailureReportSCG_EUTRA__ext0__Format, unit__Format).

Definition FailureReportSCG_EUTRA__list_type : Set := (seq_type FailureReportSCG_EUTRA__root_list) * (seq_ext_type FailureReportSCG_EUTRA__ext_list).
Definition FailureReportSCG_EUTRA__list_cond (z : FailureReportSCG_EUTRA__list_type) : Prop :=
        (seq_cond FailureReportSCG_EUTRA__root_list (fst z)) /\ (seq_ext_cond FailureReportSCG_EUTRA__ext_list (snd z)).
Definition FailureReportSCG_EUTRA__list_format : T_Format FailureReportSCG_EUTRA__list_type FailureReportSCG_EUTRA__list_cond :=
 (* Eval compute in *) seq_ext_format FailureReportSCG_EUTRA__root_list FailureReportSCG_EUTRA__root_Format_list FailureReportSCG_EUTRA__ext_list FailureReportSCG_EUTRA__ext_Format_list.

Opaque FailureReportSCG_EUTRA__list_format.
Definition FailureReportSCG_EUTRA__F1 (z : FailureReportSCG_EUTRA__Type) : FailureReportSCG_EUTRA__list_type :=
  (((FailureReportSCG_EUTRA__failureType z, (FailureReportSCG_EUTRA__measResultFreqListMRDC z, (FailureReportSCG_EUTRA__measResultSCG_FailureMRDC z, tt)))), (
(FailureReportSCG_EUTRA__ext0 z, tt))).
Definition FailureReportSCG_EUTRA__F2 (y : FailureReportSCG_EUTRA__list_type) : FailureReportSCG_EUTRA__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__FailureReportSCG_EUTRA__Type j0 j1 j2 i0
  end.
Definition FailureReportSCG_EUTRA__helper1 : (forall a : FailureReportSCG_EUTRA__Type, FailureReportSCG_EUTRA__cond a -> FailureReportSCG_EUTRA__list_cond (FailureReportSCG_EUTRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FailureReportSCG_EUTRA__helper2 : (forall a : FailureReportSCG_EUTRA__Type, FailureReportSCG_EUTRA__F2 (FailureReportSCG_EUTRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FailureReportSCG_EUTRA__helper3 : (forall b : FailureReportSCG_EUTRA__list_type, FailureReportSCG_EUTRA__list_cond b -> FailureReportSCG_EUTRA__cond (FailureReportSCG_EUTRA__F2 b) /\ FailureReportSCG_EUTRA__F1 (FailureReportSCG_EUTRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FailureReportSCG_EUTRA__cond, FailureReportSCG_EUTRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FailureReportSCG_EUTRA__Format : T_Format FailureReportSCG_EUTRA__Type FailureReportSCG_EUTRA__cond :=
 proj2_format FailureReportSCG_EUTRA__cond FailureReportSCG_EUTRA__list_format  FailureReportSCG_EUTRA__F1 FailureReportSCG_EUTRA__F2 FailureReportSCG_EUTRA__helper1 FailureReportSCG_EUTRA__helper2 FailureReportSCG_EUTRA__helper3.

Opaque FailureReportSCG_EUTRA__cond FailureReportSCG_EUTRA__Format.

