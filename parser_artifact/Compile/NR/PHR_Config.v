Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PHR_Config__phr_PeriodicTimer__Type : Set :=
 | PHR_Config__phr_PeriodicTimer__sf10
 | PHR_Config__phr_PeriodicTimer__sf20
 | PHR_Config__phr_PeriodicTimer__sf50
 | PHR_Config__phr_PeriodicTimer__sf100
 | PHR_Config__phr_PeriodicTimer__sf200
 | PHR_Config__phr_PeriodicTimer__sf500
 | PHR_Config__phr_PeriodicTimer__sf1000
 | PHR_Config__phr_PeriodicTimer__infinity
.
Definition PHR_Config__phr_PeriodicTimer__cond := (fun (_ : PHR_Config__phr_PeriodicTimer__Type) => True).
Lemma PHR_Config__phr_PeriodicTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PHR_Config__phr_PeriodicTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PHR_Config__phr_PeriodicTimer__nat__helper.

Definition PHR_Config__phr_PeriodicTimer__F1 t :=
  match t with
  | PHR_Config__phr_PeriodicTimer__sf10 => 0
  | PHR_Config__phr_PeriodicTimer__sf20 => 1
  | PHR_Config__phr_PeriodicTimer__sf50 => 2
  | PHR_Config__phr_PeriodicTimer__sf100 => 3
  | PHR_Config__phr_PeriodicTimer__sf200 => 4
  | PHR_Config__phr_PeriodicTimer__sf500 => 5
  | PHR_Config__phr_PeriodicTimer__sf1000 => 6
  | PHR_Config__phr_PeriodicTimer__infinity => 7
  end.
Definition PHR_Config__phr_PeriodicTimer__F2 n :=
  match n with
  | 0 => PHR_Config__phr_PeriodicTimer__sf10
  | 1 => PHR_Config__phr_PeriodicTimer__sf20
  | 2 => PHR_Config__phr_PeriodicTimer__sf50
  | 3 => PHR_Config__phr_PeriodicTimer__sf100
  | 4 => PHR_Config__phr_PeriodicTimer__sf200
  | 5 => PHR_Config__phr_PeriodicTimer__sf500
  | 6 => PHR_Config__phr_PeriodicTimer__sf1000
  | 7 => PHR_Config__phr_PeriodicTimer__infinity
  | _ => PHR_Config__phr_PeriodicTimer__sf10
  end.
Lemma PHR_Config__phr_PeriodicTimer__F1F2 : forall x : PHR_Config__phr_PeriodicTimer__Type, (PHR_Config__phr_PeriodicTimer__F1 x <= 7) /\ PHR_Config__phr_PeriodicTimer__F2 (PHR_Config__phr_PeriodicTimer__F1 x) = x. imp_solve. Qed.
Lemma PHR_Config__phr_PeriodicTimer__F2F1 : forall (y : nat) (H : y <= 7), PHR_Config__phr_PeriodicTimer__F1 (PHR_Config__phr_PeriodicTimer__F2 y) = y. enum_solve H y. Qed.

Inductive PHR_Config__phr_ProhibitTimer__Type : Set :=
 | PHR_Config__phr_ProhibitTimer__sf0
 | PHR_Config__phr_ProhibitTimer__sf10
 | PHR_Config__phr_ProhibitTimer__sf20
 | PHR_Config__phr_ProhibitTimer__sf50
 | PHR_Config__phr_ProhibitTimer__sf100
 | PHR_Config__phr_ProhibitTimer__sf200
 | PHR_Config__phr_ProhibitTimer__sf500
 | PHR_Config__phr_ProhibitTimer__sf1000
.
Definition PHR_Config__phr_ProhibitTimer__cond := (fun (_ : PHR_Config__phr_ProhibitTimer__Type) => True).
Lemma PHR_Config__phr_ProhibitTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PHR_Config__phr_ProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PHR_Config__phr_ProhibitTimer__nat__helper.

Definition PHR_Config__phr_ProhibitTimer__F1 t :=
  match t with
  | PHR_Config__phr_ProhibitTimer__sf0 => 0
  | PHR_Config__phr_ProhibitTimer__sf10 => 1
  | PHR_Config__phr_ProhibitTimer__sf20 => 2
  | PHR_Config__phr_ProhibitTimer__sf50 => 3
  | PHR_Config__phr_ProhibitTimer__sf100 => 4
  | PHR_Config__phr_ProhibitTimer__sf200 => 5
  | PHR_Config__phr_ProhibitTimer__sf500 => 6
  | PHR_Config__phr_ProhibitTimer__sf1000 => 7
  end.
Definition PHR_Config__phr_ProhibitTimer__F2 n :=
  match n with
  | 0 => PHR_Config__phr_ProhibitTimer__sf0
  | 1 => PHR_Config__phr_ProhibitTimer__sf10
  | 2 => PHR_Config__phr_ProhibitTimer__sf20
  | 3 => PHR_Config__phr_ProhibitTimer__sf50
  | 4 => PHR_Config__phr_ProhibitTimer__sf100
  | 5 => PHR_Config__phr_ProhibitTimer__sf200
  | 6 => PHR_Config__phr_ProhibitTimer__sf500
  | 7 => PHR_Config__phr_ProhibitTimer__sf1000
  | _ => PHR_Config__phr_ProhibitTimer__sf0
  end.
Lemma PHR_Config__phr_ProhibitTimer__F1F2 : forall x : PHR_Config__phr_ProhibitTimer__Type, (PHR_Config__phr_ProhibitTimer__F1 x <= 7) /\ PHR_Config__phr_ProhibitTimer__F2 (PHR_Config__phr_ProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma PHR_Config__phr_ProhibitTimer__F2F1 : forall (y : nat) (H : y <= 7), PHR_Config__phr_ProhibitTimer__F1 (PHR_Config__phr_ProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Inductive PHR_Config__phr_Tx_PowerFactorChange__Type : Set :=
 | PHR_Config__phr_Tx_PowerFactorChange__dB1
 | PHR_Config__phr_Tx_PowerFactorChange__dB3
 | PHR_Config__phr_Tx_PowerFactorChange__dB6
 | PHR_Config__phr_Tx_PowerFactorChange__infinity
.
Definition PHR_Config__phr_Tx_PowerFactorChange__cond := (fun (_ : PHR_Config__phr_Tx_PowerFactorChange__Type) => True).
Lemma PHR_Config__phr_Tx_PowerFactorChange__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PHR_Config__phr_Tx_PowerFactorChange__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PHR_Config__phr_Tx_PowerFactorChange__nat__helper.

Definition PHR_Config__phr_Tx_PowerFactorChange__F1 t :=
  match t with
  | PHR_Config__phr_Tx_PowerFactorChange__dB1 => 0
  | PHR_Config__phr_Tx_PowerFactorChange__dB3 => 1
  | PHR_Config__phr_Tx_PowerFactorChange__dB6 => 2
  | PHR_Config__phr_Tx_PowerFactorChange__infinity => 3
  end.
Definition PHR_Config__phr_Tx_PowerFactorChange__F2 n :=
  match n with
  | 0 => PHR_Config__phr_Tx_PowerFactorChange__dB1
  | 1 => PHR_Config__phr_Tx_PowerFactorChange__dB3
  | 2 => PHR_Config__phr_Tx_PowerFactorChange__dB6
  | 3 => PHR_Config__phr_Tx_PowerFactorChange__infinity
  | _ => PHR_Config__phr_Tx_PowerFactorChange__dB1
  end.
Lemma PHR_Config__phr_Tx_PowerFactorChange__F1F2 : forall x : PHR_Config__phr_Tx_PowerFactorChange__Type, (PHR_Config__phr_Tx_PowerFactorChange__F1 x <= 3) /\ PHR_Config__phr_Tx_PowerFactorChange__F2 (PHR_Config__phr_Tx_PowerFactorChange__F1 x) = x. imp_solve. Qed.
Lemma PHR_Config__phr_Tx_PowerFactorChange__F2F1 : forall (y : nat) (H : y <= 3), PHR_Config__phr_Tx_PowerFactorChange__F1 (PHR_Config__phr_Tx_PowerFactorChange__F2 y) = y. enum_solve H y. Qed.

Inductive PHR_Config__phr_ModeOtherCG__Type : Set :=
 | PHR_Config__phr_ModeOtherCG__real
 | PHR_Config__phr_ModeOtherCG__virtual
.
Definition PHR_Config__phr_ModeOtherCG__cond := (fun (_ : PHR_Config__phr_ModeOtherCG__Type) => True).
Lemma PHR_Config__phr_ModeOtherCG__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PHR_Config__phr_ModeOtherCG__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PHR_Config__phr_ModeOtherCG__nat__helper.

Definition PHR_Config__phr_ModeOtherCG__F1 t :=
  match t with
  | PHR_Config__phr_ModeOtherCG__real => 0
  | PHR_Config__phr_ModeOtherCG__virtual => 1
  end.
Definition PHR_Config__phr_ModeOtherCG__F2 n :=
  match n with
  | 0 => PHR_Config__phr_ModeOtherCG__real
  | 1 => PHR_Config__phr_ModeOtherCG__virtual
  | _ => PHR_Config__phr_ModeOtherCG__real
  end.
Lemma PHR_Config__phr_ModeOtherCG__F1F2 : forall x : PHR_Config__phr_ModeOtherCG__Type, (PHR_Config__phr_ModeOtherCG__F1 x <= 1) /\ PHR_Config__phr_ModeOtherCG__F2 (PHR_Config__phr_ModeOtherCG__F1 x) = x. imp_solve. Qed.
Lemma PHR_Config__phr_ModeOtherCG__F2F1 : forall (y : nat) (H : y <= 1), PHR_Config__phr_ModeOtherCG__F1 (PHR_Config__phr_ModeOtherCG__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.MPE_Config_FR2_r16.
Definition PHR_Config__ext0O__mpe_Reporting_FR2_r16__Type := SetupRelease__Type MPE_Config_FR2_r16__Type.
Definition PHR_Config__ext0O__mpe_Reporting_FR2_r16__cond := SetupRelease__cond _ MPE_Config_FR2_r16__cond.
Definition PHR_Config__ext0O__mpe_Reporting_FR2_r16__Format : T_Format PHR_Config__ext0O__mpe_Reporting_FR2_r16__Type PHR_Config__ext0O__mpe_Reporting_FR2_r16__cond := SetupRelease__Format _ _ MPE_Config_FR2_r16__Format.
Opaque PHR_Config__ext0O__mpe_Reporting_FR2_r16__cond PHR_Config__ext0O__mpe_Reporting_FR2_r16__Format.

Record PHR_Config__ext0O__Type : Set :=
  make__PHR_Config__ext0O__Type {
    PHR_Config__ext0O__mpe_Reporting_FR2_r16 : option PHR_Config__ext0O__mpe_Reporting_FR2_r16__Type ;
}.
Definition PHR_Config__ext0O__list := (
 Opt PHR_Config__ext0O__mpe_Reporting_FR2_r16__Type PHR_Config__ext0O__mpe_Reporting_FR2_r16__cond ::
 nil).
Definition PHR_Config__ext0O__cond z := 
  opt_cond PHR_Config__ext0O__mpe_Reporting_FR2_r16__cond (PHR_Config__ext0O__mpe_Reporting_FR2_r16 z) /\
  True.

Definition PHR_Config__ext0__Type := PHR_Config__ext0O__Type.
Definition PHR_Config__ext0__cond := PHR_Config__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.MPE_Config_FR2_r17.
Definition PHR_Config__ext1O__mpe_Reporting_FR2_r17__Type := SetupRelease__Type MPE_Config_FR2_r17__Type.
Definition PHR_Config__ext1O__mpe_Reporting_FR2_r17__cond := SetupRelease__cond _ MPE_Config_FR2_r17__cond.
Definition PHR_Config__ext1O__mpe_Reporting_FR2_r17__Format : T_Format PHR_Config__ext1O__mpe_Reporting_FR2_r17__Type PHR_Config__ext1O__mpe_Reporting_FR2_r17__cond := SetupRelease__Format _ _ MPE_Config_FR2_r17__Format.
Opaque PHR_Config__ext1O__mpe_Reporting_FR2_r17__cond PHR_Config__ext1O__mpe_Reporting_FR2_r17__Format.

Inductive PHR_Config__ext1O__twoPHRMode_r17__Type : Set :=
 | PHR_Config__ext1O__twoPHRMode_r17__enabled
.
Definition PHR_Config__ext1O__twoPHRMode_r17__cond := (fun (_ : PHR_Config__ext1O__twoPHRMode_r17__Type) => True).
Lemma PHR_Config__ext1O__twoPHRMode_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PHR_Config__ext1O__twoPHRMode_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PHR_Config__ext1O__twoPHRMode_r17__nat__helper.

Definition PHR_Config__ext1O__twoPHRMode_r17__F1 t :=
  match t with
  | PHR_Config__ext1O__twoPHRMode_r17__enabled => 0
  end.
Definition PHR_Config__ext1O__twoPHRMode_r17__F2 n :=
  match n with
  | 0 => PHR_Config__ext1O__twoPHRMode_r17__enabled
  | _ => PHR_Config__ext1O__twoPHRMode_r17__enabled
  end.
Lemma PHR_Config__ext1O__twoPHRMode_r17__F1F2 : forall x : PHR_Config__ext1O__twoPHRMode_r17__Type, (PHR_Config__ext1O__twoPHRMode_r17__F1 x <= 0) /\ PHR_Config__ext1O__twoPHRMode_r17__F2 (PHR_Config__ext1O__twoPHRMode_r17__F1 x) = x. imp_solve. Qed.
Lemma PHR_Config__ext1O__twoPHRMode_r17__F2F1 : forall (y : nat) (H : y <= 0), PHR_Config__ext1O__twoPHRMode_r17__F1 (PHR_Config__ext1O__twoPHRMode_r17__F2 y) = y. enum_solve H y. Qed.

Record PHR_Config__ext1O__Type : Set :=
  make__PHR_Config__ext1O__Type {
    PHR_Config__ext1O__mpe_Reporting_FR2_r17 : option PHR_Config__ext1O__mpe_Reporting_FR2_r17__Type ;
    PHR_Config__ext1O__twoPHRMode_r17 : option PHR_Config__ext1O__twoPHRMode_r17__Type ;
}.
Definition PHR_Config__ext1O__list := (
 Opt PHR_Config__ext1O__mpe_Reporting_FR2_r17__Type PHR_Config__ext1O__mpe_Reporting_FR2_r17__cond ::
 Opt PHR_Config__ext1O__twoPHRMode_r17__Type PHR_Config__ext1O__twoPHRMode_r17__cond ::
 nil).
Definition PHR_Config__ext1O__cond z := 
  opt_cond PHR_Config__ext1O__mpe_Reporting_FR2_r17__cond (PHR_Config__ext1O__mpe_Reporting_FR2_r17 z) /\
  opt_cond PHR_Config__ext1O__twoPHRMode_r17__cond (PHR_Config__ext1O__twoPHRMode_r17 z) /\
  True.

Definition PHR_Config__ext1__Type := PHR_Config__ext1O__Type.
Definition PHR_Config__ext1__cond := PHR_Config__ext1O__cond.

Record PHR_Config__Type : Set :=
  make__PHR_Config__Type {
    PHR_Config__phr_PeriodicTimer : PHR_Config__phr_PeriodicTimer__Type ;
    PHR_Config__phr_ProhibitTimer : PHR_Config__phr_ProhibitTimer__Type ;
    PHR_Config__phr_Tx_PowerFactorChange : PHR_Config__phr_Tx_PowerFactorChange__Type ;
    PHR_Config__multiplePHR : bool ;
    PHR_Config__dummy : bool ;
    PHR_Config__phr_Type2OtherCell : bool ;
    PHR_Config__phr_ModeOtherCG : PHR_Config__phr_ModeOtherCG__Type ;
    PHR_Config__ext0 : option PHR_Config__ext0__Type ;
    PHR_Config__ext1 : option PHR_Config__ext1__Type ;
}.
Definition PHR_Config__root_list : list seq_elem := (
 Nor PHR_Config__phr_PeriodicTimer__Type PHR_Config__phr_PeriodicTimer__cond ::
 Nor PHR_Config__phr_ProhibitTimer__Type PHR_Config__phr_ProhibitTimer__cond ::
 Nor PHR_Config__phr_Tx_PowerFactorChange__Type PHR_Config__phr_Tx_PowerFactorChange__cond ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor PHR_Config__phr_ModeOtherCG__Type PHR_Config__phr_ModeOtherCG__cond ::
 nil).
Definition PHR_Config__ext_list : list typ := (
  typ_cons PHR_Config__ext0__Type PHR_Config__ext0__cond ::
  typ_cons PHR_Config__ext1__Type PHR_Config__ext1__cond ::
  nil).
Definition PHR_Config__cond (z : PHR_Config__Type) := 
(  PHR_Config__phr_PeriodicTimer__cond (PHR_Config__phr_PeriodicTimer z) /\
  PHR_Config__phr_ProhibitTimer__cond (PHR_Config__phr_ProhibitTimer z) /\
  PHR_Config__phr_Tx_PowerFactorChange__cond (PHR_Config__phr_Tx_PowerFactorChange z) /\
  (fun _ => True) (PHR_Config__multiplePHR z) /\
  (fun _ => True) (PHR_Config__dummy z) /\
  (fun _ => True) (PHR_Config__phr_Type2OtherCell z) /\
  PHR_Config__phr_ModeOtherCG__cond (PHR_Config__phr_ModeOtherCG z) /\
  True) /\ 
(  opt_cond PHR_Config__ext0__cond (PHR_Config__ext0 z) /\
  opt_cond PHR_Config__ext1__cond (PHR_Config__ext1 z) /\
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
Definition PHR_Config__phr_PeriodicTimer__Format : T_Format PHR_Config__phr_PeriodicTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PHR_Config__phr_PeriodicTimer__nat__Format PHR_Config__phr_PeriodicTimer__F1 PHR_Config__phr_PeriodicTimer__F2 PHR_Config__phr_PeriodicTimer__F1F2 PHR_Config__phr_PeriodicTimer__F2F1.

Opaque PHR_Config__phr_PeriodicTimer__cond PHR_Config__phr_PeriodicTimer__Format.

Definition PHR_Config__phr_ProhibitTimer__Format : T_Format PHR_Config__phr_ProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PHR_Config__phr_ProhibitTimer__nat__Format PHR_Config__phr_ProhibitTimer__F1 PHR_Config__phr_ProhibitTimer__F2 PHR_Config__phr_ProhibitTimer__F1F2 PHR_Config__phr_ProhibitTimer__F2F1.

Opaque PHR_Config__phr_ProhibitTimer__cond PHR_Config__phr_ProhibitTimer__Format.

Definition PHR_Config__phr_Tx_PowerFactorChange__Format : T_Format PHR_Config__phr_Tx_PowerFactorChange__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PHR_Config__phr_Tx_PowerFactorChange__nat__Format PHR_Config__phr_Tx_PowerFactorChange__F1 PHR_Config__phr_Tx_PowerFactorChange__F2 PHR_Config__phr_Tx_PowerFactorChange__F1F2 PHR_Config__phr_Tx_PowerFactorChange__F2F1.

Opaque PHR_Config__phr_Tx_PowerFactorChange__cond PHR_Config__phr_Tx_PowerFactorChange__Format.

Definition PHR_Config__phr_ModeOtherCG__Format : T_Format PHR_Config__phr_ModeOtherCG__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PHR_Config__phr_ModeOtherCG__nat__Format PHR_Config__phr_ModeOtherCG__F1 PHR_Config__phr_ModeOtherCG__F2 PHR_Config__phr_ModeOtherCG__F1F2 PHR_Config__phr_ModeOtherCG__F2F1.

Opaque PHR_Config__phr_ModeOtherCG__cond PHR_Config__phr_ModeOtherCG__Format.

Opaque PHR_Config__ext0O__mpe_Reporting_FR2_r16__cond PHR_Config__ext0O__mpe_Reporting_FR2_r16__Format.


Definition PHR_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PHR_Config__ext0O__list.
Definition PHR_Config__ext0O__Format_list : PHR_Config__ext0O__Format_Type :=
  (PHR_Config__ext0O__mpe_Reporting_FR2_r16__Format, unit_format).
Definition PHR_Config__ext0O__list__Format := (*Eval compute in *) seq_format PHR_Config__ext0O__list PHR_Config__ext0O__Format_list.
Definition PHR_Config__ext0O__F1 z :=
  (PHR_Config__ext0O__mpe_Reporting_FR2_r16 z, tt).
Definition PHR_Config__ext0O__F2 (y : seq_type PHR_Config__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PHR_Config__ext0O__Type i0
  end.
Lemma PHR_Config__ext0O__F1F2_cond (z : PHR_Config__ext0O__Type)
  : PHR_Config__ext0O__cond z ->
  (seq_cond PHR_Config__ext0O__list (PHR_Config__ext0O__F1 z)).
intro H. unfold PHR_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PHR_Config__ext0O__F1F2_cond2 (z : PHR_Config__ext0O__Type)
 : PHR_Config__ext0O__F2 (PHR_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PHR_Config__ext0O__F2F1_cond (y : seq_type PHR_Config__ext0O__list)
  : seq_cond PHR_Config__ext0O__list y ->
 (PHR_Config__ext0O__cond (PHR_Config__ext0O__F2 y)) /\  PHR_Config__ext0O__F1 (PHR_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PHR_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PHR_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PHR_Config__ext0O__Format : T_Format PHR_Config__ext0O__Type PHR_Config__ext0O__cond :=
        proj2_format  PHR_Config__ext0O__cond PHR_Config__ext0O__list__Format
    PHR_Config__ext0O__F1 PHR_Config__ext0O__F2 PHR_Config__ext0O__F1F2_cond  PHR_Config__ext0O__F1F2_cond2 PHR_Config__ext0O__F2F1_cond.
Opaque PHR_Config__ext0O__cond PHR_Config__ext0O__Format.

Definition PHR_Config__ext0__check_all_none (b : PHR_Config__ext0O__Type) : bool :=
match b with 
  | make__PHR_Config__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PHR_Config__ext0__Format : T_Format PHR_Config__ext0__Type PHR_Config__ext0__cond :=
  restrict_add_format PHR_Config__ext0__check_all_none PHR_Config__ext0O__Format.

Opaque PHR_Config__ext0__cond PHR_Config__ext0__Format.

Opaque PHR_Config__ext1O__mpe_Reporting_FR2_r17__cond PHR_Config__ext1O__mpe_Reporting_FR2_r17__Format.

Definition PHR_Config__ext1O__twoPHRMode_r17__Format : T_Format PHR_Config__ext1O__twoPHRMode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PHR_Config__ext1O__twoPHRMode_r17__nat__Format PHR_Config__ext1O__twoPHRMode_r17__F1 PHR_Config__ext1O__twoPHRMode_r17__F2 PHR_Config__ext1O__twoPHRMode_r17__F1F2 PHR_Config__ext1O__twoPHRMode_r17__F2F1.

Opaque PHR_Config__ext1O__twoPHRMode_r17__cond PHR_Config__ext1O__twoPHRMode_r17__Format.


Definition PHR_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PHR_Config__ext1O__list.
Definition PHR_Config__ext1O__Format_list : PHR_Config__ext1O__Format_Type :=
  (PHR_Config__ext1O__mpe_Reporting_FR2_r17__Format, (PHR_Config__ext1O__twoPHRMode_r17__Format, unit_format)).
Definition PHR_Config__ext1O__list__Format := (*Eval compute in *) seq_format PHR_Config__ext1O__list PHR_Config__ext1O__Format_list.
Definition PHR_Config__ext1O__F1 z :=
  (PHR_Config__ext1O__mpe_Reporting_FR2_r17 z, (PHR_Config__ext1O__twoPHRMode_r17 z, tt)).
Definition PHR_Config__ext1O__F2 (y : seq_type PHR_Config__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PHR_Config__ext1O__Type i0 i1
  end.
Lemma PHR_Config__ext1O__F1F2_cond (z : PHR_Config__ext1O__Type)
  : PHR_Config__ext1O__cond z ->
  (seq_cond PHR_Config__ext1O__list (PHR_Config__ext1O__F1 z)).
intro H. unfold PHR_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PHR_Config__ext1O__F1F2_cond2 (z : PHR_Config__ext1O__Type)
 : PHR_Config__ext1O__F2 (PHR_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PHR_Config__ext1O__F2F1_cond (y : seq_type PHR_Config__ext1O__list)
  : seq_cond PHR_Config__ext1O__list y ->
 (PHR_Config__ext1O__cond (PHR_Config__ext1O__F2 y)) /\  PHR_Config__ext1O__F1 (PHR_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PHR_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PHR_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PHR_Config__ext1O__Format : T_Format PHR_Config__ext1O__Type PHR_Config__ext1O__cond :=
        proj2_format  PHR_Config__ext1O__cond PHR_Config__ext1O__list__Format
    PHR_Config__ext1O__F1 PHR_Config__ext1O__F2 PHR_Config__ext1O__F1F2_cond  PHR_Config__ext1O__F1F2_cond2 PHR_Config__ext1O__F2F1_cond.
Opaque PHR_Config__ext1O__cond PHR_Config__ext1O__Format.

Definition PHR_Config__ext1__check_all_none (b : PHR_Config__ext1O__Type) : bool :=
match b with 
  | make__PHR_Config__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition PHR_Config__ext1__Format : T_Format PHR_Config__ext1__Type PHR_Config__ext1__cond :=
  restrict_add_format PHR_Config__ext1__check_all_none PHR_Config__ext1O__Format.

Opaque PHR_Config__ext1__cond PHR_Config__ext1__Format.


Definition PHR_Config__root_Format_Type := Eval cbn in seq_format_prod PHR_Config__root_list.
Definition PHR_Config__root_Format_list : PHR_Config__root_Format_Type :=
  (PHR_Config__phr_PeriodicTimer__Format, (PHR_Config__phr_ProhibitTimer__Format, (PHR_Config__phr_Tx_PowerFactorChange__Format, (bool__Format, (bool__Format, (bool__Format, (PHR_Config__phr_ModeOtherCG__Format, unit_format))))))).

Definition PHR_Config__ext_Format_Type := Eval cbn in get_formats PHR_Config__ext_list.
Definition PHR_Config__ext_Format_list : PHR_Config__ext_Format_Type :=
  (PHR_Config__ext0__Format, (PHR_Config__ext1__Format, unit__Format)).

Definition PHR_Config__list_type : Set := (seq_type PHR_Config__root_list) * (seq_ext_type PHR_Config__ext_list).
Definition PHR_Config__list_cond (z : PHR_Config__list_type) : Prop :=
        (seq_cond PHR_Config__root_list (fst z)) /\ (seq_ext_cond PHR_Config__ext_list (snd z)).
Definition PHR_Config__list_format : T_Format PHR_Config__list_type PHR_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PHR_Config__root_list PHR_Config__root_Format_list PHR_Config__ext_list PHR_Config__ext_Format_list.

Opaque PHR_Config__list_format.
Definition PHR_Config__F1 (z : PHR_Config__Type) : PHR_Config__list_type :=
  (((PHR_Config__phr_PeriodicTimer z, (PHR_Config__phr_ProhibitTimer z, (PHR_Config__phr_Tx_PowerFactorChange z, (PHR_Config__multiplePHR z, (PHR_Config__dummy z, (PHR_Config__phr_Type2OtherCell z, (PHR_Config__phr_ModeOtherCG z, tt)))))))), (
(PHR_Config__ext0 z, (PHR_Config__ext1 z, tt)))).
Definition PHR_Config__F2 (y : PHR_Config__list_type) : PHR_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), (i0, (i1, _)))=>
    make__PHR_Config__Type j0 j1 j2 j3 j4 j5 j6 i0 i1
  end.
Definition PHR_Config__helper1 : (forall a : PHR_Config__Type, PHR_Config__cond a -> PHR_Config__list_cond (PHR_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PHR_Config__helper2 : (forall a : PHR_Config__Type, PHR_Config__F2 (PHR_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PHR_Config__helper3 : (forall b : PHR_Config__list_type, PHR_Config__list_cond b -> PHR_Config__cond (PHR_Config__F2 b) /\ PHR_Config__F1 (PHR_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PHR_Config__cond, PHR_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PHR_Config__Format : T_Format PHR_Config__Type PHR_Config__cond :=
 proj2_format PHR_Config__cond PHR_Config__list_format  PHR_Config__F1 PHR_Config__F2 PHR_Config__helper1 PHR_Config__helper2 PHR_Config__helper3.

Opaque PHR_Config__cond PHR_Config__Format.

