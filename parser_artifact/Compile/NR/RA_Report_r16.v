Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.PCI_ARFCN_NR_r16.

Opaque PCI_ARFCN_NR_r16__cond PCI_ARFCN_NR_r16__Format.


Inductive RA_Report_r16__cellId_r16__Type : Set :=
  | RA_Report_r16__cellId_r16__cellGlobalId_r16 : CGI_Info_Logging_r16__Type -> RA_Report_r16__cellId_r16__Type
  | RA_Report_r16__cellId_r16__pci_arfcn_r16 : PCI_ARFCN_NR_r16__Type -> RA_Report_r16__cellId_r16__Type
.
Definition RA_Report_r16__cellId_r16__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons PCI_ARFCN_NR_r16__Type PCI_ARFCN_NR_r16__cond ::
 nil).
Definition RA_Report_r16__cellId_r16__cond (c : RA_Report_r16__cellId_r16__Type) := 
  match c with
  | RA_Report_r16__cellId_r16__cellGlobalId_r16 t => CGI_Info_Logging_r16__cond t 
  | RA_Report_r16__cellId_r16__pci_arfcn_r16 t => PCI_ARFCN_NR_r16__cond t 
  end.

Lemma RA_Report_r16__cellId_r16__len_helper1 : to_bit_sz (length RA_Report_r16__cellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RA_Report_r16__cellId_r16__len_helper2 : 2 <= length2 RA_Report_r16__cellId_r16__list.
 simpl. lia. Qed.
Require Import NR.RA_InformationCommon_r16.

Opaque RA_InformationCommon_r16__cond RA_InformationCommon_r16__Format.

Inductive RA_Report_r16__raPurpose_r16__Type : Set :=
 | RA_Report_r16__raPurpose_r16__accessRelated
 | RA_Report_r16__raPurpose_r16__beamFailureRecovery
 | RA_Report_r16__raPurpose_r16__reconfigurationWithSync
 | RA_Report_r16__raPurpose_r16__ulUnSynchronized
 | RA_Report_r16__raPurpose_r16__schedulingRequestFailure
 | RA_Report_r16__raPurpose_r16__noPUCCHResourceAvailable
 | RA_Report_r16__raPurpose_r16__requestForOtherSI
 | RA_Report_r16__raPurpose_r16__msg3RequestForOtherSI_r17
 | RA_Report_r16__raPurpose_r16__spare8
 | RA_Report_r16__raPurpose_r16__spare7
 | RA_Report_r16__raPurpose_r16__spare6
 | RA_Report_r16__raPurpose_r16__spare5
 | RA_Report_r16__raPurpose_r16__spare4
 | RA_Report_r16__raPurpose_r16__spare3
 | RA_Report_r16__raPurpose_r16__spare2
 | RA_Report_r16__raPurpose_r16__spare1
.
Definition RA_Report_r16__raPurpose_r16__cond := (fun (_ : RA_Report_r16__raPurpose_r16__Type) => True).
Lemma RA_Report_r16__raPurpose_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_Report_r16__raPurpose_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RA_Report_r16__raPurpose_r16__nat__helper.

Definition RA_Report_r16__raPurpose_r16__F1 t :=
  match t with
  | RA_Report_r16__raPurpose_r16__accessRelated => 0
  | RA_Report_r16__raPurpose_r16__beamFailureRecovery => 1
  | RA_Report_r16__raPurpose_r16__reconfigurationWithSync => 2
  | RA_Report_r16__raPurpose_r16__ulUnSynchronized => 3
  | RA_Report_r16__raPurpose_r16__schedulingRequestFailure => 4
  | RA_Report_r16__raPurpose_r16__noPUCCHResourceAvailable => 5
  | RA_Report_r16__raPurpose_r16__requestForOtherSI => 6
  | RA_Report_r16__raPurpose_r16__msg3RequestForOtherSI_r17 => 7
  | RA_Report_r16__raPurpose_r16__spare8 => 8
  | RA_Report_r16__raPurpose_r16__spare7 => 9
  | RA_Report_r16__raPurpose_r16__spare6 => 10
  | RA_Report_r16__raPurpose_r16__spare5 => 11
  | RA_Report_r16__raPurpose_r16__spare4 => 12
  | RA_Report_r16__raPurpose_r16__spare3 => 13
  | RA_Report_r16__raPurpose_r16__spare2 => 14
  | RA_Report_r16__raPurpose_r16__spare1 => 15
  end.
Definition RA_Report_r16__raPurpose_r16__F2 n :=
  match n with
  | 0 => RA_Report_r16__raPurpose_r16__accessRelated
  | 1 => RA_Report_r16__raPurpose_r16__beamFailureRecovery
  | 2 => RA_Report_r16__raPurpose_r16__reconfigurationWithSync
  | 3 => RA_Report_r16__raPurpose_r16__ulUnSynchronized
  | 4 => RA_Report_r16__raPurpose_r16__schedulingRequestFailure
  | 5 => RA_Report_r16__raPurpose_r16__noPUCCHResourceAvailable
  | 6 => RA_Report_r16__raPurpose_r16__requestForOtherSI
  | 7 => RA_Report_r16__raPurpose_r16__msg3RequestForOtherSI_r17
  | 8 => RA_Report_r16__raPurpose_r16__spare8
  | 9 => RA_Report_r16__raPurpose_r16__spare7
  | 10 => RA_Report_r16__raPurpose_r16__spare6
  | 11 => RA_Report_r16__raPurpose_r16__spare5
  | 12 => RA_Report_r16__raPurpose_r16__spare4
  | 13 => RA_Report_r16__raPurpose_r16__spare3
  | 14 => RA_Report_r16__raPurpose_r16__spare2
  | 15 => RA_Report_r16__raPurpose_r16__spare1
  | _ => RA_Report_r16__raPurpose_r16__accessRelated
  end.
Lemma RA_Report_r16__raPurpose_r16__F1F2 : forall x : RA_Report_r16__raPurpose_r16__Type, (RA_Report_r16__raPurpose_r16__F1 x <= 15) /\ RA_Report_r16__raPurpose_r16__F2 (RA_Report_r16__raPurpose_r16__F1 x) = x. imp_solve. Qed.
Lemma RA_Report_r16__raPurpose_r16__F2F1 : forall (y : nat) (H : y <= 15), RA_Report_r16__raPurpose_r16__F1 (RA_Report_r16__raPurpose_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Record RA_Report_r16__ext0O__Type : Set :=
  make__RA_Report_r16__ext0O__Type {
    RA_Report_r16__ext0O__spCellID_r17 : option CGI_Info_Logging_r16__Type ;
}.
Definition RA_Report_r16__ext0O__list := (
 Opt CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
 nil).
Definition RA_Report_r16__ext0O__cond z := 
  opt_cond CGI_Info_Logging_r16__cond (RA_Report_r16__ext0O__spCellID_r17 z) /\
  True.

Definition RA_Report_r16__ext0__Type := RA_Report_r16__ext0O__Type.
Definition RA_Report_r16__ext0__cond := RA_Report_r16__ext0O__cond.

Record RA_Report_r16__Type : Set :=
  make__RA_Report_r16__Type {
    RA_Report_r16__cellId_r16 : RA_Report_r16__cellId_r16__Type ;
    RA_Report_r16__ra_InformationCommon_r16 : option RA_InformationCommon_r16__Type ;
    RA_Report_r16__raPurpose_r16 : RA_Report_r16__raPurpose_r16__Type ;
    RA_Report_r16__ext0 : option RA_Report_r16__ext0__Type ;
}.
Definition RA_Report_r16__root_list : list seq_elem := (
 Nor RA_Report_r16__cellId_r16__Type RA_Report_r16__cellId_r16__cond ::
 Opt RA_InformationCommon_r16__Type RA_InformationCommon_r16__cond ::
 Nor RA_Report_r16__raPurpose_r16__Type RA_Report_r16__raPurpose_r16__cond ::
 nil).
Definition RA_Report_r16__ext_list : list typ := (
  typ_cons RA_Report_r16__ext0__Type RA_Report_r16__ext0__cond ::
  nil).
Definition RA_Report_r16__cond (z : RA_Report_r16__Type) := 
(  RA_Report_r16__cellId_r16__cond (RA_Report_r16__cellId_r16 z) /\
  opt_cond RA_InformationCommon_r16__cond (RA_Report_r16__ra_InformationCommon_r16 z) /\
  RA_Report_r16__raPurpose_r16__cond (RA_Report_r16__raPurpose_r16 z) /\
  True) /\ 
(  opt_cond RA_Report_r16__ext0__cond (RA_Report_r16__ext0 z) /\
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

Definition RA_Report_r16__cellId_r16__Format_Type := Eval cbn in get_formats RA_Report_r16__cellId_r16__list.
Definition RA_Report_r16__cellId_r16__Format_list : RA_Report_r16__cellId_r16__Format_Type :=
  (CGI_Info_Logging_r16__Format, (PCI_ARFCN_NR_r16__Format, unit__Format)).
Definition RA_Report_r16__cellId_r16__list__Format := Eval compute in choice_format RA_Report_r16__cellId_r16__list RA_Report_r16__cellId_r16__len_helper1 RA_Report_r16__cellId_r16__len_helper2  RA_Report_r16__cellId_r16__Format_list.
Definition RA_Report_r16__cellId_r16__F1 (z : RA_Report_r16__cellId_r16__Type) : (choice RA_Report_r16__cellId_r16__list) :=
  match z with
   | RA_Report_r16__cellId_r16__cellGlobalId_r16 t => existT _ 0 t
  | RA_Report_r16__cellId_r16__pci_arfcn_r16 t => existT _ 1 t
  end.
Definition RA_Report_r16__cellId_r16__g := (fun n => typ_set (get_nth_typ RA_Report_r16__cellId_r16__list n)).
Definition RA_Report_r16__cellId_r16__F2 (y : choice RA_Report_r16__cellId_r16__list) : RA_Report_r16__cellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RA_Report_r16__cellId_r16__g n -> RA_Report_r16__cellId_r16__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => RA_Report_r16__cellId_r16__cellGlobalId_r16 t 
    | 1 => fun (t : PCI_ARFCN_NR_r16__Type) => RA_Report_r16__cellId_r16__pci_arfcn_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RA_Report_r16__cellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RA_Report_r16__cellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RA_Report_r16__cellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RA_Report_r16__cellId_r16__Type with end) n0
           end t0).

Lemma RA_Report_r16__cellId_r16__helper2 :  forall (y : RA_Report_r16__cellId_r16__Type), RA_Report_r16__cellId_r16__cond y -> choice_cond RA_Report_r16__cellId_r16__list (RA_Report_r16__cellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RA_Report_r16__cellId_r16__helper3 :  forall (y : RA_Report_r16__cellId_r16__Type), RA_Report_r16__cellId_r16__F2 (RA_Report_r16__cellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RA_Report_r16__cellId_r16__helper4 : (forall b : choice RA_Report_r16__cellId_r16__list, choice_cond RA_Report_r16__cellId_r16__list b -> RA_Report_r16__cellId_r16__cond (RA_Report_r16__cellId_r16__F2 b) /\ RA_Report_r16__cellId_r16__F1 (RA_Report_r16__cellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RA_Report_r16__cellId_r16__F1 RA_Report_r16__cellId_r16__F2.
Definition RA_Report_r16__cellId_r16__Format : T_Format RA_Report_r16__cellId_r16__Type RA_Report_r16__cellId_r16__cond :=
  (* Eval compute in *) proj2_format RA_Report_r16__cellId_r16__cond RA_Report_r16__cellId_r16__list__Format RA_Report_r16__cellId_r16__F1 RA_Report_r16__cellId_r16__F2 RA_Report_r16__cellId_r16__helper2 RA_Report_r16__cellId_r16__helper3 RA_Report_r16__cellId_r16__helper4.
Opaque RA_Report_r16__cellId_r16__cond RA_Report_r16__cellId_r16__Format.

Definition RA_Report_r16__raPurpose_r16__Format : T_Format RA_Report_r16__raPurpose_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_Report_r16__raPurpose_r16__nat__Format RA_Report_r16__raPurpose_r16__F1 RA_Report_r16__raPurpose_r16__F2 RA_Report_r16__raPurpose_r16__F1F2 RA_Report_r16__raPurpose_r16__F2F1.

Opaque RA_Report_r16__raPurpose_r16__cond RA_Report_r16__raPurpose_r16__Format.


Definition RA_Report_r16__ext0O__Format_Type := Eval cbn in seq_format_prod RA_Report_r16__ext0O__list.
Definition RA_Report_r16__ext0O__Format_list : RA_Report_r16__ext0O__Format_Type :=
  (CGI_Info_Logging_r16__Format, unit_format).
Definition RA_Report_r16__ext0O__list__Format := (*Eval compute in *) seq_format RA_Report_r16__ext0O__list RA_Report_r16__ext0O__Format_list.
Definition RA_Report_r16__ext0O__F1 z :=
  (RA_Report_r16__ext0O__spCellID_r17 z, tt).
Definition RA_Report_r16__ext0O__F2 (y : seq_type RA_Report_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RA_Report_r16__ext0O__Type i0
  end.
Lemma RA_Report_r16__ext0O__F1F2_cond (z : RA_Report_r16__ext0O__Type)
  : RA_Report_r16__ext0O__cond z ->
  (seq_cond RA_Report_r16__ext0O__list (RA_Report_r16__ext0O__F1 z)).
intro H. unfold RA_Report_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma RA_Report_r16__ext0O__F1F2_cond2 (z : RA_Report_r16__ext0O__Type)
 : RA_Report_r16__ext0O__F2 (RA_Report_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RA_Report_r16__ext0O__F2F1_cond (y : seq_type RA_Report_r16__ext0O__list)
  : seq_cond RA_Report_r16__ext0O__list y ->
 (RA_Report_r16__ext0O__cond (RA_Report_r16__ext0O__F2 y)) /\  RA_Report_r16__ext0O__F1 (RA_Report_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RA_Report_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold RA_Report_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RA_Report_r16__ext0O__Format : T_Format RA_Report_r16__ext0O__Type RA_Report_r16__ext0O__cond :=
        proj2_format  RA_Report_r16__ext0O__cond RA_Report_r16__ext0O__list__Format
    RA_Report_r16__ext0O__F1 RA_Report_r16__ext0O__F2 RA_Report_r16__ext0O__F1F2_cond  RA_Report_r16__ext0O__F1F2_cond2 RA_Report_r16__ext0O__F2F1_cond.
Opaque RA_Report_r16__ext0O__cond RA_Report_r16__ext0O__Format.

Definition RA_Report_r16__ext0__check_all_none (b : RA_Report_r16__ext0O__Type) : bool :=
match b with 
  | make__RA_Report_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RA_Report_r16__ext0__Format : T_Format RA_Report_r16__ext0__Type RA_Report_r16__ext0__cond :=
  restrict_add_format RA_Report_r16__ext0__check_all_none RA_Report_r16__ext0O__Format.

Opaque RA_Report_r16__ext0__cond RA_Report_r16__ext0__Format.


Definition RA_Report_r16__root_Format_Type := Eval cbn in seq_format_prod RA_Report_r16__root_list.
Definition RA_Report_r16__root_Format_list : RA_Report_r16__root_Format_Type :=
  (RA_Report_r16__cellId_r16__Format, (RA_InformationCommon_r16__Format, (RA_Report_r16__raPurpose_r16__Format, unit_format))).

Definition RA_Report_r16__ext_Format_Type := Eval cbn in get_formats RA_Report_r16__ext_list.
Definition RA_Report_r16__ext_Format_list : RA_Report_r16__ext_Format_Type :=
  (RA_Report_r16__ext0__Format, unit__Format).

Definition RA_Report_r16__list_type : Set := (seq_type RA_Report_r16__root_list) * (seq_ext_type RA_Report_r16__ext_list).
Definition RA_Report_r16__list_cond (z : RA_Report_r16__list_type) : Prop :=
        (seq_cond RA_Report_r16__root_list (fst z)) /\ (seq_ext_cond RA_Report_r16__ext_list (snd z)).
Definition RA_Report_r16__list_format : T_Format RA_Report_r16__list_type RA_Report_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RA_Report_r16__root_list RA_Report_r16__root_Format_list RA_Report_r16__ext_list RA_Report_r16__ext_Format_list.

Opaque RA_Report_r16__list_format.
Definition RA_Report_r16__F1 (z : RA_Report_r16__Type) : RA_Report_r16__list_type :=
  (((RA_Report_r16__cellId_r16 z, (RA_Report_r16__ra_InformationCommon_r16 z, (RA_Report_r16__raPurpose_r16 z, tt)))), (
(RA_Report_r16__ext0 z, tt))).
Definition RA_Report_r16__F2 (y : RA_Report_r16__list_type) : RA_Report_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__RA_Report_r16__Type j0 j1 j2 i0
  end.
Definition RA_Report_r16__helper1 : (forall a : RA_Report_r16__Type, RA_Report_r16__cond a -> RA_Report_r16__list_cond (RA_Report_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RA_Report_r16__helper2 : (forall a : RA_Report_r16__Type, RA_Report_r16__F2 (RA_Report_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RA_Report_r16__helper3 : (forall b : RA_Report_r16__list_type, RA_Report_r16__list_cond b -> RA_Report_r16__cond (RA_Report_r16__F2 b) /\ RA_Report_r16__F1 (RA_Report_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RA_Report_r16__cond, RA_Report_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RA_Report_r16__Format : T_Format RA_Report_r16__Type RA_Report_r16__cond :=
 proj2_format RA_Report_r16__cond RA_Report_r16__list_format  RA_Report_r16__F1 RA_Report_r16__F2 RA_Report_r16__helper1 RA_Report_r16__helper2 RA_Report_r16__helper3.

Opaque RA_Report_r16__cond RA_Report_r16__Format.

