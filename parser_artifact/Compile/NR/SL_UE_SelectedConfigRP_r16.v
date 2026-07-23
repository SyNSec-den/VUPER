Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_CBR_PriorityTxConfigList_r16.

Opaque SL_CBR_PriorityTxConfigList_r16__cond SL_CBR_PriorityTxConfigList_r16__Format.

Require Import NR.SL_Thres_RSRP_List_r16.

Opaque SL_Thres_RSRP_List_r16__cond SL_Thres_RSRP_List_r16__Format.

Inductive SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Type : Set :=
 | SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__enabled
.
Definition SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__cond := (fun (_ : SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Type) => True).
Lemma SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__nat__helper.

Definition SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1 t :=
  match t with
  | SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__enabled => 0
  end.
Definition SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F2 n :=
  match n with
  | 0 => SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__enabled
  | _ => SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__enabled
  end.
Lemma SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1F2 : forall x : SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Type, (SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1 x <= 0) /\ SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F2 (SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1 (SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Type : Set :=
 | SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n2
 | SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n3
.
Definition SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__cond := (fun (_ : SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Type) => True).
Lemma SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__nat__helper.

Definition SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1 t :=
  match t with
  | SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n2 => 0
  | SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n3 => 1
  end.
Definition SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F2 n :=
  match n with
  | 0 => SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n2
  | 1 => SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n3
  | _ => SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__n2
  end.
Lemma SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1F2 : forall x : SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Type, (SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1 x <= 1) /\ SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F2 (SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1 (SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Type : Set :=
 | SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms100
 | SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms1100
.
Definition SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__cond := (fun (_ : SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Type) => True).
Lemma SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__nat__helper.

Definition SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1 t :=
  match t with
  | SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms100 => 0
  | SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms1100 => 1
  end.
Definition SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F2 n :=
  match n with
  | 0 => SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms100
  | 1 => SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms1100
  | _ => SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__ms100
  end.
Lemma SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1F2 : forall x : SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Type, (SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1 x <= 1) /\ SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F2 (SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1 (SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_SelectionWindowList_r16.

Opaque SL_SelectionWindowList_r16__cond SL_SelectionWindowList_r16__Format.

Require Import NR.SL_ResourceReservePeriod_r16.

Opaque SL_ResourceReservePeriod_r16__cond SL_ResourceReservePeriod_r16__Format.

Definition SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Type := list SL_ResourceReservePeriod_r16__Type.

Lemma SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__helper1 : (0 <= 1 <= 16)%Z.  lia. Qed.
Lemma SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__cond (z : SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Type) :=  (1 <= Z.of_nat (length z) <= 16)%Z /\ (list_and SL_ResourceReservePeriod_r16__cond z) .

Inductive SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Type : Set :=
 | SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pscch
 | SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pssch
.
Definition SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__cond := (fun (_ : SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Type) => True).
Lemma SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__nat__helper.

Definition SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1 t :=
  match t with
  | SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pscch => 0
  | SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pssch => 1
  end.
Definition SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F2 n :=
  match n with
  | 0 => SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pscch
  | 1 => SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pssch
  | _ => SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__pscch
  end.
Lemma SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1F2 : forall x : SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Type, (SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1 x <= 1) /\ SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F2 (SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1 (SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_CBR_PriorityTxConfigList_v1650.

Opaque SL_CBR_PriorityTxConfigList_v1650__cond SL_CBR_PriorityTxConfigList_v1650__Format.

Record SL_UE_SelectedConfigRP_r16__ext0O__Type : Set :=
  make__SL_UE_SelectedConfigRP_r16__ext0O__Type {
    SL_UE_SelectedConfigRP_r16__ext0O__sl_CBR_PriorityTxConfigList_v1650 : option SL_CBR_PriorityTxConfigList_v1650__Type ;
}.
Definition SL_UE_SelectedConfigRP_r16__ext0O__list := (
 Opt SL_CBR_PriorityTxConfigList_v1650__Type SL_CBR_PriorityTxConfigList_v1650__cond ::
 nil).
Definition SL_UE_SelectedConfigRP_r16__ext0O__cond z := 
  opt_cond SL_CBR_PriorityTxConfigList_v1650__cond (SL_UE_SelectedConfigRP_r16__ext0O__sl_CBR_PriorityTxConfigList_v1650 z) /\
  True.

Definition SL_UE_SelectedConfigRP_r16__ext0__Type := SL_UE_SelectedConfigRP_r16__ext0O__Type.
Definition SL_UE_SelectedConfigRP_r16__ext0__cond := SL_UE_SelectedConfigRP_r16__ext0O__cond.

Record SL_UE_SelectedConfigRP_r16__Type : Set :=
  make__SL_UE_SelectedConfigRP_r16__Type {
    SL_UE_SelectedConfigRP_r16__sl_CBR_PriorityTxConfigList_r16 : option SL_CBR_PriorityTxConfigList_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_Thres_RSRP_List_r16 : option SL_Thres_RSRP_List_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16 : option SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16 : option SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16 : option SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_SelectionWindowList_r16 : option SL_SelectionWindowList_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16 : option SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Type ;
    SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16 : SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Type ;
    SL_UE_SelectedConfigRP_r16__ext0 : option SL_UE_SelectedConfigRP_r16__ext0__Type ;
}.
Definition SL_UE_SelectedConfigRP_r16__root_list : list seq_elem := (
 Opt SL_CBR_PriorityTxConfigList_r16__Type SL_CBR_PriorityTxConfigList_r16__cond ::
 Opt SL_Thres_RSRP_List_r16__Type SL_Thres_RSRP_List_r16__cond ::
 Opt SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Type SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__cond ::
 Opt SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Type SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__cond ::
 Opt SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Type SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__cond ::
 Opt SL_SelectionWindowList_r16__Type SL_SelectionWindowList_r16__cond ::
 Opt SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Type SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__cond ::
 Nor SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Type SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__cond ::
 nil).
Definition SL_UE_SelectedConfigRP_r16__ext_list : list typ := (
  typ_cons SL_UE_SelectedConfigRP_r16__ext0__Type SL_UE_SelectedConfigRP_r16__ext0__cond ::
  nil).
Definition SL_UE_SelectedConfigRP_r16__cond (z : SL_UE_SelectedConfigRP_r16__Type) := 
(  opt_cond SL_CBR_PriorityTxConfigList_r16__cond (SL_UE_SelectedConfigRP_r16__sl_CBR_PriorityTxConfigList_r16 z) /\
  opt_cond SL_Thres_RSRP_List_r16__cond (SL_UE_SelectedConfigRP_r16__sl_Thres_RSRP_List_r16 z) /\
  opt_cond SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__cond (SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16 z) /\
  opt_cond SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__cond (SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16 z) /\
  opt_cond SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__cond (SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16 z) /\
  opt_cond SL_SelectionWindowList_r16__cond (SL_UE_SelectedConfigRP_r16__sl_SelectionWindowList_r16 z) /\
  opt_cond SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__cond (SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16 z) /\
  SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__cond (SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16 z) /\
  True) /\ 
(  opt_cond SL_UE_SelectedConfigRP_r16__ext0__cond (SL_UE_SelectedConfigRP_r16__ext0 z) /\
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
Definition SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Format : T_Format SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__nat__Format SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1 SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F2 SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F1F2 SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__F2F1.

Opaque SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__cond SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Format.

Definition SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Format : T_Format SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__nat__Format SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1 SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F2 SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F1F2 SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__F2F1.

Opaque SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__cond SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Format.

Definition SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Format : T_Format SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__nat__Format SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1 SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F2 SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F1F2 SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__F2F1.

Opaque SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__cond SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Format.

Definition SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Format : T_Format SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Type SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__cond := seq_of_format SL_ResourceReservePeriod_r16__Format 1 16 SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__helper1 SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__helper2.

Opaque SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__cond SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Format.

Definition SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Format : T_Format SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__nat__Format SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1 SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F2 SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F1F2 SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__F2F1.

Opaque SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__cond SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Format.


Definition SL_UE_SelectedConfigRP_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SL_UE_SelectedConfigRP_r16__ext0O__list.
Definition SL_UE_SelectedConfigRP_r16__ext0O__Format_list : SL_UE_SelectedConfigRP_r16__ext0O__Format_Type :=
  (SL_CBR_PriorityTxConfigList_v1650__Format, unit_format).
Definition SL_UE_SelectedConfigRP_r16__ext0O__list__Format := (*Eval compute in *) seq_format SL_UE_SelectedConfigRP_r16__ext0O__list SL_UE_SelectedConfigRP_r16__ext0O__Format_list.
Definition SL_UE_SelectedConfigRP_r16__ext0O__F1 z :=
  (SL_UE_SelectedConfigRP_r16__ext0O__sl_CBR_PriorityTxConfigList_v1650 z, tt).
Definition SL_UE_SelectedConfigRP_r16__ext0O__F2 (y : seq_type SL_UE_SelectedConfigRP_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SL_UE_SelectedConfigRP_r16__ext0O__Type i0
  end.
Lemma SL_UE_SelectedConfigRP_r16__ext0O__F1F2_cond (z : SL_UE_SelectedConfigRP_r16__ext0O__Type)
  : SL_UE_SelectedConfigRP_r16__ext0O__cond z ->
  (seq_cond SL_UE_SelectedConfigRP_r16__ext0O__list (SL_UE_SelectedConfigRP_r16__ext0O__F1 z)).
intro H. unfold SL_UE_SelectedConfigRP_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SL_UE_SelectedConfigRP_r16__ext0O__F1F2_cond2 (z : SL_UE_SelectedConfigRP_r16__ext0O__Type)
 : SL_UE_SelectedConfigRP_r16__ext0O__F2 (SL_UE_SelectedConfigRP_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_UE_SelectedConfigRP_r16__ext0O__F2F1_cond (y : seq_type SL_UE_SelectedConfigRP_r16__ext0O__list)
  : seq_cond SL_UE_SelectedConfigRP_r16__ext0O__list y ->
 (SL_UE_SelectedConfigRP_r16__ext0O__cond (SL_UE_SelectedConfigRP_r16__ext0O__F2 y)) /\  SL_UE_SelectedConfigRP_r16__ext0O__F1 (SL_UE_SelectedConfigRP_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_UE_SelectedConfigRP_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SL_UE_SelectedConfigRP_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_UE_SelectedConfigRP_r16__ext0O__Format : T_Format SL_UE_SelectedConfigRP_r16__ext0O__Type SL_UE_SelectedConfigRP_r16__ext0O__cond :=
        proj2_format  SL_UE_SelectedConfigRP_r16__ext0O__cond SL_UE_SelectedConfigRP_r16__ext0O__list__Format
    SL_UE_SelectedConfigRP_r16__ext0O__F1 SL_UE_SelectedConfigRP_r16__ext0O__F2 SL_UE_SelectedConfigRP_r16__ext0O__F1F2_cond  SL_UE_SelectedConfigRP_r16__ext0O__F1F2_cond2 SL_UE_SelectedConfigRP_r16__ext0O__F2F1_cond.
Opaque SL_UE_SelectedConfigRP_r16__ext0O__cond SL_UE_SelectedConfigRP_r16__ext0O__Format.

Definition SL_UE_SelectedConfigRP_r16__ext0__check_all_none (b : SL_UE_SelectedConfigRP_r16__ext0O__Type) : bool :=
match b with 
  | make__SL_UE_SelectedConfigRP_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SL_UE_SelectedConfigRP_r16__ext0__Format : T_Format SL_UE_SelectedConfigRP_r16__ext0__Type SL_UE_SelectedConfigRP_r16__ext0__cond :=
  restrict_add_format SL_UE_SelectedConfigRP_r16__ext0__check_all_none SL_UE_SelectedConfigRP_r16__ext0O__Format.

Opaque SL_UE_SelectedConfigRP_r16__ext0__cond SL_UE_SelectedConfigRP_r16__ext0__Format.


Definition SL_UE_SelectedConfigRP_r16__root_Format_Type := Eval cbn in seq_format_prod SL_UE_SelectedConfigRP_r16__root_list.
Definition SL_UE_SelectedConfigRP_r16__root_Format_list : SL_UE_SelectedConfigRP_r16__root_Format_Type :=
  (SL_CBR_PriorityTxConfigList_r16__Format, (SL_Thres_RSRP_List_r16__Format, (SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16__Format, (SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16__Format, (SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16__Format, (SL_SelectionWindowList_r16__Format, (SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16__Format, (SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16__Format, unit_format)))))))).

Definition SL_UE_SelectedConfigRP_r16__ext_Format_Type := Eval cbn in get_formats SL_UE_SelectedConfigRP_r16__ext_list.
Definition SL_UE_SelectedConfigRP_r16__ext_Format_list : SL_UE_SelectedConfigRP_r16__ext_Format_Type :=
  (SL_UE_SelectedConfigRP_r16__ext0__Format, unit__Format).

Definition SL_UE_SelectedConfigRP_r16__list_type : Set := (seq_type SL_UE_SelectedConfigRP_r16__root_list) * (seq_ext_type SL_UE_SelectedConfigRP_r16__ext_list).
Definition SL_UE_SelectedConfigRP_r16__list_cond (z : SL_UE_SelectedConfigRP_r16__list_type) : Prop :=
        (seq_cond SL_UE_SelectedConfigRP_r16__root_list (fst z)) /\ (seq_ext_cond SL_UE_SelectedConfigRP_r16__ext_list (snd z)).
Definition SL_UE_SelectedConfigRP_r16__list_format : T_Format SL_UE_SelectedConfigRP_r16__list_type SL_UE_SelectedConfigRP_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_UE_SelectedConfigRP_r16__root_list SL_UE_SelectedConfigRP_r16__root_Format_list SL_UE_SelectedConfigRP_r16__ext_list SL_UE_SelectedConfigRP_r16__ext_Format_list.

Opaque SL_UE_SelectedConfigRP_r16__list_format.
Definition SL_UE_SelectedConfigRP_r16__F1 (z : SL_UE_SelectedConfigRP_r16__Type) : SL_UE_SelectedConfigRP_r16__list_type :=
  (((SL_UE_SelectedConfigRP_r16__sl_CBR_PriorityTxConfigList_r16 z, (SL_UE_SelectedConfigRP_r16__sl_Thres_RSRP_List_r16 z, (SL_UE_SelectedConfigRP_r16__sl_MultiReserveResource_r16 z, (SL_UE_SelectedConfigRP_r16__sl_MaxNumPerReserve_r16 z, (SL_UE_SelectedConfigRP_r16__sl_SensingWindow_r16 z, (SL_UE_SelectedConfigRP_r16__sl_SelectionWindowList_r16 z, (SL_UE_SelectedConfigRP_r16__sl_ResourceReservePeriodList_r16 z, (SL_UE_SelectedConfigRP_r16__sl_RS_ForSensing_r16 z, tt))))))))), (
(SL_UE_SelectedConfigRP_r16__ext0 z, tt))).
Definition SL_UE_SelectedConfigRP_r16__F2 (y : SL_UE_SelectedConfigRP_r16__list_type) : SL_UE_SelectedConfigRP_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, _))=>
    make__SL_UE_SelectedConfigRP_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 i0
  end.
Definition SL_UE_SelectedConfigRP_r16__helper1 : (forall a : SL_UE_SelectedConfigRP_r16__Type, SL_UE_SelectedConfigRP_r16__cond a -> SL_UE_SelectedConfigRP_r16__list_cond (SL_UE_SelectedConfigRP_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_UE_SelectedConfigRP_r16__helper2 : (forall a : SL_UE_SelectedConfigRP_r16__Type, SL_UE_SelectedConfigRP_r16__F2 (SL_UE_SelectedConfigRP_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_UE_SelectedConfigRP_r16__helper3 : (forall b : SL_UE_SelectedConfigRP_r16__list_type, SL_UE_SelectedConfigRP_r16__list_cond b -> SL_UE_SelectedConfigRP_r16__cond (SL_UE_SelectedConfigRP_r16__F2 b) /\ SL_UE_SelectedConfigRP_r16__F1 (SL_UE_SelectedConfigRP_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_UE_SelectedConfigRP_r16__cond, SL_UE_SelectedConfigRP_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_UE_SelectedConfigRP_r16__Format : T_Format SL_UE_SelectedConfigRP_r16__Type SL_UE_SelectedConfigRP_r16__cond :=
 proj2_format SL_UE_SelectedConfigRP_r16__cond SL_UE_SelectedConfigRP_r16__list_format  SL_UE_SelectedConfigRP_r16__F1 SL_UE_SelectedConfigRP_r16__F2 SL_UE_SelectedConfigRP_r16__helper1 SL_UE_SelectedConfigRP_r16__helper2 SL_UE_SelectedConfigRP_r16__helper3.

Opaque SL_UE_SelectedConfigRP_r16__cond SL_UE_SelectedConfigRP_r16__Format.

