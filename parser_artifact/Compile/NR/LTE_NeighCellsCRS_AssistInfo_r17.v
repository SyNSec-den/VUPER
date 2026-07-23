Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Type : Set :=
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n6
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n15
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n25
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n50
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n75
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n100
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__spare2
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__spare1
.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__cond := (fun (_ : LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Type) => True).
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__nat__helper.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1 t :=
  match t with
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n6 => 0
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n15 => 1
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n25 => 2
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n50 => 3
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n75 => 4
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n100 => 5
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__spare2 => 6
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__spare1 => 7
  end.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F2 n :=
  match n with
  | 0 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n6
  | 1 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n15
  | 2 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n25
  | 3 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n50
  | 4 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n75
  | 5 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n100
  | 6 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__spare2
  | 7 => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__spare1
  | _ => LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__n6
  end.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1F2 : forall x : LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Type, (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1 x <= 7) /\ LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F2 (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1 x) = x. imp_solve. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F2F1 : forall (y : nat) (H : y <= 7), LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1 (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F2 y) = y. enum_solve H y. Qed.

Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__helper1 : (0 <= 16383)%Z.  lia. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__helper2 : to_bit_sz (Z.to_nat (16383 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16383 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__Type := Z.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__cond := (fun z => (0 <= z <= 16383)%Z).
Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Inductive LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Type : Set :=
 | LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__enabled
.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__cond := (fun (_ : LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Type) => True).
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__nat__helper.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1 t :=
  match t with
  | LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__enabled => 0
  end.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F2 n :=
  match n with
  | 0 => LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__enabled
  | _ => LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__enabled
  end.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1F2 : forall x : LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Type, (LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1 x <= 0) /\ LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F2 (LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1 x) = x. imp_solve. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F2F1 : forall (y : nat) (H : y <= 0), LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1 (LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.EUTRA_MBSFN_SubframeConfigList.

Opaque EUTRA_MBSFN_SubframeConfigList__cond EUTRA_MBSFN_SubframeConfigList__Format.

Inductive LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Type : Set :=
 | LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n1
 | LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n2
 | LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n4
.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__cond := (fun (_ : LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Type) => True).
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__nat__helper.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1 t :=
  match t with
  | LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n1 => 0
  | LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n2 => 1
  | LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n4 => 2
  end.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F2 n :=
  match n with
  | 0 => LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n1
  | 1 => LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n2
  | 2 => LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n4
  | _ => LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__n1
  end.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1F2 : forall x : LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Type, (LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1 x <= 2) /\ LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F2 (LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1 x) = x. imp_solve. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F2F1 : forall (y : nat) (H : y <= 2), LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1 (LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F2 y) = y. enum_solve H y. Qed.

Inductive LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Type : Set :=
 | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n0
 | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n1
 | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n2
 | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n3
 | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n4
 | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n5
.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__cond := (fun (_ : LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Type) => True).
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__nat__helper.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1 t :=
  match t with
  | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n0 => 0
  | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n1 => 1
  | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n2 => 2
  | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n3 => 3
  | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n4 => 4
  | LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n5 => 5
  end.
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F2 n :=
  match n with
  | 0 => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n0
  | 1 => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n1
  | 2 => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n2
  | 3 => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n3
  | 4 => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n4
  | 5 => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n5
  | _ => LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__n0
  end.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1F2 : forall x : LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Type, (LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1 x <= 5) /\ LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F2 (LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1 x) = x. imp_solve. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F2F1 : forall (y : nat) (H : y <= 5), LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1 (LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F2 y) = y. enum_solve H y. Qed.

Record LTE_NeighCellsCRS_AssistInfo_r17__Type : Set :=
  make__LTE_NeighCellsCRS_AssistInfo_r17__Type {
    LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17 : option LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Type ;
    LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17 : option Z ;
    LTE_NeighCellsCRS_AssistInfo_r17__neighCellId_r17 : option EUTRA_PhysCellId__Type ;
    LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17 : option LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Type ;
    LTE_NeighCellsCRS_AssistInfo_r17__neighMBSFN_SubframeConfigList_r17 : option EUTRA_MBSFN_SubframeConfigList__Type ;
    LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17 : option LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Type ;
    LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17 : option LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Type ;
}.
Definition LTE_NeighCellsCRS_AssistInfo_r17__list := (
 Opt LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Type LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__cond ::
 Opt Z LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__cond ::
 Opt EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Opt LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Type LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__cond ::
 Opt EUTRA_MBSFN_SubframeConfigList__Type EUTRA_MBSFN_SubframeConfigList__cond ::
 Opt LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Type LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__cond ::
 Opt LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Type LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__cond ::
 nil).
Definition LTE_NeighCellsCRS_AssistInfo_r17__cond z := 
  opt_cond LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17 z) /\
  opt_cond LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17 z) /\
  opt_cond EUTRA_PhysCellId__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighCellId_r17 z) /\
  opt_cond LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17 z) /\
  opt_cond EUTRA_MBSFN_SubframeConfigList__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighMBSFN_SubframeConfigList_r17 z) /\
  opt_cond LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17 z) /\
  opt_cond LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__cond (LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17 z) /\
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
Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Format : T_Format LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__nat__Format LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1 LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F2 LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F1F2 LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__F2F1.

Opaque LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Format.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__Format : T_Format Z LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__cond :=
 ranged_int_format (0) (16383) LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__helper1 LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__helper2.

Opaque LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__Format.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Format : T_Format LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__nat__Format LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1 LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F2 LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F1F2 LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__F2F1.

Opaque LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Format.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Format : T_Format LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__nat__Format LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1 LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F2 LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F1F2 LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__F2F1.

Opaque LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Format.

Definition LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Format : T_Format LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__nat__Format LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1 LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F2 LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F1F2 LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__F2F1.

Opaque LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Format.


Definition LTE_NeighCellsCRS_AssistInfo_r17__Format_Type := Eval cbn in seq_format_prod LTE_NeighCellsCRS_AssistInfo_r17__list.
Definition LTE_NeighCellsCRS_AssistInfo_r17__Format_list : LTE_NeighCellsCRS_AssistInfo_r17__Format_Type :=
  (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17__Format, (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17__Format, (EUTRA_PhysCellId__Format, (LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17__Format, (EUTRA_MBSFN_SubframeConfigList__Format, (LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17__Format, (LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17__Format, unit_format))))))).
Definition LTE_NeighCellsCRS_AssistInfo_r17__list__Format := (*Eval compute in *) seq_format LTE_NeighCellsCRS_AssistInfo_r17__list LTE_NeighCellsCRS_AssistInfo_r17__Format_list.
Definition LTE_NeighCellsCRS_AssistInfo_r17__F1 z :=
  (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierBandwidthDL_r17 z, (LTE_NeighCellsCRS_AssistInfo_r17__neighCarrierFreqDL_r17 z, (LTE_NeighCellsCRS_AssistInfo_r17__neighCellId_r17 z, (LTE_NeighCellsCRS_AssistInfo_r17__neighCRS_muting_r17 z, (LTE_NeighCellsCRS_AssistInfo_r17__neighMBSFN_SubframeConfigList_r17 z, (LTE_NeighCellsCRS_AssistInfo_r17__neighNrofCRS_Ports_r17 z, (LTE_NeighCellsCRS_AssistInfo_r17__neighV_Shift_r17 z, tt))))))).
Definition LTE_NeighCellsCRS_AssistInfo_r17__F2 (y : seq_type LTE_NeighCellsCRS_AssistInfo_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__LTE_NeighCellsCRS_AssistInfo_r17__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__F1F2_cond (z : LTE_NeighCellsCRS_AssistInfo_r17__Type)
  : LTE_NeighCellsCRS_AssistInfo_r17__cond z ->
  (seq_cond LTE_NeighCellsCRS_AssistInfo_r17__list (LTE_NeighCellsCRS_AssistInfo_r17__F1 z)).
intro H. unfold LTE_NeighCellsCRS_AssistInfo_r17__cond in H. simpl. auto. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__F1F2_cond2 (z : LTE_NeighCellsCRS_AssistInfo_r17__Type)
 : LTE_NeighCellsCRS_AssistInfo_r17__F2 (LTE_NeighCellsCRS_AssistInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LTE_NeighCellsCRS_AssistInfo_r17__F2F1_cond (y : seq_type LTE_NeighCellsCRS_AssistInfo_r17__list)
  : seq_cond LTE_NeighCellsCRS_AssistInfo_r17__list y ->
 (LTE_NeighCellsCRS_AssistInfo_r17__cond (LTE_NeighCellsCRS_AssistInfo_r17__F2 y)) /\  LTE_NeighCellsCRS_AssistInfo_r17__F1 (LTE_NeighCellsCRS_AssistInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LTE_NeighCellsCRS_AssistInfo_r17__cond. simpl in *. auto.
 - simpl. unfold LTE_NeighCellsCRS_AssistInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LTE_NeighCellsCRS_AssistInfo_r17__Format : T_Format LTE_NeighCellsCRS_AssistInfo_r17__Type LTE_NeighCellsCRS_AssistInfo_r17__cond :=
        proj2_format  LTE_NeighCellsCRS_AssistInfo_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__list__Format
    LTE_NeighCellsCRS_AssistInfo_r17__F1 LTE_NeighCellsCRS_AssistInfo_r17__F2 LTE_NeighCellsCRS_AssistInfo_r17__F1F2_cond  LTE_NeighCellsCRS_AssistInfo_r17__F1F2_cond2 LTE_NeighCellsCRS_AssistInfo_r17__F2F1_cond.
Opaque LTE_NeighCellsCRS_AssistInfo_r17__cond LTE_NeighCellsCRS_AssistInfo_r17__Format.

