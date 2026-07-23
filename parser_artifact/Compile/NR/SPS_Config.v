Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SPS_Config__periodicity__Type : Set :=
 | SPS_Config__periodicity__ms10
 | SPS_Config__periodicity__ms20
 | SPS_Config__periodicity__ms32
 | SPS_Config__periodicity__ms40
 | SPS_Config__periodicity__ms64
 | SPS_Config__periodicity__ms80
 | SPS_Config__periodicity__ms128
 | SPS_Config__periodicity__ms160
 | SPS_Config__periodicity__ms320
 | SPS_Config__periodicity__ms640
 | SPS_Config__periodicity__spare6
 | SPS_Config__periodicity__spare5
 | SPS_Config__periodicity__spare4
 | SPS_Config__periodicity__spare3
 | SPS_Config__periodicity__spare2
 | SPS_Config__periodicity__spare1
.
Definition SPS_Config__periodicity__cond := (fun (_ : SPS_Config__periodicity__Type) => True).
Lemma SPS_Config__periodicity__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SPS_Config__periodicity__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SPS_Config__periodicity__nat__helper.

Definition SPS_Config__periodicity__F1 t :=
  match t with
  | SPS_Config__periodicity__ms10 => 0
  | SPS_Config__periodicity__ms20 => 1
  | SPS_Config__periodicity__ms32 => 2
  | SPS_Config__periodicity__ms40 => 3
  | SPS_Config__periodicity__ms64 => 4
  | SPS_Config__periodicity__ms80 => 5
  | SPS_Config__periodicity__ms128 => 6
  | SPS_Config__periodicity__ms160 => 7
  | SPS_Config__periodicity__ms320 => 8
  | SPS_Config__periodicity__ms640 => 9
  | SPS_Config__periodicity__spare6 => 10
  | SPS_Config__periodicity__spare5 => 11
  | SPS_Config__periodicity__spare4 => 12
  | SPS_Config__periodicity__spare3 => 13
  | SPS_Config__periodicity__spare2 => 14
  | SPS_Config__periodicity__spare1 => 15
  end.
Definition SPS_Config__periodicity__F2 n :=
  match n with
  | 0 => SPS_Config__periodicity__ms10
  | 1 => SPS_Config__periodicity__ms20
  | 2 => SPS_Config__periodicity__ms32
  | 3 => SPS_Config__periodicity__ms40
  | 4 => SPS_Config__periodicity__ms64
  | 5 => SPS_Config__periodicity__ms80
  | 6 => SPS_Config__periodicity__ms128
  | 7 => SPS_Config__periodicity__ms160
  | 8 => SPS_Config__periodicity__ms320
  | 9 => SPS_Config__periodicity__ms640
  | 10 => SPS_Config__periodicity__spare6
  | 11 => SPS_Config__periodicity__spare5
  | 12 => SPS_Config__periodicity__spare4
  | 13 => SPS_Config__periodicity__spare3
  | 14 => SPS_Config__periodicity__spare2
  | 15 => SPS_Config__periodicity__spare1
  | _ => SPS_Config__periodicity__ms10
  end.
Lemma SPS_Config__periodicity__F1F2 : forall x : SPS_Config__periodicity__Type, (SPS_Config__periodicity__F1 x <= 15) /\ SPS_Config__periodicity__F2 (SPS_Config__periodicity__F1 x) = x. imp_solve. Qed.
Lemma SPS_Config__periodicity__F2F1 : forall (y : nat) (H : y <= 15), SPS_Config__periodicity__F1 (SPS_Config__periodicity__F2 y) = y. enum_solve H y. Qed.

Lemma SPS_Config__nrofHARQ_Processes__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SPS_Config__nrofHARQ_Processes__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__nrofHARQ_Processes__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__nrofHARQ_Processes__Type := Z.
Definition SPS_Config__nrofHARQ_Processes__cond := (fun z => (1 <= z <= 8)%Z).
Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Inductive SPS_Config__mcs_Table__Type : Set :=
 | SPS_Config__mcs_Table__qam64LowSE
.
Definition SPS_Config__mcs_Table__cond := (fun (_ : SPS_Config__mcs_Table__Type) => True).
Lemma SPS_Config__mcs_Table__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SPS_Config__mcs_Table__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SPS_Config__mcs_Table__nat__helper.

Definition SPS_Config__mcs_Table__F1 t :=
  match t with
  | SPS_Config__mcs_Table__qam64LowSE => 0
  end.
Definition SPS_Config__mcs_Table__F2 n :=
  match n with
  | 0 => SPS_Config__mcs_Table__qam64LowSE
  | _ => SPS_Config__mcs_Table__qam64LowSE
  end.
Lemma SPS_Config__mcs_Table__F1F2 : forall x : SPS_Config__mcs_Table__Type, (SPS_Config__mcs_Table__F1 x <= 0) /\ SPS_Config__mcs_Table__F2 (SPS_Config__mcs_Table__F1 x) = x. imp_solve. Qed.
Lemma SPS_Config__mcs_Table__F2F1 : forall (y : nat) (H : y <= 0), SPS_Config__mcs_Table__F1 (SPS_Config__mcs_Table__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SPS_ConfigIndex_r16.

Opaque SPS_ConfigIndex_r16__cond SPS_ConfigIndex_r16__Format.

Lemma SPS_Config__ext0O__harq_ProcID_Offset_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SPS_Config__ext0O__harq_ProcID_Offset_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext0O__harq_ProcID_Offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext0O__harq_ProcID_Offset_r16__Type := Z.
Definition SPS_Config__ext0O__harq_ProcID_Offset_r16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma SPS_Config__ext0O__periodicityExt_r16__helper1 : (1 <= 5120)%Z.  lia. Qed.
Lemma SPS_Config__ext0O__periodicityExt_r16__helper2 : to_bit_sz (Z.to_nat (5120 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5120 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext0O__periodicityExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext0O__periodicityExt_r16__Type := Z.
Definition SPS_Config__ext0O__periodicityExt_r16__cond := (fun z => (1 <= z <= 5120)%Z).
Lemma SPS_Config__ext0O__harq_CodebookID_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma SPS_Config__ext0O__harq_CodebookID_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext0O__harq_CodebookID_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext0O__harq_CodebookID_r16__Type := Z.
Definition SPS_Config__ext0O__harq_CodebookID_r16__cond := (fun z => (1 <= z <= 2)%Z).
Inductive SPS_Config__ext0O__pdsch_AggregationFactor_r16__Type : Set :=
 | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n1
 | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n2
 | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n4
 | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n8
.
Definition SPS_Config__ext0O__pdsch_AggregationFactor_r16__cond := (fun (_ : SPS_Config__ext0O__pdsch_AggregationFactor_r16__Type) => True).
Lemma SPS_Config__ext0O__pdsch_AggregationFactor_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SPS_Config__ext0O__pdsch_AggregationFactor_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SPS_Config__ext0O__pdsch_AggregationFactor_r16__nat__helper.

Definition SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1 t :=
  match t with
  | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n1 => 0
  | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n2 => 1
  | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n4 => 2
  | SPS_Config__ext0O__pdsch_AggregationFactor_r16__n8 => 3
  end.
Definition SPS_Config__ext0O__pdsch_AggregationFactor_r16__F2 n :=
  match n with
  | 0 => SPS_Config__ext0O__pdsch_AggregationFactor_r16__n1
  | 1 => SPS_Config__ext0O__pdsch_AggregationFactor_r16__n2
  | 2 => SPS_Config__ext0O__pdsch_AggregationFactor_r16__n4
  | 3 => SPS_Config__ext0O__pdsch_AggregationFactor_r16__n8
  | _ => SPS_Config__ext0O__pdsch_AggregationFactor_r16__n1
  end.
Lemma SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1F2 : forall x : SPS_Config__ext0O__pdsch_AggregationFactor_r16__Type, (SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1 x <= 3) /\ SPS_Config__ext0O__pdsch_AggregationFactor_r16__F2 (SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1 x) = x. imp_solve. Qed.
Lemma SPS_Config__ext0O__pdsch_AggregationFactor_r16__F2F1 : forall (y : nat) (H : y <= 3), SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1 (SPS_Config__ext0O__pdsch_AggregationFactor_r16__F2 y) = y. enum_solve H y. Qed.

Record SPS_Config__ext0O__Type : Set :=
  make__SPS_Config__ext0O__Type {
    SPS_Config__ext0O__sps_ConfigIndex_r16 : option SPS_ConfigIndex_r16__Type ;
    SPS_Config__ext0O__harq_ProcID_Offset_r16 : option Z ;
    SPS_Config__ext0O__periodicityExt_r16 : option Z ;
    SPS_Config__ext0O__harq_CodebookID_r16 : option Z ;
    SPS_Config__ext0O__pdsch_AggregationFactor_r16 : option SPS_Config__ext0O__pdsch_AggregationFactor_r16__Type ;
}.
Definition SPS_Config__ext0O__list := (
 Opt SPS_ConfigIndex_r16__Type SPS_ConfigIndex_r16__cond ::
 Opt Z SPS_Config__ext0O__harq_ProcID_Offset_r16__cond ::
 Opt Z SPS_Config__ext0O__periodicityExt_r16__cond ::
 Opt Z SPS_Config__ext0O__harq_CodebookID_r16__cond ::
 Opt SPS_Config__ext0O__pdsch_AggregationFactor_r16__Type SPS_Config__ext0O__pdsch_AggregationFactor_r16__cond ::
 nil).
Definition SPS_Config__ext0O__cond z := 
  opt_cond SPS_ConfigIndex_r16__cond (SPS_Config__ext0O__sps_ConfigIndex_r16 z) /\
  opt_cond SPS_Config__ext0O__harq_ProcID_Offset_r16__cond (SPS_Config__ext0O__harq_ProcID_Offset_r16 z) /\
  opt_cond SPS_Config__ext0O__periodicityExt_r16__cond (SPS_Config__ext0O__periodicityExt_r16 z) /\
  opt_cond SPS_Config__ext0O__harq_CodebookID_r16__cond (SPS_Config__ext0O__harq_CodebookID_r16 z) /\
  opt_cond SPS_Config__ext0O__pdsch_AggregationFactor_r16__cond (SPS_Config__ext0O__pdsch_AggregationFactor_r16 z) /\
  True.

Definition SPS_Config__ext0__Type := SPS_Config__ext0O__Type.
Definition SPS_Config__ext0__cond := SPS_Config__ext0O__cond.

Lemma SPS_Config__ext1O__sps_HARQ_Deferral_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma SPS_Config__ext1O__sps_HARQ_Deferral_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext1O__sps_HARQ_Deferral_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext1O__sps_HARQ_Deferral_r17__Type := Z.
Definition SPS_Config__ext1O__sps_HARQ_Deferral_r17__cond := (fun z => (1 <= z <= 32)%Z).
Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Lemma SPS_Config__ext1O__periodicityExt_r17__helper1 : (1 <= 40960)%Z.  lia. Qed.
Lemma SPS_Config__ext1O__periodicityExt_r17__helper2 : to_bit_sz (Z.to_nat (40960 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40960 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext1O__periodicityExt_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext1O__periodicityExt_r17__Type := Z.
Definition SPS_Config__ext1O__periodicityExt_r17__cond := (fun z => (1 <= z <= 40960)%Z).
Lemma SPS_Config__ext1O__nrofHARQ_Processes_v1710__helper1 : (9 <= 32)%Z.  lia. Qed.
Lemma SPS_Config__ext1O__nrofHARQ_Processes_v1710__helper2 : to_bit_sz (Z.to_nat (32 - 9)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 9))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext1O__nrofHARQ_Processes_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext1O__nrofHARQ_Processes_v1710__Type := Z.
Definition SPS_Config__ext1O__nrofHARQ_Processes_v1710__cond := (fun z => (9 <= z <= 32)%Z).
Lemma SPS_Config__ext1O__harq_ProcID_Offset_v1700__helper1 : (16 <= 31)%Z.  lia. Qed.
Lemma SPS_Config__ext1O__harq_ProcID_Offset_v1700__helper2 : to_bit_sz (Z.to_nat (31 - 16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 16))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_Config__ext1O__harq_ProcID_Offset_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_Config__ext1O__harq_ProcID_Offset_v1700__Type := Z.
Definition SPS_Config__ext1O__harq_ProcID_Offset_v1700__cond := (fun z => (16 <= z <= 31)%Z).
Record SPS_Config__ext1O__Type : Set :=
  make__SPS_Config__ext1O__Type {
    SPS_Config__ext1O__sps_HARQ_Deferral_r17 : option Z ;
    SPS_Config__ext1O__n1PUCCH_AN_PUCCHsSCell_r17 : option PUCCH_ResourceId__Type ;
    SPS_Config__ext1O__periodicityExt_r17 : option Z ;
    SPS_Config__ext1O__nrofHARQ_Processes_v1710 : option Z ;
    SPS_Config__ext1O__harq_ProcID_Offset_v1700 : option Z ;
}.
Definition SPS_Config__ext1O__list := (
 Opt Z SPS_Config__ext1O__sps_HARQ_Deferral_r17__cond ::
 Opt PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 Opt Z SPS_Config__ext1O__periodicityExt_r17__cond ::
 Opt Z SPS_Config__ext1O__nrofHARQ_Processes_v1710__cond ::
 Opt Z SPS_Config__ext1O__harq_ProcID_Offset_v1700__cond ::
 nil).
Definition SPS_Config__ext1O__cond z := 
  opt_cond SPS_Config__ext1O__sps_HARQ_Deferral_r17__cond (SPS_Config__ext1O__sps_HARQ_Deferral_r17 z) /\
  opt_cond PUCCH_ResourceId__cond (SPS_Config__ext1O__n1PUCCH_AN_PUCCHsSCell_r17 z) /\
  opt_cond SPS_Config__ext1O__periodicityExt_r17__cond (SPS_Config__ext1O__periodicityExt_r17 z) /\
  opt_cond SPS_Config__ext1O__nrofHARQ_Processes_v1710__cond (SPS_Config__ext1O__nrofHARQ_Processes_v1710 z) /\
  opt_cond SPS_Config__ext1O__harq_ProcID_Offset_v1700__cond (SPS_Config__ext1O__harq_ProcID_Offset_v1700 z) /\
  True.

Definition SPS_Config__ext1__Type := SPS_Config__ext1O__Type.
Definition SPS_Config__ext1__cond := SPS_Config__ext1O__cond.

Record SPS_Config__Type : Set :=
  make__SPS_Config__Type {
    SPS_Config__periodicity : SPS_Config__periodicity__Type ;
    SPS_Config__nrofHARQ_Processes : Z ;
    SPS_Config__n1PUCCH_AN : option PUCCH_ResourceId__Type ;
    SPS_Config__mcs_Table : option SPS_Config__mcs_Table__Type ;
    SPS_Config__ext0 : option SPS_Config__ext0__Type ;
    SPS_Config__ext1 : option SPS_Config__ext1__Type ;
}.
Definition SPS_Config__root_list : list seq_elem := (
 Nor SPS_Config__periodicity__Type SPS_Config__periodicity__cond ::
 Nor Z SPS_Config__nrofHARQ_Processes__cond ::
 Opt PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 Opt SPS_Config__mcs_Table__Type SPS_Config__mcs_Table__cond ::
 nil).
Definition SPS_Config__ext_list : list typ := (
  typ_cons SPS_Config__ext0__Type SPS_Config__ext0__cond ::
  typ_cons SPS_Config__ext1__Type SPS_Config__ext1__cond ::
  nil).
Definition SPS_Config__cond (z : SPS_Config__Type) := 
(  SPS_Config__periodicity__cond (SPS_Config__periodicity z) /\
  SPS_Config__nrofHARQ_Processes__cond (SPS_Config__nrofHARQ_Processes z) /\
  opt_cond PUCCH_ResourceId__cond (SPS_Config__n1PUCCH_AN z) /\
  opt_cond SPS_Config__mcs_Table__cond (SPS_Config__mcs_Table z) /\
  True) /\ 
(  opt_cond SPS_Config__ext0__cond (SPS_Config__ext0 z) /\
  opt_cond SPS_Config__ext1__cond (SPS_Config__ext1 z) /\
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
Definition SPS_Config__periodicity__Format : T_Format SPS_Config__periodicity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SPS_Config__periodicity__nat__Format SPS_Config__periodicity__F1 SPS_Config__periodicity__F2 SPS_Config__periodicity__F1F2 SPS_Config__periodicity__F2F1.

Opaque SPS_Config__periodicity__cond SPS_Config__periodicity__Format.

Definition SPS_Config__nrofHARQ_Processes__Format : T_Format Z SPS_Config__nrofHARQ_Processes__cond :=
 ranged_int_format (1) (8) SPS_Config__nrofHARQ_Processes__helper1 SPS_Config__nrofHARQ_Processes__helper2.

Opaque SPS_Config__nrofHARQ_Processes__cond SPS_Config__nrofHARQ_Processes__Format.

Definition SPS_Config__mcs_Table__Format : T_Format SPS_Config__mcs_Table__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SPS_Config__mcs_Table__nat__Format SPS_Config__mcs_Table__F1 SPS_Config__mcs_Table__F2 SPS_Config__mcs_Table__F1F2 SPS_Config__mcs_Table__F2F1.

Opaque SPS_Config__mcs_Table__cond SPS_Config__mcs_Table__Format.

Definition SPS_Config__ext0O__harq_ProcID_Offset_r16__Format : T_Format Z SPS_Config__ext0O__harq_ProcID_Offset_r16__cond :=
 ranged_int_format (0) (15) SPS_Config__ext0O__harq_ProcID_Offset_r16__helper1 SPS_Config__ext0O__harq_ProcID_Offset_r16__helper2.

Opaque SPS_Config__ext0O__harq_ProcID_Offset_r16__cond SPS_Config__ext0O__harq_ProcID_Offset_r16__Format.

Definition SPS_Config__ext0O__periodicityExt_r16__Format : T_Format Z SPS_Config__ext0O__periodicityExt_r16__cond :=
 ranged_int_format (1) (5120) SPS_Config__ext0O__periodicityExt_r16__helper1 SPS_Config__ext0O__periodicityExt_r16__helper2.

Opaque SPS_Config__ext0O__periodicityExt_r16__cond SPS_Config__ext0O__periodicityExt_r16__Format.

Definition SPS_Config__ext0O__harq_CodebookID_r16__Format : T_Format Z SPS_Config__ext0O__harq_CodebookID_r16__cond :=
 ranged_int_format (1) (2) SPS_Config__ext0O__harq_CodebookID_r16__helper1 SPS_Config__ext0O__harq_CodebookID_r16__helper2.

Opaque SPS_Config__ext0O__harq_CodebookID_r16__cond SPS_Config__ext0O__harq_CodebookID_r16__Format.

Definition SPS_Config__ext0O__pdsch_AggregationFactor_r16__Format : T_Format SPS_Config__ext0O__pdsch_AggregationFactor_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SPS_Config__ext0O__pdsch_AggregationFactor_r16__nat__Format SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1 SPS_Config__ext0O__pdsch_AggregationFactor_r16__F2 SPS_Config__ext0O__pdsch_AggregationFactor_r16__F1F2 SPS_Config__ext0O__pdsch_AggregationFactor_r16__F2F1.

Opaque SPS_Config__ext0O__pdsch_AggregationFactor_r16__cond SPS_Config__ext0O__pdsch_AggregationFactor_r16__Format.


Definition SPS_Config__ext0O__Format_Type := Eval cbn in seq_format_prod SPS_Config__ext0O__list.
Definition SPS_Config__ext0O__Format_list : SPS_Config__ext0O__Format_Type :=
  (SPS_ConfigIndex_r16__Format, (SPS_Config__ext0O__harq_ProcID_Offset_r16__Format, (SPS_Config__ext0O__periodicityExt_r16__Format, (SPS_Config__ext0O__harq_CodebookID_r16__Format, (SPS_Config__ext0O__pdsch_AggregationFactor_r16__Format, unit_format))))).
Definition SPS_Config__ext0O__list__Format := (*Eval compute in *) seq_format SPS_Config__ext0O__list SPS_Config__ext0O__Format_list.
Definition SPS_Config__ext0O__F1 z :=
  (SPS_Config__ext0O__sps_ConfigIndex_r16 z, (SPS_Config__ext0O__harq_ProcID_Offset_r16 z, (SPS_Config__ext0O__periodicityExt_r16 z, (SPS_Config__ext0O__harq_CodebookID_r16 z, (SPS_Config__ext0O__pdsch_AggregationFactor_r16 z, tt))))).
Definition SPS_Config__ext0O__F2 (y : seq_type SPS_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SPS_Config__ext0O__Type i0 i1 i2 i3 i4
  end.
Lemma SPS_Config__ext0O__F1F2_cond (z : SPS_Config__ext0O__Type)
  : SPS_Config__ext0O__cond z ->
  (seq_cond SPS_Config__ext0O__list (SPS_Config__ext0O__F1 z)).
intro H. unfold SPS_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma SPS_Config__ext0O__F1F2_cond2 (z : SPS_Config__ext0O__Type)
 : SPS_Config__ext0O__F2 (SPS_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SPS_Config__ext0O__F2F1_cond (y : seq_type SPS_Config__ext0O__list)
  : seq_cond SPS_Config__ext0O__list y ->
 (SPS_Config__ext0O__cond (SPS_Config__ext0O__F2 y)) /\  SPS_Config__ext0O__F1 (SPS_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SPS_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold SPS_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SPS_Config__ext0O__Format : T_Format SPS_Config__ext0O__Type SPS_Config__ext0O__cond :=
        proj2_format  SPS_Config__ext0O__cond SPS_Config__ext0O__list__Format
    SPS_Config__ext0O__F1 SPS_Config__ext0O__F2 SPS_Config__ext0O__F1F2_cond  SPS_Config__ext0O__F1F2_cond2 SPS_Config__ext0O__F2F1_cond.
Opaque SPS_Config__ext0O__cond SPS_Config__ext0O__Format.

Definition SPS_Config__ext0__check_all_none (b : SPS_Config__ext0O__Type) : bool :=
match b with 
  | make__SPS_Config__ext0O__Type None None None None None  => false 
  | _ => true 
 end.
Definition SPS_Config__ext0__Format : T_Format SPS_Config__ext0__Type SPS_Config__ext0__cond :=
  restrict_add_format SPS_Config__ext0__check_all_none SPS_Config__ext0O__Format.

Opaque SPS_Config__ext0__cond SPS_Config__ext0__Format.

Definition SPS_Config__ext1O__sps_HARQ_Deferral_r17__Format : T_Format Z SPS_Config__ext1O__sps_HARQ_Deferral_r17__cond :=
 ranged_int_format (1) (32) SPS_Config__ext1O__sps_HARQ_Deferral_r17__helper1 SPS_Config__ext1O__sps_HARQ_Deferral_r17__helper2.

Opaque SPS_Config__ext1O__sps_HARQ_Deferral_r17__cond SPS_Config__ext1O__sps_HARQ_Deferral_r17__Format.

Definition SPS_Config__ext1O__periodicityExt_r17__Format : T_Format Z SPS_Config__ext1O__periodicityExt_r17__cond :=
 ranged_int_format (1) (40960) SPS_Config__ext1O__periodicityExt_r17__helper1 SPS_Config__ext1O__periodicityExt_r17__helper2.

Opaque SPS_Config__ext1O__periodicityExt_r17__cond SPS_Config__ext1O__periodicityExt_r17__Format.

Definition SPS_Config__ext1O__nrofHARQ_Processes_v1710__Format : T_Format Z SPS_Config__ext1O__nrofHARQ_Processes_v1710__cond :=
 ranged_int_format (9) (32) SPS_Config__ext1O__nrofHARQ_Processes_v1710__helper1 SPS_Config__ext1O__nrofHARQ_Processes_v1710__helper2.

Opaque SPS_Config__ext1O__nrofHARQ_Processes_v1710__cond SPS_Config__ext1O__nrofHARQ_Processes_v1710__Format.

Definition SPS_Config__ext1O__harq_ProcID_Offset_v1700__Format : T_Format Z SPS_Config__ext1O__harq_ProcID_Offset_v1700__cond :=
 ranged_int_format (16) (31) SPS_Config__ext1O__harq_ProcID_Offset_v1700__helper1 SPS_Config__ext1O__harq_ProcID_Offset_v1700__helper2.

Opaque SPS_Config__ext1O__harq_ProcID_Offset_v1700__cond SPS_Config__ext1O__harq_ProcID_Offset_v1700__Format.


Definition SPS_Config__ext1O__Format_Type := Eval cbn in seq_format_prod SPS_Config__ext1O__list.
Definition SPS_Config__ext1O__Format_list : SPS_Config__ext1O__Format_Type :=
  (SPS_Config__ext1O__sps_HARQ_Deferral_r17__Format, (PUCCH_ResourceId__Format, (SPS_Config__ext1O__periodicityExt_r17__Format, (SPS_Config__ext1O__nrofHARQ_Processes_v1710__Format, (SPS_Config__ext1O__harq_ProcID_Offset_v1700__Format, unit_format))))).
Definition SPS_Config__ext1O__list__Format := (*Eval compute in *) seq_format SPS_Config__ext1O__list SPS_Config__ext1O__Format_list.
Definition SPS_Config__ext1O__F1 z :=
  (SPS_Config__ext1O__sps_HARQ_Deferral_r17 z, (SPS_Config__ext1O__n1PUCCH_AN_PUCCHsSCell_r17 z, (SPS_Config__ext1O__periodicityExt_r17 z, (SPS_Config__ext1O__nrofHARQ_Processes_v1710 z, (SPS_Config__ext1O__harq_ProcID_Offset_v1700 z, tt))))).
Definition SPS_Config__ext1O__F2 (y : seq_type SPS_Config__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SPS_Config__ext1O__Type i0 i1 i2 i3 i4
  end.
Lemma SPS_Config__ext1O__F1F2_cond (z : SPS_Config__ext1O__Type)
  : SPS_Config__ext1O__cond z ->
  (seq_cond SPS_Config__ext1O__list (SPS_Config__ext1O__F1 z)).
intro H. unfold SPS_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma SPS_Config__ext1O__F1F2_cond2 (z : SPS_Config__ext1O__Type)
 : SPS_Config__ext1O__F2 (SPS_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SPS_Config__ext1O__F2F1_cond (y : seq_type SPS_Config__ext1O__list)
  : seq_cond SPS_Config__ext1O__list y ->
 (SPS_Config__ext1O__cond (SPS_Config__ext1O__F2 y)) /\  SPS_Config__ext1O__F1 (SPS_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SPS_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold SPS_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SPS_Config__ext1O__Format : T_Format SPS_Config__ext1O__Type SPS_Config__ext1O__cond :=
        proj2_format  SPS_Config__ext1O__cond SPS_Config__ext1O__list__Format
    SPS_Config__ext1O__F1 SPS_Config__ext1O__F2 SPS_Config__ext1O__F1F2_cond  SPS_Config__ext1O__F1F2_cond2 SPS_Config__ext1O__F2F1_cond.
Opaque SPS_Config__ext1O__cond SPS_Config__ext1O__Format.

Definition SPS_Config__ext1__check_all_none (b : SPS_Config__ext1O__Type) : bool :=
match b with 
  | make__SPS_Config__ext1O__Type None None None None None  => false 
  | _ => true 
 end.
Definition SPS_Config__ext1__Format : T_Format SPS_Config__ext1__Type SPS_Config__ext1__cond :=
  restrict_add_format SPS_Config__ext1__check_all_none SPS_Config__ext1O__Format.

Opaque SPS_Config__ext1__cond SPS_Config__ext1__Format.


Definition SPS_Config__root_Format_Type := Eval cbn in seq_format_prod SPS_Config__root_list.
Definition SPS_Config__root_Format_list : SPS_Config__root_Format_Type :=
  (SPS_Config__periodicity__Format, (SPS_Config__nrofHARQ_Processes__Format, (PUCCH_ResourceId__Format, (SPS_Config__mcs_Table__Format, unit_format)))).

Definition SPS_Config__ext_Format_Type := Eval cbn in get_formats SPS_Config__ext_list.
Definition SPS_Config__ext_Format_list : SPS_Config__ext_Format_Type :=
  (SPS_Config__ext0__Format, (SPS_Config__ext1__Format, unit__Format)).

Definition SPS_Config__list_type : Set := (seq_type SPS_Config__root_list) * (seq_ext_type SPS_Config__ext_list).
Definition SPS_Config__list_cond (z : SPS_Config__list_type) : Prop :=
        (seq_cond SPS_Config__root_list (fst z)) /\ (seq_ext_cond SPS_Config__ext_list (snd z)).
Definition SPS_Config__list_format : T_Format SPS_Config__list_type SPS_Config__list_cond :=
 (* Eval compute in *) seq_ext_format SPS_Config__root_list SPS_Config__root_Format_list SPS_Config__ext_list SPS_Config__ext_Format_list.

Opaque SPS_Config__list_format.
Definition SPS_Config__F1 (z : SPS_Config__Type) : SPS_Config__list_type :=
  (((SPS_Config__periodicity z, (SPS_Config__nrofHARQ_Processes z, (SPS_Config__n1PUCCH_AN z, (SPS_Config__mcs_Table z, tt))))), (
(SPS_Config__ext0 z, (SPS_Config__ext1 z, tt)))).
Definition SPS_Config__F2 (y : SPS_Config__list_type) : SPS_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__SPS_Config__Type j0 j1 j2 j3 i0 i1
  end.
Definition SPS_Config__helper1 : (forall a : SPS_Config__Type, SPS_Config__cond a -> SPS_Config__list_cond (SPS_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SPS_Config__helper2 : (forall a : SPS_Config__Type, SPS_Config__F2 (SPS_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SPS_Config__helper3 : (forall b : SPS_Config__list_type, SPS_Config__list_cond b -> SPS_Config__cond (SPS_Config__F2 b) /\ SPS_Config__F1 (SPS_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SPS_Config__cond, SPS_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SPS_Config__Format : T_Format SPS_Config__Type SPS_Config__cond :=
 proj2_format SPS_Config__cond SPS_Config__list_format  SPS_Config__F1 SPS_Config__F2 SPS_Config__helper1 SPS_Config__helper2 SPS_Config__helper3.

Opaque SPS_Config__cond SPS_Config__Format.

