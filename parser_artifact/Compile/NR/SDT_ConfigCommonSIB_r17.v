Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Inductive SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Type : Set :=
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf20
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf40
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf64
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf128
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf512
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf1024
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf2560
 | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__spare1
.
Definition SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__cond := (fun (_ : SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Type) => True).
Lemma SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__nat__helper.

Definition SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1 t :=
  match t with
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf20 => 0
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf40 => 1
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf64 => 2
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf128 => 3
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf512 => 4
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf1024 => 5
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf2560 => 6
  | SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__spare1 => 7
  end.
Definition SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F2 n :=
  match n with
  | 0 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf20
  | 1 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf40
  | 2 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf64
  | 3 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf128
  | 4 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf512
  | 5 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf1024
  | 6 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf2560
  | 7 => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__spare1
  | _ => SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__sf20
  end.
Lemma SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1F2 : forall x : SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Type, (SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1 x <= 7) /\ SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F2 (SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F2F1 : forall (y : nat) (H : y <= 7), SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1 (SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Type : Set :=
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte32
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte100
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte200
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte400
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte600
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte800
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte1000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte2000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte4000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte8000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte9000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte10000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte12000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte24000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte48000
 | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte96000
.
Definition SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__cond := (fun (_ : SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Type) => True).
Lemma SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__nat__helper.

Definition SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1 t :=
  match t with
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte32 => 0
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte100 => 1
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte200 => 2
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte400 => 3
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte600 => 4
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte800 => 5
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte1000 => 6
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte2000 => 7
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte4000 => 8
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte8000 => 9
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte9000 => 10
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte10000 => 11
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte12000 => 12
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte24000 => 13
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte48000 => 14
  | SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte96000 => 15
  end.
Definition SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F2 n :=
  match n with
  | 0 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte32
  | 1 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte100
  | 2 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte200
  | 3 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte400
  | 4 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte600
  | 5 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte800
  | 6 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte1000
  | 7 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte2000
  | 8 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte4000
  | 9 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte8000
  | 10 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte9000
  | 11 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte10000
  | 12 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte12000
  | 13 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte24000
  | 14 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte48000
  | 15 => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte96000
  | _ => SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__byte32
  end.
Lemma SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1F2 : forall x : SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Type, (SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1 x <= 15) /\ SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F2 (SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1 x) = x. imp_solve. Qed.
Lemma SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F2F1 : forall (y : nat) (H : y <= 15), SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1 (SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SDT_ConfigCommonSIB_r17__t319a_r17__Type : Set :=
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms100
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms200
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms300
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms400
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms600
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms1000
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms2000
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms3000
 | SDT_ConfigCommonSIB_r17__t319a_r17__ms4000
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare7
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare6
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare5
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare4
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare3
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare2
 | SDT_ConfigCommonSIB_r17__t319a_r17__spare1
.
Definition SDT_ConfigCommonSIB_r17__t319a_r17__cond := (fun (_ : SDT_ConfigCommonSIB_r17__t319a_r17__Type) => True).
Lemma SDT_ConfigCommonSIB_r17__t319a_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDT_ConfigCommonSIB_r17__t319a_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SDT_ConfigCommonSIB_r17__t319a_r17__nat__helper.

Definition SDT_ConfigCommonSIB_r17__t319a_r17__F1 t :=
  match t with
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms100 => 0
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms200 => 1
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms300 => 2
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms400 => 3
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms600 => 4
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms1000 => 5
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms2000 => 6
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms3000 => 7
  | SDT_ConfigCommonSIB_r17__t319a_r17__ms4000 => 8
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare7 => 9
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare6 => 10
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare5 => 11
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare4 => 12
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare3 => 13
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare2 => 14
  | SDT_ConfigCommonSIB_r17__t319a_r17__spare1 => 15
  end.
Definition SDT_ConfigCommonSIB_r17__t319a_r17__F2 n :=
  match n with
  | 0 => SDT_ConfigCommonSIB_r17__t319a_r17__ms100
  | 1 => SDT_ConfigCommonSIB_r17__t319a_r17__ms200
  | 2 => SDT_ConfigCommonSIB_r17__t319a_r17__ms300
  | 3 => SDT_ConfigCommonSIB_r17__t319a_r17__ms400
  | 4 => SDT_ConfigCommonSIB_r17__t319a_r17__ms600
  | 5 => SDT_ConfigCommonSIB_r17__t319a_r17__ms1000
  | 6 => SDT_ConfigCommonSIB_r17__t319a_r17__ms2000
  | 7 => SDT_ConfigCommonSIB_r17__t319a_r17__ms3000
  | 8 => SDT_ConfigCommonSIB_r17__t319a_r17__ms4000
  | 9 => SDT_ConfigCommonSIB_r17__t319a_r17__spare7
  | 10 => SDT_ConfigCommonSIB_r17__t319a_r17__spare6
  | 11 => SDT_ConfigCommonSIB_r17__t319a_r17__spare5
  | 12 => SDT_ConfigCommonSIB_r17__t319a_r17__spare4
  | 13 => SDT_ConfigCommonSIB_r17__t319a_r17__spare3
  | 14 => SDT_ConfigCommonSIB_r17__t319a_r17__spare2
  | 15 => SDT_ConfigCommonSIB_r17__t319a_r17__spare1
  | _ => SDT_ConfigCommonSIB_r17__t319a_r17__ms100
  end.
Lemma SDT_ConfigCommonSIB_r17__t319a_r17__F1F2 : forall x : SDT_ConfigCommonSIB_r17__t319a_r17__Type, (SDT_ConfigCommonSIB_r17__t319a_r17__F1 x <= 15) /\ SDT_ConfigCommonSIB_r17__t319a_r17__F2 (SDT_ConfigCommonSIB_r17__t319a_r17__F1 x) = x. imp_solve. Qed.
Lemma SDT_ConfigCommonSIB_r17__t319a_r17__F2F1 : forall (y : nat) (H : y <= 15), SDT_ConfigCommonSIB_r17__t319a_r17__F1 (SDT_ConfigCommonSIB_r17__t319a_r17__F2 y) = y. enum_solve H y. Qed.

Record SDT_ConfigCommonSIB_r17__Type : Set :=
  make__SDT_ConfigCommonSIB_r17__Type {
    SDT_ConfigCommonSIB_r17__sdt_RSRP_Threshold_r17 : option RSRP_Range__Type ;
    SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17 : option SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Type ;
    SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17 : SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Type ;
    SDT_ConfigCommonSIB_r17__t319a_r17 : SDT_ConfigCommonSIB_r17__t319a_r17__Type ;
}.
Definition SDT_ConfigCommonSIB_r17__list := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Type SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__cond ::
 Nor SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Type SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__cond ::
 Nor SDT_ConfigCommonSIB_r17__t319a_r17__Type SDT_ConfigCommonSIB_r17__t319a_r17__cond ::
 nil).
Definition SDT_ConfigCommonSIB_r17__cond z := 
  opt_cond RSRP_Range__cond (SDT_ConfigCommonSIB_r17__sdt_RSRP_Threshold_r17 z) /\
  opt_cond SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__cond (SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17 z) /\
  SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__cond (SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17 z) /\
  SDT_ConfigCommonSIB_r17__t319a_r17__cond (SDT_ConfigCommonSIB_r17__t319a_r17 z) /\
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
Definition SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Format : T_Format SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__nat__Format SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1 SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F2 SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F1F2 SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__F2F1.

Opaque SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__cond SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Format.

Definition SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Format : T_Format SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__nat__Format SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1 SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F2 SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F1F2 SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__F2F1.

Opaque SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__cond SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Format.

Definition SDT_ConfigCommonSIB_r17__t319a_r17__Format : T_Format SDT_ConfigCommonSIB_r17__t319a_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDT_ConfigCommonSIB_r17__t319a_r17__nat__Format SDT_ConfigCommonSIB_r17__t319a_r17__F1 SDT_ConfigCommonSIB_r17__t319a_r17__F2 SDT_ConfigCommonSIB_r17__t319a_r17__F1F2 SDT_ConfigCommonSIB_r17__t319a_r17__F2F1.

Opaque SDT_ConfigCommonSIB_r17__t319a_r17__cond SDT_ConfigCommonSIB_r17__t319a_r17__Format.


Definition SDT_ConfigCommonSIB_r17__Format_Type := Eval cbn in seq_format_prod SDT_ConfigCommonSIB_r17__list.
Definition SDT_ConfigCommonSIB_r17__Format_list : SDT_ConfigCommonSIB_r17__Format_Type :=
  (RSRP_Range__Format, (SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17__Format, (SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17__Format, (SDT_ConfigCommonSIB_r17__t319a_r17__Format, unit_format)))).
Definition SDT_ConfigCommonSIB_r17__list__Format := (*Eval compute in *) seq_format SDT_ConfigCommonSIB_r17__list SDT_ConfigCommonSIB_r17__Format_list.
Definition SDT_ConfigCommonSIB_r17__F1 z :=
  (SDT_ConfigCommonSIB_r17__sdt_RSRP_Threshold_r17 z, (SDT_ConfigCommonSIB_r17__sdt_LogicalChannelSR_DelayTimer_r17 z, (SDT_ConfigCommonSIB_r17__sdt_DataVolumeThreshold_r17 z, (SDT_ConfigCommonSIB_r17__t319a_r17 z, tt)))).
Definition SDT_ConfigCommonSIB_r17__F2 (y : seq_type SDT_ConfigCommonSIB_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SDT_ConfigCommonSIB_r17__Type i0 i1 i2 i3
  end.
Lemma SDT_ConfigCommonSIB_r17__F1F2_cond (z : SDT_ConfigCommonSIB_r17__Type)
  : SDT_ConfigCommonSIB_r17__cond z ->
  (seq_cond SDT_ConfigCommonSIB_r17__list (SDT_ConfigCommonSIB_r17__F1 z)).
intro H. unfold SDT_ConfigCommonSIB_r17__cond in H. simpl. auto. Qed.
Lemma SDT_ConfigCommonSIB_r17__F1F2_cond2 (z : SDT_ConfigCommonSIB_r17__Type)
 : SDT_ConfigCommonSIB_r17__F2 (SDT_ConfigCommonSIB_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SDT_ConfigCommonSIB_r17__F2F1_cond (y : seq_type SDT_ConfigCommonSIB_r17__list)
  : seq_cond SDT_ConfigCommonSIB_r17__list y ->
 (SDT_ConfigCommonSIB_r17__cond (SDT_ConfigCommonSIB_r17__F2 y)) /\  SDT_ConfigCommonSIB_r17__F1 (SDT_ConfigCommonSIB_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SDT_ConfigCommonSIB_r17__cond. simpl in *. auto.
 - simpl. unfold SDT_ConfigCommonSIB_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SDT_ConfigCommonSIB_r17__Format : T_Format SDT_ConfigCommonSIB_r17__Type SDT_ConfigCommonSIB_r17__cond :=
        proj2_format  SDT_ConfigCommonSIB_r17__cond SDT_ConfigCommonSIB_r17__list__Format
    SDT_ConfigCommonSIB_r17__F1 SDT_ConfigCommonSIB_r17__F2 SDT_ConfigCommonSIB_r17__F1F2_cond  SDT_ConfigCommonSIB_r17__F1F2_cond2 SDT_ConfigCommonSIB_r17__F2F1_cond.
Opaque SDT_ConfigCommonSIB_r17__cond SDT_ConfigCommonSIB_r17__Format.

