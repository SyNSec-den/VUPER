Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RateMatchPatternLTE_CRS__carrierFreqDL__helper1 : (0 <= 16383)%Z.  lia. Qed.
Lemma RateMatchPatternLTE_CRS__carrierFreqDL__helper2 : to_bit_sz (Z.to_nat (16383 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16383 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RateMatchPatternLTE_CRS__carrierFreqDL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RateMatchPatternLTE_CRS__carrierFreqDL__Type := Z.
Definition RateMatchPatternLTE_CRS__carrierFreqDL__cond := (fun z => (0 <= z <= 16383)%Z).
Inductive RateMatchPatternLTE_CRS__carrierBandwidthDL__Type : Set :=
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__n6
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__n15
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__n25
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__n50
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__n75
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__n100
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__spare2
 | RateMatchPatternLTE_CRS__carrierBandwidthDL__spare1
.
Definition RateMatchPatternLTE_CRS__carrierBandwidthDL__cond := (fun (_ : RateMatchPatternLTE_CRS__carrierBandwidthDL__Type) => True).
Lemma RateMatchPatternLTE_CRS__carrierBandwidthDL__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RateMatchPatternLTE_CRS__carrierBandwidthDL__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RateMatchPatternLTE_CRS__carrierBandwidthDL__nat__helper.

Definition RateMatchPatternLTE_CRS__carrierBandwidthDL__F1 t :=
  match t with
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__n6 => 0
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__n15 => 1
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__n25 => 2
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__n50 => 3
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__n75 => 4
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__n100 => 5
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__spare2 => 6
  | RateMatchPatternLTE_CRS__carrierBandwidthDL__spare1 => 7
  end.
Definition RateMatchPatternLTE_CRS__carrierBandwidthDL__F2 n :=
  match n with
  | 0 => RateMatchPatternLTE_CRS__carrierBandwidthDL__n6
  | 1 => RateMatchPatternLTE_CRS__carrierBandwidthDL__n15
  | 2 => RateMatchPatternLTE_CRS__carrierBandwidthDL__n25
  | 3 => RateMatchPatternLTE_CRS__carrierBandwidthDL__n50
  | 4 => RateMatchPatternLTE_CRS__carrierBandwidthDL__n75
  | 5 => RateMatchPatternLTE_CRS__carrierBandwidthDL__n100
  | 6 => RateMatchPatternLTE_CRS__carrierBandwidthDL__spare2
  | 7 => RateMatchPatternLTE_CRS__carrierBandwidthDL__spare1
  | _ => RateMatchPatternLTE_CRS__carrierBandwidthDL__n6
  end.
Lemma RateMatchPatternLTE_CRS__carrierBandwidthDL__F1F2 : forall x : RateMatchPatternLTE_CRS__carrierBandwidthDL__Type, (RateMatchPatternLTE_CRS__carrierBandwidthDL__F1 x <= 7) /\ RateMatchPatternLTE_CRS__carrierBandwidthDL__F2 (RateMatchPatternLTE_CRS__carrierBandwidthDL__F1 x) = x. imp_solve. Qed.
Lemma RateMatchPatternLTE_CRS__carrierBandwidthDL__F2F1 : forall (y : nat) (H : y <= 7), RateMatchPatternLTE_CRS__carrierBandwidthDL__F1 (RateMatchPatternLTE_CRS__carrierBandwidthDL__F2 y) = y. enum_solve H y. Qed.

Require Import NR.EUTRA_MBSFN_SubframeConfigList.

Opaque EUTRA_MBSFN_SubframeConfigList__cond EUTRA_MBSFN_SubframeConfigList__Format.

Inductive RateMatchPatternLTE_CRS__nrofCRS_Ports__Type : Set :=
 | RateMatchPatternLTE_CRS__nrofCRS_Ports__n1
 | RateMatchPatternLTE_CRS__nrofCRS_Ports__n2
 | RateMatchPatternLTE_CRS__nrofCRS_Ports__n4
.
Definition RateMatchPatternLTE_CRS__nrofCRS_Ports__cond := (fun (_ : RateMatchPatternLTE_CRS__nrofCRS_Ports__Type) => True).
Lemma RateMatchPatternLTE_CRS__nrofCRS_Ports__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RateMatchPatternLTE_CRS__nrofCRS_Ports__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 RateMatchPatternLTE_CRS__nrofCRS_Ports__nat__helper.

Definition RateMatchPatternLTE_CRS__nrofCRS_Ports__F1 t :=
  match t with
  | RateMatchPatternLTE_CRS__nrofCRS_Ports__n1 => 0
  | RateMatchPatternLTE_CRS__nrofCRS_Ports__n2 => 1
  | RateMatchPatternLTE_CRS__nrofCRS_Ports__n4 => 2
  end.
Definition RateMatchPatternLTE_CRS__nrofCRS_Ports__F2 n :=
  match n with
  | 0 => RateMatchPatternLTE_CRS__nrofCRS_Ports__n1
  | 1 => RateMatchPatternLTE_CRS__nrofCRS_Ports__n2
  | 2 => RateMatchPatternLTE_CRS__nrofCRS_Ports__n4
  | _ => RateMatchPatternLTE_CRS__nrofCRS_Ports__n1
  end.
Lemma RateMatchPatternLTE_CRS__nrofCRS_Ports__F1F2 : forall x : RateMatchPatternLTE_CRS__nrofCRS_Ports__Type, (RateMatchPatternLTE_CRS__nrofCRS_Ports__F1 x <= 2) /\ RateMatchPatternLTE_CRS__nrofCRS_Ports__F2 (RateMatchPatternLTE_CRS__nrofCRS_Ports__F1 x) = x. imp_solve. Qed.
Lemma RateMatchPatternLTE_CRS__nrofCRS_Ports__F2F1 : forall (y : nat) (H : y <= 2), RateMatchPatternLTE_CRS__nrofCRS_Ports__F1 (RateMatchPatternLTE_CRS__nrofCRS_Ports__F2 y) = y. enum_solve H y. Qed.

Inductive RateMatchPatternLTE_CRS__v_Shift__Type : Set :=
 | RateMatchPatternLTE_CRS__v_Shift__n0
 | RateMatchPatternLTE_CRS__v_Shift__n1
 | RateMatchPatternLTE_CRS__v_Shift__n2
 | RateMatchPatternLTE_CRS__v_Shift__n3
 | RateMatchPatternLTE_CRS__v_Shift__n4
 | RateMatchPatternLTE_CRS__v_Shift__n5
.
Definition RateMatchPatternLTE_CRS__v_Shift__cond := (fun (_ : RateMatchPatternLTE_CRS__v_Shift__Type) => True).
Lemma RateMatchPatternLTE_CRS__v_Shift__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RateMatchPatternLTE_CRS__v_Shift__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 RateMatchPatternLTE_CRS__v_Shift__nat__helper.

Definition RateMatchPatternLTE_CRS__v_Shift__F1 t :=
  match t with
  | RateMatchPatternLTE_CRS__v_Shift__n0 => 0
  | RateMatchPatternLTE_CRS__v_Shift__n1 => 1
  | RateMatchPatternLTE_CRS__v_Shift__n2 => 2
  | RateMatchPatternLTE_CRS__v_Shift__n3 => 3
  | RateMatchPatternLTE_CRS__v_Shift__n4 => 4
  | RateMatchPatternLTE_CRS__v_Shift__n5 => 5
  end.
Definition RateMatchPatternLTE_CRS__v_Shift__F2 n :=
  match n with
  | 0 => RateMatchPatternLTE_CRS__v_Shift__n0
  | 1 => RateMatchPatternLTE_CRS__v_Shift__n1
  | 2 => RateMatchPatternLTE_CRS__v_Shift__n2
  | 3 => RateMatchPatternLTE_CRS__v_Shift__n3
  | 4 => RateMatchPatternLTE_CRS__v_Shift__n4
  | 5 => RateMatchPatternLTE_CRS__v_Shift__n5
  | _ => RateMatchPatternLTE_CRS__v_Shift__n0
  end.
Lemma RateMatchPatternLTE_CRS__v_Shift__F1F2 : forall x : RateMatchPatternLTE_CRS__v_Shift__Type, (RateMatchPatternLTE_CRS__v_Shift__F1 x <= 5) /\ RateMatchPatternLTE_CRS__v_Shift__F2 (RateMatchPatternLTE_CRS__v_Shift__F1 x) = x. imp_solve. Qed.
Lemma RateMatchPatternLTE_CRS__v_Shift__F2F1 : forall (y : nat) (H : y <= 5), RateMatchPatternLTE_CRS__v_Shift__F1 (RateMatchPatternLTE_CRS__v_Shift__F2 y) = y. enum_solve H y. Qed.

Record RateMatchPatternLTE_CRS__Type : Set :=
  make__RateMatchPatternLTE_CRS__Type {
    RateMatchPatternLTE_CRS__carrierFreqDL : Z ;
    RateMatchPatternLTE_CRS__carrierBandwidthDL : RateMatchPatternLTE_CRS__carrierBandwidthDL__Type ;
    RateMatchPatternLTE_CRS__mbsfn_SubframeConfigList : option EUTRA_MBSFN_SubframeConfigList__Type ;
    RateMatchPatternLTE_CRS__nrofCRS_Ports : RateMatchPatternLTE_CRS__nrofCRS_Ports__Type ;
    RateMatchPatternLTE_CRS__v_Shift : RateMatchPatternLTE_CRS__v_Shift__Type ;
}.
Definition RateMatchPatternLTE_CRS__list := (
 Nor Z RateMatchPatternLTE_CRS__carrierFreqDL__cond ::
 Nor RateMatchPatternLTE_CRS__carrierBandwidthDL__Type RateMatchPatternLTE_CRS__carrierBandwidthDL__cond ::
 Opt EUTRA_MBSFN_SubframeConfigList__Type EUTRA_MBSFN_SubframeConfigList__cond ::
 Nor RateMatchPatternLTE_CRS__nrofCRS_Ports__Type RateMatchPatternLTE_CRS__nrofCRS_Ports__cond ::
 Nor RateMatchPatternLTE_CRS__v_Shift__Type RateMatchPatternLTE_CRS__v_Shift__cond ::
 nil).
Definition RateMatchPatternLTE_CRS__cond z := 
  RateMatchPatternLTE_CRS__carrierFreqDL__cond (RateMatchPatternLTE_CRS__carrierFreqDL z) /\
  RateMatchPatternLTE_CRS__carrierBandwidthDL__cond (RateMatchPatternLTE_CRS__carrierBandwidthDL z) /\
  opt_cond EUTRA_MBSFN_SubframeConfigList__cond (RateMatchPatternLTE_CRS__mbsfn_SubframeConfigList z) /\
  RateMatchPatternLTE_CRS__nrofCRS_Ports__cond (RateMatchPatternLTE_CRS__nrofCRS_Ports z) /\
  RateMatchPatternLTE_CRS__v_Shift__cond (RateMatchPatternLTE_CRS__v_Shift z) /\
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
Definition RateMatchPatternLTE_CRS__carrierFreqDL__Format : T_Format Z RateMatchPatternLTE_CRS__carrierFreqDL__cond :=
 ranged_int_format (0) (16383) RateMatchPatternLTE_CRS__carrierFreqDL__helper1 RateMatchPatternLTE_CRS__carrierFreqDL__helper2.

Opaque RateMatchPatternLTE_CRS__carrierFreqDL__cond RateMatchPatternLTE_CRS__carrierFreqDL__Format.

Definition RateMatchPatternLTE_CRS__carrierBandwidthDL__Format : T_Format RateMatchPatternLTE_CRS__carrierBandwidthDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RateMatchPatternLTE_CRS__carrierBandwidthDL__nat__Format RateMatchPatternLTE_CRS__carrierBandwidthDL__F1 RateMatchPatternLTE_CRS__carrierBandwidthDL__F2 RateMatchPatternLTE_CRS__carrierBandwidthDL__F1F2 RateMatchPatternLTE_CRS__carrierBandwidthDL__F2F1.

Opaque RateMatchPatternLTE_CRS__carrierBandwidthDL__cond RateMatchPatternLTE_CRS__carrierBandwidthDL__Format.

Definition RateMatchPatternLTE_CRS__nrofCRS_Ports__Format : T_Format RateMatchPatternLTE_CRS__nrofCRS_Ports__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RateMatchPatternLTE_CRS__nrofCRS_Ports__nat__Format RateMatchPatternLTE_CRS__nrofCRS_Ports__F1 RateMatchPatternLTE_CRS__nrofCRS_Ports__F2 RateMatchPatternLTE_CRS__nrofCRS_Ports__F1F2 RateMatchPatternLTE_CRS__nrofCRS_Ports__F2F1.

Opaque RateMatchPatternLTE_CRS__nrofCRS_Ports__cond RateMatchPatternLTE_CRS__nrofCRS_Ports__Format.

Definition RateMatchPatternLTE_CRS__v_Shift__Format : T_Format RateMatchPatternLTE_CRS__v_Shift__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RateMatchPatternLTE_CRS__v_Shift__nat__Format RateMatchPatternLTE_CRS__v_Shift__F1 RateMatchPatternLTE_CRS__v_Shift__F2 RateMatchPatternLTE_CRS__v_Shift__F1F2 RateMatchPatternLTE_CRS__v_Shift__F2F1.

Opaque RateMatchPatternLTE_CRS__v_Shift__cond RateMatchPatternLTE_CRS__v_Shift__Format.


Definition RateMatchPatternLTE_CRS__Format_Type := Eval cbn in seq_format_prod RateMatchPatternLTE_CRS__list.
Definition RateMatchPatternLTE_CRS__Format_list : RateMatchPatternLTE_CRS__Format_Type :=
  (RateMatchPatternLTE_CRS__carrierFreqDL__Format, (RateMatchPatternLTE_CRS__carrierBandwidthDL__Format, (EUTRA_MBSFN_SubframeConfigList__Format, (RateMatchPatternLTE_CRS__nrofCRS_Ports__Format, (RateMatchPatternLTE_CRS__v_Shift__Format, unit_format))))).
Definition RateMatchPatternLTE_CRS__list__Format := (*Eval compute in *) seq_format RateMatchPatternLTE_CRS__list RateMatchPatternLTE_CRS__Format_list.
Definition RateMatchPatternLTE_CRS__F1 z :=
  (RateMatchPatternLTE_CRS__carrierFreqDL z, (RateMatchPatternLTE_CRS__carrierBandwidthDL z, (RateMatchPatternLTE_CRS__mbsfn_SubframeConfigList z, (RateMatchPatternLTE_CRS__nrofCRS_Ports z, (RateMatchPatternLTE_CRS__v_Shift z, tt))))).
Definition RateMatchPatternLTE_CRS__F2 (y : seq_type RateMatchPatternLTE_CRS__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__RateMatchPatternLTE_CRS__Type i0 i1 i2 i3 i4
  end.
Lemma RateMatchPatternLTE_CRS__F1F2_cond (z : RateMatchPatternLTE_CRS__Type)
  : RateMatchPatternLTE_CRS__cond z ->
  (seq_cond RateMatchPatternLTE_CRS__list (RateMatchPatternLTE_CRS__F1 z)).
intro H. unfold RateMatchPatternLTE_CRS__cond in H. simpl. auto. Qed.
Lemma RateMatchPatternLTE_CRS__F1F2_cond2 (z : RateMatchPatternLTE_CRS__Type)
 : RateMatchPatternLTE_CRS__F2 (RateMatchPatternLTE_CRS__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RateMatchPatternLTE_CRS__F2F1_cond (y : seq_type RateMatchPatternLTE_CRS__list)
  : seq_cond RateMatchPatternLTE_CRS__list y ->
 (RateMatchPatternLTE_CRS__cond (RateMatchPatternLTE_CRS__F2 y)) /\  RateMatchPatternLTE_CRS__F1 (RateMatchPatternLTE_CRS__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RateMatchPatternLTE_CRS__cond. simpl in *. auto.
 - simpl. unfold RateMatchPatternLTE_CRS__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RateMatchPatternLTE_CRS__Format : T_Format RateMatchPatternLTE_CRS__Type RateMatchPatternLTE_CRS__cond :=
        proj2_format  RateMatchPatternLTE_CRS__cond RateMatchPatternLTE_CRS__list__Format
    RateMatchPatternLTE_CRS__F1 RateMatchPatternLTE_CRS__F2 RateMatchPatternLTE_CRS__F1F2_cond  RateMatchPatternLTE_CRS__F1F2_cond2 RateMatchPatternLTE_CRS__F2F1_cond.
Opaque RateMatchPatternLTE_CRS__cond RateMatchPatternLTE_CRS__Format.

