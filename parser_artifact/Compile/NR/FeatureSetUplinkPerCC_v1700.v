Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SupportedBandwidth_v1700.

Opaque SupportedBandwidth_v1700__cond SupportedBandwidth_v1700__Format.

Inductive FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Type : Set :=
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n1
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n2
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n3
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n4
.
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__cond := (fun (_ : FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Type) => True).
Lemma FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__nat__helper.

Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1 t :=
  match t with
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n1 => 0
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n2 => 1
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n3 => 2
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n4 => 3
  end.
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n1
  | 1 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n2
  | 2 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n3
  | 3 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n4
  | _ => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__n1
  end.
Lemma FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1F2 : forall x : FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Type, (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1 x <= 3) /\ FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F2 (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F2F1 : forall (y : nat) (H : y <= 3), FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1 (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Type : Set :=
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n1
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n2
 | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n4
.
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__cond := (fun (_ : FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Type) => True).
Lemma FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__nat__helper.

Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1 t :=
  match t with
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n1 => 0
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n2 => 1
  | FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n4 => 2
  end.
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n1
  | 1 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n2
  | 2 => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n4
  | _ => FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__n1
  end.
Lemma FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1F2 : forall x : FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Type, (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1 x <= 2) /\ FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F2 (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1 (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SupportedBandwidth_v1700.

Opaque SupportedBandwidth_v1700__cond SupportedBandwidth_v1700__Format.

Record FeatureSetUplinkPerCC_v1700__Type : Set :=
  make__FeatureSetUplinkPerCC_v1700__Type {
    FeatureSetUplinkPerCC_v1700__supportedMinBandwidthUL_r17 : option SupportedBandwidth_v1700__Type ;
    FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17 : option FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Type ;
    FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17 : option FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Type ;
    FeatureSetUplinkPerCC_v1700__supportedBandwidthUL_v1710 : option SupportedBandwidth_v1700__Type ;
}.
Definition FeatureSetUplinkPerCC_v1700__list := (
 Opt SupportedBandwidth_v1700__Type SupportedBandwidth_v1700__cond ::
 Opt FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Type FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__cond ::
 Opt FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Type FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__cond ::
 Opt SupportedBandwidth_v1700__Type SupportedBandwidth_v1700__cond ::
 nil).
Definition FeatureSetUplinkPerCC_v1700__cond z := 
  opt_cond SupportedBandwidth_v1700__cond (FeatureSetUplinkPerCC_v1700__supportedMinBandwidthUL_r17 z) /\
  opt_cond FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__cond (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17 z) /\
  opt_cond FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__cond (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17 z) /\
  opt_cond SupportedBandwidth_v1700__cond (FeatureSetUplinkPerCC_v1700__supportedBandwidthUL_v1710 z) /\
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
Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Format : T_Format FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__nat__Format FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F2 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F1F2 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__F2F1.

Opaque FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__cond FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Format.

Definition FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Format : T_Format FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__nat__Format FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F2 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F1F2 FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__F2F1.

Opaque FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__cond FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Format.


Definition FeatureSetUplinkPerCC_v1700__Format_Type := Eval cbn in seq_format_prod FeatureSetUplinkPerCC_v1700__list.
Definition FeatureSetUplinkPerCC_v1700__Format_list : FeatureSetUplinkPerCC_v1700__Format_Type :=
  (SupportedBandwidth_v1700__Format, (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17__Format, (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17__Format, (SupportedBandwidth_v1700__Format, unit_format)))).
Definition FeatureSetUplinkPerCC_v1700__list__Format := (*Eval compute in *) seq_format FeatureSetUplinkPerCC_v1700__list FeatureSetUplinkPerCC_v1700__Format_list.
Definition FeatureSetUplinkPerCC_v1700__F1 z :=
  (FeatureSetUplinkPerCC_v1700__supportedMinBandwidthUL_r17 z, (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_RepetitionTypeB_r17 z, (FeatureSetUplinkPerCC_v1700__mTRP_PUSCH_TypeB_CB_r17 z, (FeatureSetUplinkPerCC_v1700__supportedBandwidthUL_v1710 z, tt)))).
Definition FeatureSetUplinkPerCC_v1700__F2 (y : seq_type FeatureSetUplinkPerCC_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FeatureSetUplinkPerCC_v1700__Type i0 i1 i2 i3
  end.
Lemma FeatureSetUplinkPerCC_v1700__F1F2_cond (z : FeatureSetUplinkPerCC_v1700__Type)
  : FeatureSetUplinkPerCC_v1700__cond z ->
  (seq_cond FeatureSetUplinkPerCC_v1700__list (FeatureSetUplinkPerCC_v1700__F1 z)).
intro H. unfold FeatureSetUplinkPerCC_v1700__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC_v1700__F1F2_cond2 (z : FeatureSetUplinkPerCC_v1700__Type)
 : FeatureSetUplinkPerCC_v1700__F2 (FeatureSetUplinkPerCC_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC_v1700__F2F1_cond (y : seq_type FeatureSetUplinkPerCC_v1700__list)
  : seq_cond FeatureSetUplinkPerCC_v1700__list y ->
 (FeatureSetUplinkPerCC_v1700__cond (FeatureSetUplinkPerCC_v1700__F2 y)) /\  FeatureSetUplinkPerCC_v1700__F1 (FeatureSetUplinkPerCC_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplinkPerCC_v1700__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplinkPerCC_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplinkPerCC_v1700__Format : T_Format FeatureSetUplinkPerCC_v1700__Type FeatureSetUplinkPerCC_v1700__cond :=
        proj2_format  FeatureSetUplinkPerCC_v1700__cond FeatureSetUplinkPerCC_v1700__list__Format
    FeatureSetUplinkPerCC_v1700__F1 FeatureSetUplinkPerCC_v1700__F2 FeatureSetUplinkPerCC_v1700__F1F2_cond  FeatureSetUplinkPerCC_v1700__F1F2_cond2 FeatureSetUplinkPerCC_v1700__F2F1_cond.
Opaque FeatureSetUplinkPerCC_v1700__cond FeatureSetUplinkPerCC_v1700__Format.

