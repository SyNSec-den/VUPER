Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type : Set :=
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms20
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms50
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms100
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms200
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms300
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms400
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms500
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms600
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms700
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms800
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms900
 | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms1000
.
Definition SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__cond := (fun (_ : SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type) => True).
Lemma SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__nat__helper : to_bit_sz 11 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__nat__Format : T_Format nat (fun z => (z <= 11)) :=
  nat_enum_format 11 SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__nat__helper.

Definition SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1 t :=
  match t with
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms20 => 0
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms50 => 1
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms100 => 2
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms200 => 3
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms300 => 4
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms400 => 5
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms500 => 6
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms600 => 7
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms700 => 8
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms800 => 9
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms900 => 10
  | SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms1000 => 11
  end.
Definition SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2 n :=
  match n with
  | 0 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms20
  | 1 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms50
  | 2 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms100
  | 3 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms200
  | 4 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms300
  | 5 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms400
  | 6 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms500
  | 7 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms600
  | 8 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms700
  | 9 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms800
  | 10 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms900
  | 11 => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms1000
  | _ => SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms20
  end.
Lemma SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1F2 : forall x : SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type, (SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1 x <= 11) /\ SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2 (SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2F1 : forall (y : nat) (H : y <= 11), SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1 (SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_TrafficPatternInfo_r16__timingOffset_r16__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma SL_TrafficPatternInfo_r16__timingOffset_r16__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_TrafficPatternInfo_r16__timingOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_TrafficPatternInfo_r16__timingOffset_r16__Type := Z.
Definition SL_TrafficPatternInfo_r16__timingOffset_r16__cond := (fun z => (0 <= z <= 10239)%Z).
Definition SL_TrafficPatternInfo_r16__messageSize_r16__Type := bit_string_fixed.
Definition SL_TrafficPatternInfo_r16__messageSize_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.SL_QoS_FlowIdentity_r16.

Opaque SL_QoS_FlowIdentity_r16__cond SL_QoS_FlowIdentity_r16__Format.

Record SL_TrafficPatternInfo_r16__Type : Set :=
  make__SL_TrafficPatternInfo_r16__Type {
    SL_TrafficPatternInfo_r16__trafficPeriodicity_r16 : SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type ;
    SL_TrafficPatternInfo_r16__timingOffset_r16 : Z ;
    SL_TrafficPatternInfo_r16__messageSize_r16 : SL_TrafficPatternInfo_r16__messageSize_r16__Type ;
    SL_TrafficPatternInfo_r16__sl_QoS_FlowIdentity_r16 : SL_QoS_FlowIdentity_r16__Type ;
}.
Definition SL_TrafficPatternInfo_r16__list := (
 Nor SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__cond ::
 Nor Z SL_TrafficPatternInfo_r16__timingOffset_r16__cond ::
 Nor SL_TrafficPatternInfo_r16__messageSize_r16__Type SL_TrafficPatternInfo_r16__messageSize_r16__cond ::
 Nor SL_QoS_FlowIdentity_r16__Type SL_QoS_FlowIdentity_r16__cond ::
 nil).
Definition SL_TrafficPatternInfo_r16__cond z := 
  SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__cond (SL_TrafficPatternInfo_r16__trafficPeriodicity_r16 z) /\
  SL_TrafficPatternInfo_r16__timingOffset_r16__cond (SL_TrafficPatternInfo_r16__timingOffset_r16 z) /\
  SL_TrafficPatternInfo_r16__messageSize_r16__cond (SL_TrafficPatternInfo_r16__messageSize_r16 z) /\
  SL_QoS_FlowIdentity_r16__cond (SL_TrafficPatternInfo_r16__sl_QoS_FlowIdentity_r16 z) /\
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
Definition SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Format : T_Format SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__nat__Format SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1 SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2 SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1F2 SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2F1.

Opaque SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__cond SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Format.

Definition SL_TrafficPatternInfo_r16__timingOffset_r16__Format : T_Format Z SL_TrafficPatternInfo_r16__timingOffset_r16__cond :=
 ranged_int_format (0) (10239) SL_TrafficPatternInfo_r16__timingOffset_r16__helper1 SL_TrafficPatternInfo_r16__timingOffset_r16__helper2.

Opaque SL_TrafficPatternInfo_r16__timingOffset_r16__cond SL_TrafficPatternInfo_r16__timingOffset_r16__Format.

Definition SL_TrafficPatternInfo_r16__messageSize_r16__Format : T_Format SL_TrafficPatternInfo_r16__messageSize_r16__Type SL_TrafficPatternInfo_r16__messageSize_r16__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque SL_TrafficPatternInfo_r16__messageSize_r16__cond SL_TrafficPatternInfo_r16__messageSize_r16__Format.


Definition SL_TrafficPatternInfo_r16__Format_Type := Eval cbn in seq_format_prod SL_TrafficPatternInfo_r16__list.
Definition SL_TrafficPatternInfo_r16__Format_list : SL_TrafficPatternInfo_r16__Format_Type :=
  (SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Format, (SL_TrafficPatternInfo_r16__timingOffset_r16__Format, (SL_TrafficPatternInfo_r16__messageSize_r16__Format, (SL_QoS_FlowIdentity_r16__Format, unit_format)))).
Definition SL_TrafficPatternInfo_r16__list__Format := (*Eval compute in *) seq_format SL_TrafficPatternInfo_r16__list SL_TrafficPatternInfo_r16__Format_list.
Definition SL_TrafficPatternInfo_r16__F1 z :=
  (SL_TrafficPatternInfo_r16__trafficPeriodicity_r16 z, (SL_TrafficPatternInfo_r16__timingOffset_r16 z, (SL_TrafficPatternInfo_r16__messageSize_r16 z, (SL_TrafficPatternInfo_r16__sl_QoS_FlowIdentity_r16 z, tt)))).
Definition SL_TrafficPatternInfo_r16__F2 (y : seq_type SL_TrafficPatternInfo_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SL_TrafficPatternInfo_r16__Type i0 i1 i2 i3
  end.
Lemma SL_TrafficPatternInfo_r16__F1F2_cond (z : SL_TrafficPatternInfo_r16__Type)
  : SL_TrafficPatternInfo_r16__cond z ->
  (seq_cond SL_TrafficPatternInfo_r16__list (SL_TrafficPatternInfo_r16__F1 z)).
intro H. unfold SL_TrafficPatternInfo_r16__cond in H. simpl. auto. Qed.
Lemma SL_TrafficPatternInfo_r16__F1F2_cond2 (z : SL_TrafficPatternInfo_r16__Type)
 : SL_TrafficPatternInfo_r16__F2 (SL_TrafficPatternInfo_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_TrafficPatternInfo_r16__F2F1_cond (y : seq_type SL_TrafficPatternInfo_r16__list)
  : seq_cond SL_TrafficPatternInfo_r16__list y ->
 (SL_TrafficPatternInfo_r16__cond (SL_TrafficPatternInfo_r16__F2 y)) /\  SL_TrafficPatternInfo_r16__F1 (SL_TrafficPatternInfo_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_TrafficPatternInfo_r16__cond. simpl in *. auto.
 - simpl. unfold SL_TrafficPatternInfo_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_TrafficPatternInfo_r16__Format : T_Format SL_TrafficPatternInfo_r16__Type SL_TrafficPatternInfo_r16__cond :=
        proj2_format  SL_TrafficPatternInfo_r16__cond SL_TrafficPatternInfo_r16__list__Format
    SL_TrafficPatternInfo_r16__F1 SL_TrafficPatternInfo_r16__F2 SL_TrafficPatternInfo_r16__F1F2_cond  SL_TrafficPatternInfo_r16__F1F2_cond2 SL_TrafficPatternInfo_r16__F2F1_cond.
Opaque SL_TrafficPatternInfo_r16__cond SL_TrafficPatternInfo_r16__Format.

