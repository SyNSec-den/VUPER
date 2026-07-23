Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.IAB_ResourceConfigID_r17.

Opaque IAB_ResourceConfigID_r17__cond IAB_ResourceConfigID_r17__Format.

Lemma IAB_ResourceConfig_r17__slotList_r17__seq_of__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma IAB_ResourceConfig_r17__slotList_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply IAB_ResourceConfig_r17__slotList_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IAB_ResourceConfig_r17__slotList_r17__seq_of__Type := Z.
Definition IAB_ResourceConfig_r17__slotList_r17__seq_of__cond := (fun z => (0 <= z <= 5119)%Z).
Definition IAB_ResourceConfig_r17__slotList_r17__Type := list Z.

Lemma IAB_ResourceConfig_r17__slotList_r17__helper1 : (0 <= 1 <= 5120)%Z.  lia. Qed.
Lemma IAB_ResourceConfig_r17__slotList_r17__helper2 : to_bit_sz (Z.to_nat (5120 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5120 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IAB_ResourceConfig_r17__slotList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IAB_ResourceConfig_r17__slotList_r17__cond (z : IAB_ResourceConfig_r17__slotList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 5120)%Z /\ (list_and IAB_ResourceConfig_r17__slotList_r17__seq_of__cond z) .

Inductive IAB_ResourceConfig_r17__periodicitySlotList_r17__Type : Set :=
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p5
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p625
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms1
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms1p25
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms2
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms2p5
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms5
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms10
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms20
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms40
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms80
 | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms160
.
Definition IAB_ResourceConfig_r17__periodicitySlotList_r17__cond := (fun (_ : IAB_ResourceConfig_r17__periodicitySlotList_r17__Type) => True).
Lemma IAB_ResourceConfig_r17__periodicitySlotList_r17__nat__helper : to_bit_sz 11 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition IAB_ResourceConfig_r17__periodicitySlotList_r17__nat__Format : T_Format nat (fun z => (z <= 11)) :=
  nat_enum_format 11 IAB_ResourceConfig_r17__periodicitySlotList_r17__nat__helper.

Definition IAB_ResourceConfig_r17__periodicitySlotList_r17__F1 t :=
  match t with
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p5 => 0
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p625 => 1
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms1 => 2
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms1p25 => 3
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms2 => 4
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms2p5 => 5
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms5 => 6
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms10 => 7
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms20 => 8
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms40 => 9
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms80 => 10
  | IAB_ResourceConfig_r17__periodicitySlotList_r17__ms160 => 11
  end.
Definition IAB_ResourceConfig_r17__periodicitySlotList_r17__F2 n :=
  match n with
  | 0 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p5
  | 1 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p625
  | 2 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms1
  | 3 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms1p25
  | 4 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms2
  | 5 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms2p5
  | 6 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms5
  | 7 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms10
  | 8 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms20
  | 9 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms40
  | 10 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms80
  | 11 => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms160
  | _ => IAB_ResourceConfig_r17__periodicitySlotList_r17__ms0p5
  end.
Lemma IAB_ResourceConfig_r17__periodicitySlotList_r17__F1F2 : forall x : IAB_ResourceConfig_r17__periodicitySlotList_r17__Type, (IAB_ResourceConfig_r17__periodicitySlotList_r17__F1 x <= 11) /\ IAB_ResourceConfig_r17__periodicitySlotList_r17__F2 (IAB_ResourceConfig_r17__periodicitySlotList_r17__F1 x) = x. imp_solve. Qed.
Lemma IAB_ResourceConfig_r17__periodicitySlotList_r17__F2F1 : forall (y : nat) (H : y <= 11), IAB_ResourceConfig_r17__periodicitySlotList_r17__F1 (IAB_ResourceConfig_r17__periodicitySlotList_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Record IAB_ResourceConfig_r17__Type : Set :=
  make__IAB_ResourceConfig_r17__Type {
    IAB_ResourceConfig_r17__iab_ResourceConfigID_r17 : IAB_ResourceConfigID_r17__Type ;
    IAB_ResourceConfig_r17__slotList_r17 : option IAB_ResourceConfig_r17__slotList_r17__Type ;
    IAB_ResourceConfig_r17__periodicitySlotList_r17 : option IAB_ResourceConfig_r17__periodicitySlotList_r17__Type ;
    IAB_ResourceConfig_r17__slotListSubcarrierSpacing_r17 : option SubcarrierSpacing__Type ;
}.
Definition IAB_ResourceConfig_r17__root_list : list seq_elem := (
 Nor IAB_ResourceConfigID_r17__Type IAB_ResourceConfigID_r17__cond ::
 Opt IAB_ResourceConfig_r17__slotList_r17__Type IAB_ResourceConfig_r17__slotList_r17__cond ::
 Opt IAB_ResourceConfig_r17__periodicitySlotList_r17__Type IAB_ResourceConfig_r17__periodicitySlotList_r17__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 nil).
Definition IAB_ResourceConfig_r17__ext_list : list typ := (
  nil).
Definition IAB_ResourceConfig_r17__cond (z : IAB_ResourceConfig_r17__Type) := 
(  IAB_ResourceConfigID_r17__cond (IAB_ResourceConfig_r17__iab_ResourceConfigID_r17 z) /\
  opt_cond IAB_ResourceConfig_r17__slotList_r17__cond (IAB_ResourceConfig_r17__slotList_r17 z) /\
  opt_cond IAB_ResourceConfig_r17__periodicitySlotList_r17__cond (IAB_ResourceConfig_r17__periodicitySlotList_r17 z) /\
  opt_cond SubcarrierSpacing__cond (IAB_ResourceConfig_r17__slotListSubcarrierSpacing_r17 z) /\
  True) /\ 
(  True).


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
Definition IAB_ResourceConfig_r17__slotList_r17__seq_of__Format : T_Format Z IAB_ResourceConfig_r17__slotList_r17__seq_of__cond :=
 ranged_int_format (0) (5119) IAB_ResourceConfig_r17__slotList_r17__seq_of__helper1 IAB_ResourceConfig_r17__slotList_r17__seq_of__helper2.

Opaque IAB_ResourceConfig_r17__slotList_r17__seq_of__cond IAB_ResourceConfig_r17__slotList_r17__seq_of__Format.

Definition IAB_ResourceConfig_r17__slotList_r17__Format : T_Format IAB_ResourceConfig_r17__slotList_r17__Type IAB_ResourceConfig_r17__slotList_r17__cond := seq_of_format IAB_ResourceConfig_r17__slotList_r17__seq_of__Format 1 5120 IAB_ResourceConfig_r17__slotList_r17__helper1 IAB_ResourceConfig_r17__slotList_r17__helper2.

Opaque IAB_ResourceConfig_r17__slotList_r17__cond IAB_ResourceConfig_r17__slotList_r17__Format.

Definition IAB_ResourceConfig_r17__periodicitySlotList_r17__Format : T_Format IAB_ResourceConfig_r17__periodicitySlotList_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format IAB_ResourceConfig_r17__periodicitySlotList_r17__nat__Format IAB_ResourceConfig_r17__periodicitySlotList_r17__F1 IAB_ResourceConfig_r17__periodicitySlotList_r17__F2 IAB_ResourceConfig_r17__periodicitySlotList_r17__F1F2 IAB_ResourceConfig_r17__periodicitySlotList_r17__F2F1.

Opaque IAB_ResourceConfig_r17__periodicitySlotList_r17__cond IAB_ResourceConfig_r17__periodicitySlotList_r17__Format.


Definition IAB_ResourceConfig_r17__root_Format_Type := Eval cbn in seq_format_prod IAB_ResourceConfig_r17__root_list.
Definition IAB_ResourceConfig_r17__root_Format_list : IAB_ResourceConfig_r17__root_Format_Type :=
  (IAB_ResourceConfigID_r17__Format, (IAB_ResourceConfig_r17__slotList_r17__Format, (IAB_ResourceConfig_r17__periodicitySlotList_r17__Format, (SubcarrierSpacing__Format, unit_format)))).

Definition IAB_ResourceConfig_r17__ext_Format_Type := Eval cbn in get_formats IAB_ResourceConfig_r17__ext_list.
Definition IAB_ResourceConfig_r17__ext_Format_list : IAB_ResourceConfig_r17__ext_Format_Type :=
  unit__Format.

Definition IAB_ResourceConfig_r17__list_type : Set := (seq_type IAB_ResourceConfig_r17__root_list) * (seq_ext_type IAB_ResourceConfig_r17__ext_list).
Definition IAB_ResourceConfig_r17__list_cond (z : IAB_ResourceConfig_r17__list_type) : Prop :=
        (seq_cond IAB_ResourceConfig_r17__root_list (fst z)) /\ (seq_ext_cond IAB_ResourceConfig_r17__ext_list (snd z)).
Definition IAB_ResourceConfig_r17__list_format : T_Format IAB_ResourceConfig_r17__list_type IAB_ResourceConfig_r17__list_cond :=
 (* Eval compute in *) seq_ext_format IAB_ResourceConfig_r17__root_list IAB_ResourceConfig_r17__root_Format_list IAB_ResourceConfig_r17__ext_list IAB_ResourceConfig_r17__ext_Format_list.

Opaque IAB_ResourceConfig_r17__list_format.
Definition IAB_ResourceConfig_r17__F1 (z : IAB_ResourceConfig_r17__Type) : IAB_ResourceConfig_r17__list_type :=
  (((IAB_ResourceConfig_r17__iab_ResourceConfigID_r17 z, (IAB_ResourceConfig_r17__slotList_r17 z, (IAB_ResourceConfig_r17__periodicitySlotList_r17 z, (IAB_ResourceConfig_r17__slotListSubcarrierSpacing_r17 z, tt))))), (
tt)).
Definition IAB_ResourceConfig_r17__F2 (y : IAB_ResourceConfig_r17__list_type) : IAB_ResourceConfig_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__IAB_ResourceConfig_r17__Type j0 j1 j2 j3
  end.
Definition IAB_ResourceConfig_r17__helper1 : (forall a : IAB_ResourceConfig_r17__Type, IAB_ResourceConfig_r17__cond a -> IAB_ResourceConfig_r17__list_cond (IAB_ResourceConfig_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition IAB_ResourceConfig_r17__helper2 : (forall a : IAB_ResourceConfig_r17__Type, IAB_ResourceConfig_r17__F2 (IAB_ResourceConfig_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition IAB_ResourceConfig_r17__helper3 : (forall b : IAB_ResourceConfig_r17__list_type, IAB_ResourceConfig_r17__list_cond b -> IAB_ResourceConfig_r17__cond (IAB_ResourceConfig_r17__F2 b) /\ IAB_ResourceConfig_r17__F1 (IAB_ResourceConfig_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold IAB_ResourceConfig_r17__cond, IAB_ResourceConfig_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition IAB_ResourceConfig_r17__Format : T_Format IAB_ResourceConfig_r17__Type IAB_ResourceConfig_r17__cond :=
 proj2_format IAB_ResourceConfig_r17__cond IAB_ResourceConfig_r17__list_format  IAB_ResourceConfig_r17__F1 IAB_ResourceConfig_r17__F2 IAB_ResourceConfig_r17__helper1 IAB_ResourceConfig_r17__helper2 IAB_ResourceConfig_r17__helper3.

Opaque IAB_ResourceConfig_r17__cond IAB_ResourceConfig_r17__Format.

