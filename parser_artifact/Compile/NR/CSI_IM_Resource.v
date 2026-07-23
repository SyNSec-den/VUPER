Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_IM_ResourceId.

Opaque CSI_IM_ResourceId__cond CSI_IM_ResourceId__Format.

Inductive CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Type : Set :=
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s0
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s2
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s4
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s6
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s8
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s10
.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__cond := (fun (_ : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Type) => True).
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__nat__helper.

Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1 t :=
  match t with
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s0 => 0
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s2 => 1
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s4 => 2
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s6 => 3
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s8 => 4
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s10 => 5
  end.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F2 n :=
  match n with
  | 0 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s0
  | 1 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s2
  | 2 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s4
  | 3 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s6
  | 4 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s8
  | 5 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s10
  | _ => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__s0
  end.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1F2 : forall x : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Type, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1 x <= 5) /\ CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F2 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1 x) = x. imp_solve. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F2F1 : forall (y : nat) (H : y <= 5), CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__helper1 : (0 <= 12)%Z.  lia. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__helper2 : to_bit_sz (Z.to_nat (12 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (12 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__Type := Z.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__cond := (fun z => (0 <= z <= 12)%Z).
Record CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type : Set :=
  make__CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type {
    CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0 : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Type ;
    CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0 : Z ;
}.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list := (
 Nor CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__cond ::
 Nor Z CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__cond ::
 nil).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond z := 
  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0 z) /\
  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0 z) /\
  True.

Inductive CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Type : Set :=
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s0
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s4
 | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s8
.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__cond := (fun (_ : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Type) => True).
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__nat__helper.

Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1 t :=
  match t with
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s0 => 0
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s4 => 1
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s8 => 2
  end.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F2 n :=
  match n with
  | 0 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s0
  | 1 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s4
  | 2 => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s8
  | _ => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__s0
  end.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1F2 : forall x : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Type, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1 x <= 2) /\ CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F2 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1 x) = x. imp_solve. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F2F1 : forall (y : nat) (H : y <= 2), CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__Type := Z.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__cond := (fun z => (0 <= z <= 13)%Z).
Record CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type : Set :=
  make__CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type {
    CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1 : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Type ;
    CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1 : Z ;
}.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list := (
 Nor CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__cond ::
 Nor Z CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__cond ::
 nil).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond z := 
  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1 z) /\
  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1 z) /\
  True.


Inductive CSI_IM_Resource__csi_IM_ResourceElementPattern__Type : Set :=
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0 : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type -> CSI_IM_Resource__csi_IM_ResourceElementPattern__Type
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1 : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type -> CSI_IM_Resource__csi_IM_ResourceElementPattern__Type
.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__list : list typ := (
typ_cons CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond ::
typ_cons CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond ::
 nil).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__cond (c : CSI_IM_Resource__csi_IM_ResourceElementPattern__Type) := 
  match c with
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0 t => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond t 
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1 t => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond t 
  end.

Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__len_helper1 : to_bit_sz (length CSI_IM_Resource__csi_IM_ResourceElementPattern__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__len_helper2 : 2 <= length2 CSI_IM_Resource__csi_IM_ResourceElementPattern__list.
 simpl. lia. Qed.
Require Import NR.CSI_FrequencyOccupation.

Opaque CSI_FrequencyOccupation__cond CSI_FrequencyOccupation__Format.

Require Import NR.CSI_ResourcePeriodicityAndOffset.

Opaque CSI_ResourcePeriodicityAndOffset__cond CSI_ResourcePeriodicityAndOffset__Format.

Record CSI_IM_Resource__Type : Set :=
  make__CSI_IM_Resource__Type {
    CSI_IM_Resource__csi_IM_ResourceId : CSI_IM_ResourceId__Type ;
    CSI_IM_Resource__csi_IM_ResourceElementPattern : option CSI_IM_Resource__csi_IM_ResourceElementPattern__Type ;
    CSI_IM_Resource__freqBand : option CSI_FrequencyOccupation__Type ;
    CSI_IM_Resource__periodicityAndOffset : option CSI_ResourcePeriodicityAndOffset__Type ;
}.
Definition CSI_IM_Resource__root_list : list seq_elem := (
 Nor CSI_IM_ResourceId__Type CSI_IM_ResourceId__cond ::
 Opt CSI_IM_Resource__csi_IM_ResourceElementPattern__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__cond ::
 Opt CSI_FrequencyOccupation__Type CSI_FrequencyOccupation__cond ::
 Opt CSI_ResourcePeriodicityAndOffset__Type CSI_ResourcePeriodicityAndOffset__cond ::
 nil).
Definition CSI_IM_Resource__ext_list : list typ := (
  nil).
Definition CSI_IM_Resource__cond (z : CSI_IM_Resource__Type) := 
(  CSI_IM_ResourceId__cond (CSI_IM_Resource__csi_IM_ResourceId z) /\
  opt_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern z) /\
  opt_cond CSI_FrequencyOccupation__cond (CSI_IM_Resource__freqBand z) /\
  opt_cond CSI_ResourcePeriodicityAndOffset__cond (CSI_IM_Resource__periodicityAndOffset z) /\
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
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Format : T_Format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__nat__Format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F1F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__F2F1.

Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Format.

Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__Format : T_Format Z CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__cond :=
 ranged_int_format (0) (12) CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__helper1 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__helper2.

Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__Format.


Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format_Type := Eval cbn in seq_format_prod CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format_list : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format_Type :=
  (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0__Format, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0__Format, unit_format)).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list__Format := (*Eval compute in *) seq_format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format_list.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1 z :=
  (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__subcarrierLocation_p0 z, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__symbolLocation_p0 z, tt)).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2 (y : seq_type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type i0 i1
  end.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1F2_cond (z : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type)
  : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond z ->
  (seq_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1 z)).
intro H. unfold CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond in H. simpl. auto. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1F2_cond2 (z : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type)
 : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2F1_cond (y : seq_type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list)
  : seq_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list y ->
 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2 y)) /\  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond. simpl in *. auto.
 - simpl. unfold CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format : T_Format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond :=
        proj2_format  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__list__Format
    CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1F2_cond  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F1F2_cond2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__F2F1_cond.
Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format.

Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Format : T_Format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__nat__Format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F1F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__F2F1.

Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Format.

Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__Format : T_Format Z CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__cond :=
 ranged_int_format (0) (13) CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__helper1 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__helper2.

Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__Format.


Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format_Type := Eval cbn in seq_format_prod CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format_list : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format_Type :=
  (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1__Format, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1__Format, unit_format)).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list__Format := (*Eval compute in *) seq_format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format_list.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1 z :=
  (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__subcarrierLocation_p1 z, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__symbolLocation_p1 z, tt)).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2 (y : seq_type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type i0 i1
  end.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1F2_cond (z : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type)
  : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond z ->
  (seq_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1 z)).
intro H. unfold CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond in H. simpl. auto. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1F2_cond2 (z : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type)
 : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2F1_cond (y : seq_type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list)
  : seq_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list y ->
 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2 y)) /\  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1 (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond. simpl in *. auto.
 - simpl. unfold CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format : T_Format CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond :=
        proj2_format  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__list__Format
    CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1F2_cond  CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F1F2_cond2 CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__F2F1_cond.
Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format.


Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__Format_Type := Eval cbn in get_formats CSI_IM_Resource__csi_IM_ResourceElementPattern__list.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__Format_list : CSI_IM_Resource__csi_IM_ResourceElementPattern__Format_Type :=
  (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Format, (CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Format, unit__Format)).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__list__Format := Eval compute in choice_format CSI_IM_Resource__csi_IM_ResourceElementPattern__list CSI_IM_Resource__csi_IM_ResourceElementPattern__len_helper1 CSI_IM_Resource__csi_IM_ResourceElementPattern__len_helper2  CSI_IM_Resource__csi_IM_ResourceElementPattern__Format_list.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__F1 (z : CSI_IM_Resource__csi_IM_ResourceElementPattern__Type) : (choice CSI_IM_Resource__csi_IM_ResourceElementPattern__list) :=
  match z with
   | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0 t => existT _ 0 t
  | CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1 t => existT _ 1 t
  end.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__g := (fun n => typ_set (get_nth_typ CSI_IM_Resource__csi_IM_ResourceElementPattern__list n)).
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__F2 (y : choice CSI_IM_Resource__csi_IM_ResourceElementPattern__list) : CSI_IM_Resource__csi_IM_ResourceElementPattern__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_IM_Resource__csi_IM_ResourceElementPattern__g n -> CSI_IM_Resource__csi_IM_ResourceElementPattern__Type) with
    | 0 => fun (t : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0__Type) => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern0 t 
    | 1 => fun (t : CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1__Type) => CSI_IM_Resource__csi_IM_ResourceElementPattern__pattern1 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CSI_IM_Resource__csi_IM_ResourceElementPattern__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CSI_IM_Resource__csi_IM_ResourceElementPattern__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_IM_Resource__csi_IM_ResourceElementPattern__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CSI_IM_Resource__csi_IM_ResourceElementPattern__Type with end) n0
           end t0).

Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__helper2 :  forall (y : CSI_IM_Resource__csi_IM_ResourceElementPattern__Type), CSI_IM_Resource__csi_IM_ResourceElementPattern__cond y -> choice_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__list (CSI_IM_Resource__csi_IM_ResourceElementPattern__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__helper3 :  forall (y : CSI_IM_Resource__csi_IM_ResourceElementPattern__Type), CSI_IM_Resource__csi_IM_ResourceElementPattern__F2 (CSI_IM_Resource__csi_IM_ResourceElementPattern__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_IM_Resource__csi_IM_ResourceElementPattern__helper4 : (forall b : choice CSI_IM_Resource__csi_IM_ResourceElementPattern__list, choice_cond CSI_IM_Resource__csi_IM_ResourceElementPattern__list b -> CSI_IM_Resource__csi_IM_ResourceElementPattern__cond (CSI_IM_Resource__csi_IM_ResourceElementPattern__F2 b) /\ CSI_IM_Resource__csi_IM_ResourceElementPattern__F1 (CSI_IM_Resource__csi_IM_ResourceElementPattern__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_IM_Resource__csi_IM_ResourceElementPattern__F1 CSI_IM_Resource__csi_IM_ResourceElementPattern__F2.
Definition CSI_IM_Resource__csi_IM_ResourceElementPattern__Format : T_Format CSI_IM_Resource__csi_IM_ResourceElementPattern__Type CSI_IM_Resource__csi_IM_ResourceElementPattern__cond :=
  (* Eval compute in *) proj2_format CSI_IM_Resource__csi_IM_ResourceElementPattern__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__list__Format CSI_IM_Resource__csi_IM_ResourceElementPattern__F1 CSI_IM_Resource__csi_IM_ResourceElementPattern__F2 CSI_IM_Resource__csi_IM_ResourceElementPattern__helper2 CSI_IM_Resource__csi_IM_ResourceElementPattern__helper3 CSI_IM_Resource__csi_IM_ResourceElementPattern__helper4.
Opaque CSI_IM_Resource__csi_IM_ResourceElementPattern__cond CSI_IM_Resource__csi_IM_ResourceElementPattern__Format.


Definition CSI_IM_Resource__root_Format_Type := Eval cbn in seq_format_prod CSI_IM_Resource__root_list.
Definition CSI_IM_Resource__root_Format_list : CSI_IM_Resource__root_Format_Type :=
  (CSI_IM_ResourceId__Format, (CSI_IM_Resource__csi_IM_ResourceElementPattern__Format, (CSI_FrequencyOccupation__Format, (CSI_ResourcePeriodicityAndOffset__Format, unit_format)))).

Definition CSI_IM_Resource__ext_Format_Type := Eval cbn in get_formats CSI_IM_Resource__ext_list.
Definition CSI_IM_Resource__ext_Format_list : CSI_IM_Resource__ext_Format_Type :=
  unit__Format.

Definition CSI_IM_Resource__list_type : Set := (seq_type CSI_IM_Resource__root_list) * (seq_ext_type CSI_IM_Resource__ext_list).
Definition CSI_IM_Resource__list_cond (z : CSI_IM_Resource__list_type) : Prop :=
        (seq_cond CSI_IM_Resource__root_list (fst z)) /\ (seq_ext_cond CSI_IM_Resource__ext_list (snd z)).
Definition CSI_IM_Resource__list_format : T_Format CSI_IM_Resource__list_type CSI_IM_Resource__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_IM_Resource__root_list CSI_IM_Resource__root_Format_list CSI_IM_Resource__ext_list CSI_IM_Resource__ext_Format_list.

Opaque CSI_IM_Resource__list_format.
Definition CSI_IM_Resource__F1 (z : CSI_IM_Resource__Type) : CSI_IM_Resource__list_type :=
  (((CSI_IM_Resource__csi_IM_ResourceId z, (CSI_IM_Resource__csi_IM_ResourceElementPattern z, (CSI_IM_Resource__freqBand z, (CSI_IM_Resource__periodicityAndOffset z, tt))))), (
tt)).
Definition CSI_IM_Resource__F2 (y : CSI_IM_Resource__list_type) : CSI_IM_Resource__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__CSI_IM_Resource__Type j0 j1 j2 j3
  end.
Definition CSI_IM_Resource__helper1 : (forall a : CSI_IM_Resource__Type, CSI_IM_Resource__cond a -> CSI_IM_Resource__list_cond (CSI_IM_Resource__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_IM_Resource__helper2 : (forall a : CSI_IM_Resource__Type, CSI_IM_Resource__F2 (CSI_IM_Resource__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_IM_Resource__helper3 : (forall b : CSI_IM_Resource__list_type, CSI_IM_Resource__list_cond b -> CSI_IM_Resource__cond (CSI_IM_Resource__F2 b) /\ CSI_IM_Resource__F1 (CSI_IM_Resource__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_IM_Resource__cond, CSI_IM_Resource__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_IM_Resource__Format : T_Format CSI_IM_Resource__Type CSI_IM_Resource__cond :=
 proj2_format CSI_IM_Resource__cond CSI_IM_Resource__list_format  CSI_IM_Resource__F1 CSI_IM_Resource__F2 CSI_IM_Resource__helper1 CSI_IM_Resource__helper2 CSI_IM_Resource__helper3.

Opaque CSI_IM_Resource__cond CSI_IM_Resource__Format.

