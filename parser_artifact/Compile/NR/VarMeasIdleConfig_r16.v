Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.MeasIdleCarrierNR_r16.

Opaque MeasIdleCarrierNR_r16__cond MeasIdleCarrierNR_r16__Format.

Definition VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Type := list MeasIdleCarrierNR_r16__Type.

Lemma VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__helper1 : (0 <= 1 <= maxFreqIdle_r16)%Z. unfold maxFreqIdle_r16.
 lia. Qed.
Lemma VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__helper2 : to_bit_sz (Z.to_nat (maxFreqIdle_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFreqIdle_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__cond (z : VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxFreqIdle_r16)%Z /\ (list_and MeasIdleCarrierNR_r16__cond z) .

Require Import NR.MeasIdleCarrierEUTRA_r16.

Opaque MeasIdleCarrierEUTRA_r16__cond MeasIdleCarrierEUTRA_r16__Format.

Definition VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Type := list MeasIdleCarrierEUTRA_r16__Type.

Lemma VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__helper1 : (0 <= 1 <= maxFreqIdle_r16)%Z. unfold maxFreqIdle_r16.
 lia. Qed.
Lemma VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__helper2 : to_bit_sz (Z.to_nat (maxFreqIdle_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFreqIdle_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__cond (z : VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxFreqIdle_r16)%Z /\ (list_and MeasIdleCarrierEUTRA_r16__cond z) .

Inductive VarMeasIdleConfig_r16__measIdleDuration_r16__Type : Set :=
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec10
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec30
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec60
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec120
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec180
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec240
 | VarMeasIdleConfig_r16__measIdleDuration_r16__sec300
 | VarMeasIdleConfig_r16__measIdleDuration_r16__spare
.
Definition VarMeasIdleConfig_r16__measIdleDuration_r16__cond := (fun (_ : VarMeasIdleConfig_r16__measIdleDuration_r16__Type) => True).
Lemma VarMeasIdleConfig_r16__measIdleDuration_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VarMeasIdleConfig_r16__measIdleDuration_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 VarMeasIdleConfig_r16__measIdleDuration_r16__nat__helper.

Definition VarMeasIdleConfig_r16__measIdleDuration_r16__F1 t :=
  match t with
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec10 => 0
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec30 => 1
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec60 => 2
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec120 => 3
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec180 => 4
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec240 => 5
  | VarMeasIdleConfig_r16__measIdleDuration_r16__sec300 => 6
  | VarMeasIdleConfig_r16__measIdleDuration_r16__spare => 7
  end.
Definition VarMeasIdleConfig_r16__measIdleDuration_r16__F2 n :=
  match n with
  | 0 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec10
  | 1 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec30
  | 2 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec60
  | 3 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec120
  | 4 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec180
  | 5 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec240
  | 6 => VarMeasIdleConfig_r16__measIdleDuration_r16__sec300
  | 7 => VarMeasIdleConfig_r16__measIdleDuration_r16__spare
  | _ => VarMeasIdleConfig_r16__measIdleDuration_r16__sec10
  end.
Lemma VarMeasIdleConfig_r16__measIdleDuration_r16__F1F2 : forall x : VarMeasIdleConfig_r16__measIdleDuration_r16__Type, (VarMeasIdleConfig_r16__measIdleDuration_r16__F1 x <= 7) /\ VarMeasIdleConfig_r16__measIdleDuration_r16__F2 (VarMeasIdleConfig_r16__measIdleDuration_r16__F1 x) = x. imp_solve. Qed.
Lemma VarMeasIdleConfig_r16__measIdleDuration_r16__F2F1 : forall (y : nat) (H : y <= 7), VarMeasIdleConfig_r16__measIdleDuration_r16__F1 (VarMeasIdleConfig_r16__measIdleDuration_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ValidityAreaList_r16.

Opaque ValidityAreaList_r16__cond ValidityAreaList_r16__Format.

Record VarMeasIdleConfig_r16__Type : Set :=
  make__VarMeasIdleConfig_r16__Type {
    VarMeasIdleConfig_r16__measIdleCarrierListNR_r16 : option VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Type ;
    VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16 : option VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Type ;
    VarMeasIdleConfig_r16__measIdleDuration_r16 : VarMeasIdleConfig_r16__measIdleDuration_r16__Type ;
    VarMeasIdleConfig_r16__validityAreaList_r16 : option ValidityAreaList_r16__Type ;
}.
Definition VarMeasIdleConfig_r16__list := (
 Opt VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Type VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__cond ::
 Opt VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Type VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__cond ::
 Nor VarMeasIdleConfig_r16__measIdleDuration_r16__Type VarMeasIdleConfig_r16__measIdleDuration_r16__cond ::
 Opt ValidityAreaList_r16__Type ValidityAreaList_r16__cond ::
 nil).
Definition VarMeasIdleConfig_r16__cond z := 
  opt_cond VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__cond (VarMeasIdleConfig_r16__measIdleCarrierListNR_r16 z) /\
  opt_cond VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__cond (VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16 z) /\
  VarMeasIdleConfig_r16__measIdleDuration_r16__cond (VarMeasIdleConfig_r16__measIdleDuration_r16 z) /\
  opt_cond ValidityAreaList_r16__cond (VarMeasIdleConfig_r16__validityAreaList_r16 z) /\
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
Definition VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Format : T_Format VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Type VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__cond := seq_of_format MeasIdleCarrierNR_r16__Format 1 maxFreqIdle_r16 VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__helper1 VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__helper2.

Opaque VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__cond VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Format.

Definition VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Format : T_Format VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Type VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__cond := seq_of_format MeasIdleCarrierEUTRA_r16__Format 1 maxFreqIdle_r16 VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__helper1 VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__helper2.

Opaque VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__cond VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Format.

Definition VarMeasIdleConfig_r16__measIdleDuration_r16__Format : T_Format VarMeasIdleConfig_r16__measIdleDuration_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VarMeasIdleConfig_r16__measIdleDuration_r16__nat__Format VarMeasIdleConfig_r16__measIdleDuration_r16__F1 VarMeasIdleConfig_r16__measIdleDuration_r16__F2 VarMeasIdleConfig_r16__measIdleDuration_r16__F1F2 VarMeasIdleConfig_r16__measIdleDuration_r16__F2F1.

Opaque VarMeasIdleConfig_r16__measIdleDuration_r16__cond VarMeasIdleConfig_r16__measIdleDuration_r16__Format.


Definition VarMeasIdleConfig_r16__Format_Type := Eval cbn in seq_format_prod VarMeasIdleConfig_r16__list.
Definition VarMeasIdleConfig_r16__Format_list : VarMeasIdleConfig_r16__Format_Type :=
  (VarMeasIdleConfig_r16__measIdleCarrierListNR_r16__Format, (VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16__Format, (VarMeasIdleConfig_r16__measIdleDuration_r16__Format, (ValidityAreaList_r16__Format, unit_format)))).
Definition VarMeasIdleConfig_r16__list__Format := (*Eval compute in *) seq_format VarMeasIdleConfig_r16__list VarMeasIdleConfig_r16__Format_list.
Definition VarMeasIdleConfig_r16__F1 z :=
  (VarMeasIdleConfig_r16__measIdleCarrierListNR_r16 z, (VarMeasIdleConfig_r16__measIdleCarrierListEUTRA_r16 z, (VarMeasIdleConfig_r16__measIdleDuration_r16 z, (VarMeasIdleConfig_r16__validityAreaList_r16 z, tt)))).
Definition VarMeasIdleConfig_r16__F2 (y : seq_type VarMeasIdleConfig_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__VarMeasIdleConfig_r16__Type i0 i1 i2 i3
  end.
Lemma VarMeasIdleConfig_r16__F1F2_cond (z : VarMeasIdleConfig_r16__Type)
  : VarMeasIdleConfig_r16__cond z ->
  (seq_cond VarMeasIdleConfig_r16__list (VarMeasIdleConfig_r16__F1 z)).
intro H. unfold VarMeasIdleConfig_r16__cond in H. simpl. auto. Qed.
Lemma VarMeasIdleConfig_r16__F1F2_cond2 (z : VarMeasIdleConfig_r16__Type)
 : VarMeasIdleConfig_r16__F2 (VarMeasIdleConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarMeasIdleConfig_r16__F2F1_cond (y : seq_type VarMeasIdleConfig_r16__list)
  : seq_cond VarMeasIdleConfig_r16__list y ->
 (VarMeasIdleConfig_r16__cond (VarMeasIdleConfig_r16__F2 y)) /\  VarMeasIdleConfig_r16__F1 (VarMeasIdleConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarMeasIdleConfig_r16__cond. simpl in *. auto.
 - simpl. unfold VarMeasIdleConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarMeasIdleConfig_r16__Format : T_Format VarMeasIdleConfig_r16__Type VarMeasIdleConfig_r16__cond :=
        proj2_format  VarMeasIdleConfig_r16__cond VarMeasIdleConfig_r16__list__Format
    VarMeasIdleConfig_r16__F1 VarMeasIdleConfig_r16__F2 VarMeasIdleConfig_r16__F1F2_cond  VarMeasIdleConfig_r16__F1F2_cond2 VarMeasIdleConfig_r16__F2F1_cond.
Opaque VarMeasIdleConfig_r16__cond VarMeasIdleConfig_r16__Format.

