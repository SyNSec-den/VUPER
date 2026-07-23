Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MCCH_RepetitionPeriodAndOffset_r17.

Opaque MCCH_RepetitionPeriodAndOffset_r17__cond MCCH_RepetitionPeriodAndOffset_r17__Format.

Lemma MCCH_Config_r17__mcch_WindowStartSlot_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma MCCH_Config_r17__mcch_WindowStartSlot_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_Config_r17__mcch_WindowStartSlot_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_Config_r17__mcch_WindowStartSlot_r17__Type := Z.
Definition MCCH_Config_r17__mcch_WindowStartSlot_r17__cond := (fun z => (0 <= z <= 79)%Z).
Inductive MCCH_Config_r17__mcch_WindowDuration_r17__Type : Set :=
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl2
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl4
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl8
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl10
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl20
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl40
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl80
 | MCCH_Config_r17__mcch_WindowDuration_r17__sl160
.
Definition MCCH_Config_r17__mcch_WindowDuration_r17__cond := (fun (_ : MCCH_Config_r17__mcch_WindowDuration_r17__Type) => True).
Lemma MCCH_Config_r17__mcch_WindowDuration_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MCCH_Config_r17__mcch_WindowDuration_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MCCH_Config_r17__mcch_WindowDuration_r17__nat__helper.

Definition MCCH_Config_r17__mcch_WindowDuration_r17__F1 t :=
  match t with
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl2 => 0
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl4 => 1
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl8 => 2
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl10 => 3
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl20 => 4
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl40 => 5
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl80 => 6
  | MCCH_Config_r17__mcch_WindowDuration_r17__sl160 => 7
  end.
Definition MCCH_Config_r17__mcch_WindowDuration_r17__F2 n :=
  match n with
  | 0 => MCCH_Config_r17__mcch_WindowDuration_r17__sl2
  | 1 => MCCH_Config_r17__mcch_WindowDuration_r17__sl4
  | 2 => MCCH_Config_r17__mcch_WindowDuration_r17__sl8
  | 3 => MCCH_Config_r17__mcch_WindowDuration_r17__sl10
  | 4 => MCCH_Config_r17__mcch_WindowDuration_r17__sl20
  | 5 => MCCH_Config_r17__mcch_WindowDuration_r17__sl40
  | 6 => MCCH_Config_r17__mcch_WindowDuration_r17__sl80
  | 7 => MCCH_Config_r17__mcch_WindowDuration_r17__sl160
  | _ => MCCH_Config_r17__mcch_WindowDuration_r17__sl2
  end.
Lemma MCCH_Config_r17__mcch_WindowDuration_r17__F1F2 : forall x : MCCH_Config_r17__mcch_WindowDuration_r17__Type, (MCCH_Config_r17__mcch_WindowDuration_r17__F1 x <= 7) /\ MCCH_Config_r17__mcch_WindowDuration_r17__F2 (MCCH_Config_r17__mcch_WindowDuration_r17__F1 x) = x. imp_solve. Qed.
Lemma MCCH_Config_r17__mcch_WindowDuration_r17__F2F1 : forall (y : nat) (H : y <= 7), MCCH_Config_r17__mcch_WindowDuration_r17__F1 (MCCH_Config_r17__mcch_WindowDuration_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MCCH_Config_r17__mcch_ModificationPeriod_r17__Type : Set :=
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf2
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf4
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf8
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf16
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf32
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf64
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf128
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf256
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf512
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf1024
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__r2048
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf4096
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf8192
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf16384
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf32768
 | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf65536
.
Definition MCCH_Config_r17__mcch_ModificationPeriod_r17__cond := (fun (_ : MCCH_Config_r17__mcch_ModificationPeriod_r17__Type) => True).
Lemma MCCH_Config_r17__mcch_ModificationPeriod_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MCCH_Config_r17__mcch_ModificationPeriod_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 MCCH_Config_r17__mcch_ModificationPeriod_r17__nat__helper.

Definition MCCH_Config_r17__mcch_ModificationPeriod_r17__F1 t :=
  match t with
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf2 => 0
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf4 => 1
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf8 => 2
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf16 => 3
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf32 => 4
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf64 => 5
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf128 => 6
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf256 => 7
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf512 => 8
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf1024 => 9
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__r2048 => 10
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf4096 => 11
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf8192 => 12
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf16384 => 13
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf32768 => 14
  | MCCH_Config_r17__mcch_ModificationPeriod_r17__rf65536 => 15
  end.
Definition MCCH_Config_r17__mcch_ModificationPeriod_r17__F2 n :=
  match n with
  | 0 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf2
  | 1 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf4
  | 2 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf8
  | 3 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf16
  | 4 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf32
  | 5 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf64
  | 6 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf128
  | 7 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf256
  | 8 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf512
  | 9 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf1024
  | 10 => MCCH_Config_r17__mcch_ModificationPeriod_r17__r2048
  | 11 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf4096
  | 12 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf8192
  | 13 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf16384
  | 14 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf32768
  | 15 => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf65536
  | _ => MCCH_Config_r17__mcch_ModificationPeriod_r17__rf2
  end.
Lemma MCCH_Config_r17__mcch_ModificationPeriod_r17__F1F2 : forall x : MCCH_Config_r17__mcch_ModificationPeriod_r17__Type, (MCCH_Config_r17__mcch_ModificationPeriod_r17__F1 x <= 15) /\ MCCH_Config_r17__mcch_ModificationPeriod_r17__F2 (MCCH_Config_r17__mcch_ModificationPeriod_r17__F1 x) = x. imp_solve. Qed.
Lemma MCCH_Config_r17__mcch_ModificationPeriod_r17__F2F1 : forall (y : nat) (H : y <= 15), MCCH_Config_r17__mcch_ModificationPeriod_r17__F1 (MCCH_Config_r17__mcch_ModificationPeriod_r17__F2 y) = y. enum_solve H y. Qed.

Record MCCH_Config_r17__Type : Set :=
  make__MCCH_Config_r17__Type {
    MCCH_Config_r17__mcch_RepetitionPeriodAndOffset_r17 : MCCH_RepetitionPeriodAndOffset_r17__Type ;
    MCCH_Config_r17__mcch_WindowStartSlot_r17 : Z ;
    MCCH_Config_r17__mcch_WindowDuration_r17 : option MCCH_Config_r17__mcch_WindowDuration_r17__Type ;
    MCCH_Config_r17__mcch_ModificationPeriod_r17 : MCCH_Config_r17__mcch_ModificationPeriod_r17__Type ;
}.
Definition MCCH_Config_r17__list := (
 Nor MCCH_RepetitionPeriodAndOffset_r17__Type MCCH_RepetitionPeriodAndOffset_r17__cond ::
 Nor Z MCCH_Config_r17__mcch_WindowStartSlot_r17__cond ::
 Opt MCCH_Config_r17__mcch_WindowDuration_r17__Type MCCH_Config_r17__mcch_WindowDuration_r17__cond ::
 Nor MCCH_Config_r17__mcch_ModificationPeriod_r17__Type MCCH_Config_r17__mcch_ModificationPeriod_r17__cond ::
 nil).
Definition MCCH_Config_r17__cond z := 
  MCCH_RepetitionPeriodAndOffset_r17__cond (MCCH_Config_r17__mcch_RepetitionPeriodAndOffset_r17 z) /\
  MCCH_Config_r17__mcch_WindowStartSlot_r17__cond (MCCH_Config_r17__mcch_WindowStartSlot_r17 z) /\
  opt_cond MCCH_Config_r17__mcch_WindowDuration_r17__cond (MCCH_Config_r17__mcch_WindowDuration_r17 z) /\
  MCCH_Config_r17__mcch_ModificationPeriod_r17__cond (MCCH_Config_r17__mcch_ModificationPeriod_r17 z) /\
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
Definition MCCH_Config_r17__mcch_WindowStartSlot_r17__Format : T_Format Z MCCH_Config_r17__mcch_WindowStartSlot_r17__cond :=
 ranged_int_format (0) (79) MCCH_Config_r17__mcch_WindowStartSlot_r17__helper1 MCCH_Config_r17__mcch_WindowStartSlot_r17__helper2.

Opaque MCCH_Config_r17__mcch_WindowStartSlot_r17__cond MCCH_Config_r17__mcch_WindowStartSlot_r17__Format.

Definition MCCH_Config_r17__mcch_WindowDuration_r17__Format : T_Format MCCH_Config_r17__mcch_WindowDuration_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MCCH_Config_r17__mcch_WindowDuration_r17__nat__Format MCCH_Config_r17__mcch_WindowDuration_r17__F1 MCCH_Config_r17__mcch_WindowDuration_r17__F2 MCCH_Config_r17__mcch_WindowDuration_r17__F1F2 MCCH_Config_r17__mcch_WindowDuration_r17__F2F1.

Opaque MCCH_Config_r17__mcch_WindowDuration_r17__cond MCCH_Config_r17__mcch_WindowDuration_r17__Format.

Definition MCCH_Config_r17__mcch_ModificationPeriod_r17__Format : T_Format MCCH_Config_r17__mcch_ModificationPeriod_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MCCH_Config_r17__mcch_ModificationPeriod_r17__nat__Format MCCH_Config_r17__mcch_ModificationPeriod_r17__F1 MCCH_Config_r17__mcch_ModificationPeriod_r17__F2 MCCH_Config_r17__mcch_ModificationPeriod_r17__F1F2 MCCH_Config_r17__mcch_ModificationPeriod_r17__F2F1.

Opaque MCCH_Config_r17__mcch_ModificationPeriod_r17__cond MCCH_Config_r17__mcch_ModificationPeriod_r17__Format.


Definition MCCH_Config_r17__Format_Type := Eval cbn in seq_format_prod MCCH_Config_r17__list.
Definition MCCH_Config_r17__Format_list : MCCH_Config_r17__Format_Type :=
  (MCCH_RepetitionPeriodAndOffset_r17__Format, (MCCH_Config_r17__mcch_WindowStartSlot_r17__Format, (MCCH_Config_r17__mcch_WindowDuration_r17__Format, (MCCH_Config_r17__mcch_ModificationPeriod_r17__Format, unit_format)))).
Definition MCCH_Config_r17__list__Format := (*Eval compute in *) seq_format MCCH_Config_r17__list MCCH_Config_r17__Format_list.
Definition MCCH_Config_r17__F1 z :=
  (MCCH_Config_r17__mcch_RepetitionPeriodAndOffset_r17 z, (MCCH_Config_r17__mcch_WindowStartSlot_r17 z, (MCCH_Config_r17__mcch_WindowDuration_r17 z, (MCCH_Config_r17__mcch_ModificationPeriod_r17 z, tt)))).
Definition MCCH_Config_r17__F2 (y : seq_type MCCH_Config_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MCCH_Config_r17__Type i0 i1 i2 i3
  end.
Lemma MCCH_Config_r17__F1F2_cond (z : MCCH_Config_r17__Type)
  : MCCH_Config_r17__cond z ->
  (seq_cond MCCH_Config_r17__list (MCCH_Config_r17__F1 z)).
intro H. unfold MCCH_Config_r17__cond in H. simpl. auto. Qed.
Lemma MCCH_Config_r17__F1F2_cond2 (z : MCCH_Config_r17__Type)
 : MCCH_Config_r17__F2 (MCCH_Config_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MCCH_Config_r17__F2F1_cond (y : seq_type MCCH_Config_r17__list)
  : seq_cond MCCH_Config_r17__list y ->
 (MCCH_Config_r17__cond (MCCH_Config_r17__F2 y)) /\  MCCH_Config_r17__F1 (MCCH_Config_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MCCH_Config_r17__cond. simpl in *. auto.
 - simpl. unfold MCCH_Config_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MCCH_Config_r17__Format : T_Format MCCH_Config_r17__Type MCCH_Config_r17__cond :=
        proj2_format  MCCH_Config_r17__cond MCCH_Config_r17__list__Format
    MCCH_Config_r17__F1 MCCH_Config_r17__F2 MCCH_Config_r17__F1F2_cond  MCCH_Config_r17__F1F2_cond2 MCCH_Config_r17__F2F1_cond.
Opaque MCCH_Config_r17__cond MCCH_Config_r17__Format.

