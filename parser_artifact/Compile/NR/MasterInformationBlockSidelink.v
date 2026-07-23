Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Definition MasterInformationBlockSidelink__sl_TDD_Config_r16__Type := bit_string_fixed.
Definition MasterInformationBlockSidelink__sl_TDD_Config_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 12 /\ bit_string_len_prop (fst z) (snd z)).
Definition MasterInformationBlockSidelink__directFrameNumber_r16__Type := bit_string_fixed.
Definition MasterInformationBlockSidelink__directFrameNumber_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition MasterInformationBlockSidelink__slotIndex_r16__Type := bit_string_fixed.
Definition MasterInformationBlockSidelink__slotIndex_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 7 /\ bit_string_len_prop (fst z) (snd z)).
Definition MasterInformationBlockSidelink__reservedBits_r16__Type := bit_string_fixed.
Definition MasterInformationBlockSidelink__reservedBits_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Record MasterInformationBlockSidelink__Type : Set :=
  make__MasterInformationBlockSidelink__Type {
    MasterInformationBlockSidelink__sl_TDD_Config_r16 : MasterInformationBlockSidelink__sl_TDD_Config_r16__Type ;
    MasterInformationBlockSidelink__inCoverage_r16 : bool ;
    MasterInformationBlockSidelink__directFrameNumber_r16 : MasterInformationBlockSidelink__directFrameNumber_r16__Type ;
    MasterInformationBlockSidelink__slotIndex_r16 : MasterInformationBlockSidelink__slotIndex_r16__Type ;
    MasterInformationBlockSidelink__reservedBits_r16 : MasterInformationBlockSidelink__reservedBits_r16__Type ;
}.
Definition MasterInformationBlockSidelink__list := (
 Nor MasterInformationBlockSidelink__sl_TDD_Config_r16__Type MasterInformationBlockSidelink__sl_TDD_Config_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor MasterInformationBlockSidelink__directFrameNumber_r16__Type MasterInformationBlockSidelink__directFrameNumber_r16__cond ::
 Nor MasterInformationBlockSidelink__slotIndex_r16__Type MasterInformationBlockSidelink__slotIndex_r16__cond ::
 Nor MasterInformationBlockSidelink__reservedBits_r16__Type MasterInformationBlockSidelink__reservedBits_r16__cond ::
 nil).
Definition MasterInformationBlockSidelink__cond z := 
  MasterInformationBlockSidelink__sl_TDD_Config_r16__cond (MasterInformationBlockSidelink__sl_TDD_Config_r16 z) /\
  (fun _ => True) (MasterInformationBlockSidelink__inCoverage_r16 z) /\
  MasterInformationBlockSidelink__directFrameNumber_r16__cond (MasterInformationBlockSidelink__directFrameNumber_r16 z) /\
  MasterInformationBlockSidelink__slotIndex_r16__cond (MasterInformationBlockSidelink__slotIndex_r16 z) /\
  MasterInformationBlockSidelink__reservedBits_r16__cond (MasterInformationBlockSidelink__reservedBits_r16 z) /\
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
Definition MasterInformationBlockSidelink__sl_TDD_Config_r16__Format : T_Format MasterInformationBlockSidelink__sl_TDD_Config_r16__Type MasterInformationBlockSidelink__sl_TDD_Config_r16__cond := (* Eval compute in *) bit_string_fixed_format 12.
Opaque MasterInformationBlockSidelink__sl_TDD_Config_r16__cond MasterInformationBlockSidelink__sl_TDD_Config_r16__Format.

Definition MasterInformationBlockSidelink__directFrameNumber_r16__Format : T_Format MasterInformationBlockSidelink__directFrameNumber_r16__Type MasterInformationBlockSidelink__directFrameNumber_r16__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque MasterInformationBlockSidelink__directFrameNumber_r16__cond MasterInformationBlockSidelink__directFrameNumber_r16__Format.

Definition MasterInformationBlockSidelink__slotIndex_r16__Format : T_Format MasterInformationBlockSidelink__slotIndex_r16__Type MasterInformationBlockSidelink__slotIndex_r16__cond := (* Eval compute in *) bit_string_fixed_format 7.
Opaque MasterInformationBlockSidelink__slotIndex_r16__cond MasterInformationBlockSidelink__slotIndex_r16__Format.

Definition MasterInformationBlockSidelink__reservedBits_r16__Format : T_Format MasterInformationBlockSidelink__reservedBits_r16__Type MasterInformationBlockSidelink__reservedBits_r16__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque MasterInformationBlockSidelink__reservedBits_r16__cond MasterInformationBlockSidelink__reservedBits_r16__Format.


Definition MasterInformationBlockSidelink__Format_Type := Eval cbn in seq_format_prod MasterInformationBlockSidelink__list.
Definition MasterInformationBlockSidelink__Format_list : MasterInformationBlockSidelink__Format_Type :=
  (MasterInformationBlockSidelink__sl_TDD_Config_r16__Format, (bool__Format, (MasterInformationBlockSidelink__directFrameNumber_r16__Format, (MasterInformationBlockSidelink__slotIndex_r16__Format, (MasterInformationBlockSidelink__reservedBits_r16__Format, unit_format))))).
Definition MasterInformationBlockSidelink__list__Format := (*Eval compute in *) seq_format MasterInformationBlockSidelink__list MasterInformationBlockSidelink__Format_list.
Definition MasterInformationBlockSidelink__F1 z :=
  (MasterInformationBlockSidelink__sl_TDD_Config_r16 z, (MasterInformationBlockSidelink__inCoverage_r16 z, (MasterInformationBlockSidelink__directFrameNumber_r16 z, (MasterInformationBlockSidelink__slotIndex_r16 z, (MasterInformationBlockSidelink__reservedBits_r16 z, tt))))).
Definition MasterInformationBlockSidelink__F2 (y : seq_type MasterInformationBlockSidelink__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MasterInformationBlockSidelink__Type i0 i1 i2 i3 i4
  end.
Lemma MasterInformationBlockSidelink__F1F2_cond (z : MasterInformationBlockSidelink__Type)
  : MasterInformationBlockSidelink__cond z ->
  (seq_cond MasterInformationBlockSidelink__list (MasterInformationBlockSidelink__F1 z)).
intro H. unfold MasterInformationBlockSidelink__cond in H. simpl. auto. Qed.
Lemma MasterInformationBlockSidelink__F1F2_cond2 (z : MasterInformationBlockSidelink__Type)
 : MasterInformationBlockSidelink__F2 (MasterInformationBlockSidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MasterInformationBlockSidelink__F2F1_cond (y : seq_type MasterInformationBlockSidelink__list)
  : seq_cond MasterInformationBlockSidelink__list y ->
 (MasterInformationBlockSidelink__cond (MasterInformationBlockSidelink__F2 y)) /\  MasterInformationBlockSidelink__F1 (MasterInformationBlockSidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MasterInformationBlockSidelink__cond. simpl in *. auto.
 - simpl. unfold MasterInformationBlockSidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MasterInformationBlockSidelink__Format : T_Format MasterInformationBlockSidelink__Type MasterInformationBlockSidelink__cond :=
        proj2_format  MasterInformationBlockSidelink__cond MasterInformationBlockSidelink__list__Format
    MasterInformationBlockSidelink__F1 MasterInformationBlockSidelink__F2 MasterInformationBlockSidelink__F1F2_cond  MasterInformationBlockSidelink__F1F2_cond2 MasterInformationBlockSidelink__F2F1_cond.
Opaque MasterInformationBlockSidelink__cond MasterInformationBlockSidelink__Format.

