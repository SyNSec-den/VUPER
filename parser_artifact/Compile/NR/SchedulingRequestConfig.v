Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SchedulingRequestToAddMod.

Opaque SchedulingRequestToAddMod__cond SchedulingRequestToAddMod__Format.

Definition SchedulingRequestConfig__schedulingRequestToAddModList__Type := list SchedulingRequestToAddMod__Type.

Lemma SchedulingRequestConfig__schedulingRequestToAddModList__helper1 : (0 <= 1 <= maxNrofSR_ConfigPerCellGroup)%Z. unfold maxNrofSR_ConfigPerCellGroup.
 lia. Qed.
Lemma SchedulingRequestConfig__schedulingRequestToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_ConfigPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_ConfigPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestConfig__schedulingRequestToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestConfig__schedulingRequestToAddModList__cond (z : SchedulingRequestConfig__schedulingRequestToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_ConfigPerCellGroup)%Z /\ (list_and SchedulingRequestToAddMod__cond z) .

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Definition SchedulingRequestConfig__schedulingRequestToReleaseList__Type := list SchedulingRequestId__Type.

Lemma SchedulingRequestConfig__schedulingRequestToReleaseList__helper1 : (0 <= 1 <= maxNrofSR_ConfigPerCellGroup)%Z. unfold maxNrofSR_ConfigPerCellGroup.
 lia. Qed.
Lemma SchedulingRequestConfig__schedulingRequestToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_ConfigPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_ConfigPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestConfig__schedulingRequestToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestConfig__schedulingRequestToReleaseList__cond (z : SchedulingRequestConfig__schedulingRequestToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_ConfigPerCellGroup)%Z /\ (list_and SchedulingRequestId__cond z) .

Record SchedulingRequestConfig__Type : Set :=
  make__SchedulingRequestConfig__Type {
    SchedulingRequestConfig__schedulingRequestToAddModList : option SchedulingRequestConfig__schedulingRequestToAddModList__Type ;
    SchedulingRequestConfig__schedulingRequestToReleaseList : option SchedulingRequestConfig__schedulingRequestToReleaseList__Type ;
}.
Definition SchedulingRequestConfig__list := (
 Opt SchedulingRequestConfig__schedulingRequestToAddModList__Type SchedulingRequestConfig__schedulingRequestToAddModList__cond ::
 Opt SchedulingRequestConfig__schedulingRequestToReleaseList__Type SchedulingRequestConfig__schedulingRequestToReleaseList__cond ::
 nil).
Definition SchedulingRequestConfig__cond z := 
  opt_cond SchedulingRequestConfig__schedulingRequestToAddModList__cond (SchedulingRequestConfig__schedulingRequestToAddModList z) /\
  opt_cond SchedulingRequestConfig__schedulingRequestToReleaseList__cond (SchedulingRequestConfig__schedulingRequestToReleaseList z) /\
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
Definition SchedulingRequestConfig__schedulingRequestToAddModList__Format : T_Format SchedulingRequestConfig__schedulingRequestToAddModList__Type SchedulingRequestConfig__schedulingRequestToAddModList__cond := seq_of_format SchedulingRequestToAddMod__Format 1 maxNrofSR_ConfigPerCellGroup SchedulingRequestConfig__schedulingRequestToAddModList__helper1 SchedulingRequestConfig__schedulingRequestToAddModList__helper2.

Opaque SchedulingRequestConfig__schedulingRequestToAddModList__cond SchedulingRequestConfig__schedulingRequestToAddModList__Format.

Definition SchedulingRequestConfig__schedulingRequestToReleaseList__Format : T_Format SchedulingRequestConfig__schedulingRequestToReleaseList__Type SchedulingRequestConfig__schedulingRequestToReleaseList__cond := seq_of_format SchedulingRequestId__Format 1 maxNrofSR_ConfigPerCellGroup SchedulingRequestConfig__schedulingRequestToReleaseList__helper1 SchedulingRequestConfig__schedulingRequestToReleaseList__helper2.

Opaque SchedulingRequestConfig__schedulingRequestToReleaseList__cond SchedulingRequestConfig__schedulingRequestToReleaseList__Format.


Definition SchedulingRequestConfig__Format_Type := Eval cbn in seq_format_prod SchedulingRequestConfig__list.
Definition SchedulingRequestConfig__Format_list : SchedulingRequestConfig__Format_Type :=
  (SchedulingRequestConfig__schedulingRequestToAddModList__Format, (SchedulingRequestConfig__schedulingRequestToReleaseList__Format, unit_format)).
Definition SchedulingRequestConfig__list__Format := (*Eval compute in *) seq_format SchedulingRequestConfig__list SchedulingRequestConfig__Format_list.
Definition SchedulingRequestConfig__F1 z :=
  (SchedulingRequestConfig__schedulingRequestToAddModList z, (SchedulingRequestConfig__schedulingRequestToReleaseList z, tt)).
Definition SchedulingRequestConfig__F2 (y : seq_type SchedulingRequestConfig__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SchedulingRequestConfig__Type i0 i1
  end.
Lemma SchedulingRequestConfig__F1F2_cond (z : SchedulingRequestConfig__Type)
  : SchedulingRequestConfig__cond z ->
  (seq_cond SchedulingRequestConfig__list (SchedulingRequestConfig__F1 z)).
intro H. unfold SchedulingRequestConfig__cond in H. simpl. auto. Qed.
Lemma SchedulingRequestConfig__F1F2_cond2 (z : SchedulingRequestConfig__Type)
 : SchedulingRequestConfig__F2 (SchedulingRequestConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingRequestConfig__F2F1_cond (y : seq_type SchedulingRequestConfig__list)
  : seq_cond SchedulingRequestConfig__list y ->
 (SchedulingRequestConfig__cond (SchedulingRequestConfig__F2 y)) /\  SchedulingRequestConfig__F1 (SchedulingRequestConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingRequestConfig__cond. simpl in *. auto.
 - simpl. unfold SchedulingRequestConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingRequestConfig__Format : T_Format SchedulingRequestConfig__Type SchedulingRequestConfig__cond :=
        proj2_format  SchedulingRequestConfig__cond SchedulingRequestConfig__list__Format
    SchedulingRequestConfig__F1 SchedulingRequestConfig__F2 SchedulingRequestConfig__F1F2_cond  SchedulingRequestConfig__F1F2_cond2 SchedulingRequestConfig__F2F1_cond.
Opaque SchedulingRequestConfig__cond SchedulingRequestConfig__Format.

