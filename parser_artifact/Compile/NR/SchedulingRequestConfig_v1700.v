Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SchedulingRequestToAddModExt_v1700.

Opaque SchedulingRequestToAddModExt_v1700__cond SchedulingRequestToAddModExt_v1700__Format.

Definition SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Type := list SchedulingRequestToAddModExt_v1700__Type.

Lemma SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__helper1 : (0 <= 1 <= maxNrofSR_ConfigPerCellGroup)%Z. unfold maxNrofSR_ConfigPerCellGroup.
 lia. Qed.
Lemma SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_ConfigPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_ConfigPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__cond (z : SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_ConfigPerCellGroup)%Z /\ (list_and SchedulingRequestToAddModExt_v1700__cond z) .

Record SchedulingRequestConfig_v1700__Type : Set :=
  make__SchedulingRequestConfig_v1700__Type {
    SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700 : option SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Type ;
}.
Definition SchedulingRequestConfig_v1700__list := (
 Opt SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Type SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__cond ::
 nil).
Definition SchedulingRequestConfig_v1700__cond z := 
  opt_cond SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__cond (SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700 z) /\
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
Definition SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Format : T_Format SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Type SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__cond := seq_of_format SchedulingRequestToAddModExt_v1700__Format 1 maxNrofSR_ConfigPerCellGroup SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__helper1 SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__helper2.

Opaque SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__cond SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Format.


Definition SchedulingRequestConfig_v1700__Format_Type := Eval cbn in seq_format_prod SchedulingRequestConfig_v1700__list.
Definition SchedulingRequestConfig_v1700__Format_list : SchedulingRequestConfig_v1700__Format_Type :=
  (SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700__Format, unit_format).
Definition SchedulingRequestConfig_v1700__list__Format := (*Eval compute in *) seq_format SchedulingRequestConfig_v1700__list SchedulingRequestConfig_v1700__Format_list.
Definition SchedulingRequestConfig_v1700__F1 z :=
  (SchedulingRequestConfig_v1700__schedulingRequestToAddModListExt_v1700 z, tt).
Definition SchedulingRequestConfig_v1700__F2 (y : seq_type SchedulingRequestConfig_v1700__list) :=
  match y with
  | (i0, _)=>
    make__SchedulingRequestConfig_v1700__Type i0
  end.
Lemma SchedulingRequestConfig_v1700__F1F2_cond (z : SchedulingRequestConfig_v1700__Type)
  : SchedulingRequestConfig_v1700__cond z ->
  (seq_cond SchedulingRequestConfig_v1700__list (SchedulingRequestConfig_v1700__F1 z)).
intro H. unfold SchedulingRequestConfig_v1700__cond in H. simpl. auto. Qed.
Lemma SchedulingRequestConfig_v1700__F1F2_cond2 (z : SchedulingRequestConfig_v1700__Type)
 : SchedulingRequestConfig_v1700__F2 (SchedulingRequestConfig_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingRequestConfig_v1700__F2F1_cond (y : seq_type SchedulingRequestConfig_v1700__list)
  : seq_cond SchedulingRequestConfig_v1700__list y ->
 (SchedulingRequestConfig_v1700__cond (SchedulingRequestConfig_v1700__F2 y)) /\  SchedulingRequestConfig_v1700__F1 (SchedulingRequestConfig_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingRequestConfig_v1700__cond. simpl in *. auto.
 - simpl. unfold SchedulingRequestConfig_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingRequestConfig_v1700__Format : T_Format SchedulingRequestConfig_v1700__Type SchedulingRequestConfig_v1700__cond :=
        proj2_format  SchedulingRequestConfig_v1700__cond SchedulingRequestConfig_v1700__list__Format
    SchedulingRequestConfig_v1700__F1 SchedulingRequestConfig_v1700__F2 SchedulingRequestConfig_v1700__F1F2_cond  SchedulingRequestConfig_v1700__F1F2_cond2 SchedulingRequestConfig_v1700__F2F1_cond.
Opaque SchedulingRequestConfig_v1700__cond SchedulingRequestConfig_v1700__Format.

