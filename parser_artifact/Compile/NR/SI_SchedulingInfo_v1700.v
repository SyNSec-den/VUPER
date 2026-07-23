Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SchedulingInfo2_r17.

Opaque SchedulingInfo2_r17__cond SchedulingInfo2_r17__Format.

Definition SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Type := list SchedulingInfo2_r17__Type.

Lemma SI_SchedulingInfo_v1700__schedulingInfoList2_r17__helper1 : (0 <= 1 <= maxSI_Message)%Z. unfold maxSI_Message.
 lia. Qed.
Lemma SI_SchedulingInfo_v1700__schedulingInfoList2_r17__helper2 : to_bit_sz (Z.to_nat (maxSI_Message - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSI_Message - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SI_SchedulingInfo_v1700__schedulingInfoList2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SI_SchedulingInfo_v1700__schedulingInfoList2_r17__cond (z : SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSI_Message)%Z /\ (list_and SchedulingInfo2_r17__cond z) .

Require Import NR.SI_RequestConfig.

Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

Record SI_SchedulingInfo_v1700__Type : Set :=
  make__SI_SchedulingInfo_v1700__Type {
    SI_SchedulingInfo_v1700__schedulingInfoList2_r17 : SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Type ;
    SI_SchedulingInfo_v1700__si_RequestConfigRedCap_r17 : option SI_RequestConfig__Type ;
}.
Definition SI_SchedulingInfo_v1700__list := (
 Nor SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Type SI_SchedulingInfo_v1700__schedulingInfoList2_r17__cond ::
 Opt SI_RequestConfig__Type SI_RequestConfig__cond ::
 nil).
Definition SI_SchedulingInfo_v1700__cond z := 
  SI_SchedulingInfo_v1700__schedulingInfoList2_r17__cond (SI_SchedulingInfo_v1700__schedulingInfoList2_r17 z) /\
  opt_cond SI_RequestConfig__cond (SI_SchedulingInfo_v1700__si_RequestConfigRedCap_r17 z) /\
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
Definition SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Format : T_Format SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Type SI_SchedulingInfo_v1700__schedulingInfoList2_r17__cond := seq_of_format SchedulingInfo2_r17__Format 1 maxSI_Message SI_SchedulingInfo_v1700__schedulingInfoList2_r17__helper1 SI_SchedulingInfo_v1700__schedulingInfoList2_r17__helper2.

Opaque SI_SchedulingInfo_v1700__schedulingInfoList2_r17__cond SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Format.


Definition SI_SchedulingInfo_v1700__Format_Type := Eval cbn in seq_format_prod SI_SchedulingInfo_v1700__list.
Definition SI_SchedulingInfo_v1700__Format_list : SI_SchedulingInfo_v1700__Format_Type :=
  (SI_SchedulingInfo_v1700__schedulingInfoList2_r17__Format, (SI_RequestConfig__Format, unit_format)).
Definition SI_SchedulingInfo_v1700__list__Format := (*Eval compute in *) seq_format SI_SchedulingInfo_v1700__list SI_SchedulingInfo_v1700__Format_list.
Definition SI_SchedulingInfo_v1700__F1 z :=
  (SI_SchedulingInfo_v1700__schedulingInfoList2_r17 z, (SI_SchedulingInfo_v1700__si_RequestConfigRedCap_r17 z, tt)).
Definition SI_SchedulingInfo_v1700__F2 (y : seq_type SI_SchedulingInfo_v1700__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SI_SchedulingInfo_v1700__Type i0 i1
  end.
Lemma SI_SchedulingInfo_v1700__F1F2_cond (z : SI_SchedulingInfo_v1700__Type)
  : SI_SchedulingInfo_v1700__cond z ->
  (seq_cond SI_SchedulingInfo_v1700__list (SI_SchedulingInfo_v1700__F1 z)).
intro H. unfold SI_SchedulingInfo_v1700__cond in H. simpl. auto. Qed.
Lemma SI_SchedulingInfo_v1700__F1F2_cond2 (z : SI_SchedulingInfo_v1700__Type)
 : SI_SchedulingInfo_v1700__F2 (SI_SchedulingInfo_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SI_SchedulingInfo_v1700__F2F1_cond (y : seq_type SI_SchedulingInfo_v1700__list)
  : seq_cond SI_SchedulingInfo_v1700__list y ->
 (SI_SchedulingInfo_v1700__cond (SI_SchedulingInfo_v1700__F2 y)) /\  SI_SchedulingInfo_v1700__F1 (SI_SchedulingInfo_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SI_SchedulingInfo_v1700__cond. simpl in *. auto.
 - simpl. unfold SI_SchedulingInfo_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SI_SchedulingInfo_v1700__Format : T_Format SI_SchedulingInfo_v1700__Type SI_SchedulingInfo_v1700__cond :=
        proj2_format  SI_SchedulingInfo_v1700__cond SI_SchedulingInfo_v1700__list__Format
    SI_SchedulingInfo_v1700__F1 SI_SchedulingInfo_v1700__F2 SI_SchedulingInfo_v1700__F1F2_cond  SI_SchedulingInfo_v1700__F1F2_cond2 SI_SchedulingInfo_v1700__F2F1_cond.
Opaque SI_SchedulingInfo_v1700__cond SI_SchedulingInfo_v1700__Format.

