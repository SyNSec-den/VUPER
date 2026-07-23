Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__helper1 : (0 <= 448)%Z.  lia. Qed.
Lemma DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__helper2 : to_bit_sz (Z.to_nat (448 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (448 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__Type := Z.
Definition DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__cond := (fun z => (0 <= z <= 448)%Z).
Lemma DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__helper1 : (0 <= 448)%Z.  lia. Qed.
Lemma DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__helper2 : to_bit_sz (Z.to_nat (448 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (448 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__Type := Z.
Definition DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__cond := (fun z => (0 <= z <= 448)%Z).
Record DRX_ConfigExt_v1700__Type : Set :=
  make__DRX_ConfigExt_v1700__Type {
    DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17 : Z ;
    DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17 : Z ;
}.
Definition DRX_ConfigExt_v1700__list := (
 Nor Z DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__cond ::
 Nor Z DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__cond ::
 nil).
Definition DRX_ConfigExt_v1700__cond z := 
  DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__cond (DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17 z) /\
  DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__cond (DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17 z) /\
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
Definition DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__Format : T_Format Z DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__cond :=
 ranged_int_format (0) (448) DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__helper1 DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__helper2.

Opaque DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__cond DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__Format.

Definition DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__Format : T_Format Z DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__cond :=
 ranged_int_format (0) (448) DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__helper1 DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__helper2.

Opaque DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__cond DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__Format.


Definition DRX_ConfigExt_v1700__Format_Type := Eval cbn in seq_format_prod DRX_ConfigExt_v1700__list.
Definition DRX_ConfigExt_v1700__Format_list : DRX_ConfigExt_v1700__Format_Type :=
  (DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17__Format, (DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17__Format, unit_format)).
Definition DRX_ConfigExt_v1700__list__Format := (*Eval compute in *) seq_format DRX_ConfigExt_v1700__list DRX_ConfigExt_v1700__Format_list.
Definition DRX_ConfigExt_v1700__F1 z :=
  (DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerDL_r17 z, (DRX_ConfigExt_v1700__drx_HARQ_RTT_TimerUL_r17 z, tt)).
Definition DRX_ConfigExt_v1700__F2 (y : seq_type DRX_ConfigExt_v1700__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DRX_ConfigExt_v1700__Type i0 i1
  end.
Lemma DRX_ConfigExt_v1700__F1F2_cond (z : DRX_ConfigExt_v1700__Type)
  : DRX_ConfigExt_v1700__cond z ->
  (seq_cond DRX_ConfigExt_v1700__list (DRX_ConfigExt_v1700__F1 z)).
intro H. unfold DRX_ConfigExt_v1700__cond in H. simpl. auto. Qed.
Lemma DRX_ConfigExt_v1700__F1F2_cond2 (z : DRX_ConfigExt_v1700__Type)
 : DRX_ConfigExt_v1700__F2 (DRX_ConfigExt_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_ConfigExt_v1700__F2F1_cond (y : seq_type DRX_ConfigExt_v1700__list)
  : seq_cond DRX_ConfigExt_v1700__list y ->
 (DRX_ConfigExt_v1700__cond (DRX_ConfigExt_v1700__F2 y)) /\  DRX_ConfigExt_v1700__F1 (DRX_ConfigExt_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_ConfigExt_v1700__cond. simpl in *. auto.
 - simpl. unfold DRX_ConfigExt_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_ConfigExt_v1700__Format : T_Format DRX_ConfigExt_v1700__Type DRX_ConfigExt_v1700__cond :=
        proj2_format  DRX_ConfigExt_v1700__cond DRX_ConfigExt_v1700__list__Format
    DRX_ConfigExt_v1700__F1 DRX_ConfigExt_v1700__F2 DRX_ConfigExt_v1700__F1F2_cond  DRX_ConfigExt_v1700__F1F2_cond2 DRX_ConfigExt_v1700__F2F1_cond.
Opaque DRX_ConfigExt_v1700__cond DRX_ConfigExt_v1700__Format.

