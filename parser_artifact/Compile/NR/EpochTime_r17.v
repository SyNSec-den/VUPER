Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma EpochTime_r17__sfn_r17__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma EpochTime_r17__sfn_r17__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply EpochTime_r17__sfn_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EpochTime_r17__sfn_r17__Type := Z.
Definition EpochTime_r17__sfn_r17__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma EpochTime_r17__subFrameNR_r17__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma EpochTime_r17__subFrameNR_r17__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply EpochTime_r17__subFrameNR_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EpochTime_r17__subFrameNR_r17__Type := Z.
Definition EpochTime_r17__subFrameNR_r17__cond := (fun z => (0 <= z <= 9)%Z).
Record EpochTime_r17__Type : Set :=
  make__EpochTime_r17__Type {
    EpochTime_r17__sfn_r17 : Z ;
    EpochTime_r17__subFrameNR_r17 : Z ;
}.
Definition EpochTime_r17__list := (
 Nor Z EpochTime_r17__sfn_r17__cond ::
 Nor Z EpochTime_r17__subFrameNR_r17__cond ::
 nil).
Definition EpochTime_r17__cond z := 
  EpochTime_r17__sfn_r17__cond (EpochTime_r17__sfn_r17 z) /\
  EpochTime_r17__subFrameNR_r17__cond (EpochTime_r17__subFrameNR_r17 z) /\
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
Definition EpochTime_r17__sfn_r17__Format : T_Format Z EpochTime_r17__sfn_r17__cond :=
 ranged_int_format (0) (1023) EpochTime_r17__sfn_r17__helper1 EpochTime_r17__sfn_r17__helper2.

Opaque EpochTime_r17__sfn_r17__cond EpochTime_r17__sfn_r17__Format.

Definition EpochTime_r17__subFrameNR_r17__Format : T_Format Z EpochTime_r17__subFrameNR_r17__cond :=
 ranged_int_format (0) (9) EpochTime_r17__subFrameNR_r17__helper1 EpochTime_r17__subFrameNR_r17__helper2.

Opaque EpochTime_r17__subFrameNR_r17__cond EpochTime_r17__subFrameNR_r17__Format.


Definition EpochTime_r17__Format_Type := Eval cbn in seq_format_prod EpochTime_r17__list.
Definition EpochTime_r17__Format_list : EpochTime_r17__Format_Type :=
  (EpochTime_r17__sfn_r17__Format, (EpochTime_r17__subFrameNR_r17__Format, unit_format)).
Definition EpochTime_r17__list__Format := (*Eval compute in *) seq_format EpochTime_r17__list EpochTime_r17__Format_list.
Definition EpochTime_r17__F1 z :=
  (EpochTime_r17__sfn_r17 z, (EpochTime_r17__subFrameNR_r17 z, tt)).
Definition EpochTime_r17__F2 (y : seq_type EpochTime_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__EpochTime_r17__Type i0 i1
  end.
Lemma EpochTime_r17__F1F2_cond (z : EpochTime_r17__Type)
  : EpochTime_r17__cond z ->
  (seq_cond EpochTime_r17__list (EpochTime_r17__F1 z)).
intro H. unfold EpochTime_r17__cond in H. simpl. auto. Qed.
Lemma EpochTime_r17__F1F2_cond2 (z : EpochTime_r17__Type)
 : EpochTime_r17__F2 (EpochTime_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EpochTime_r17__F2F1_cond (y : seq_type EpochTime_r17__list)
  : seq_cond EpochTime_r17__list y ->
 (EpochTime_r17__cond (EpochTime_r17__F2 y)) /\  EpochTime_r17__F1 (EpochTime_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EpochTime_r17__cond. simpl in *. auto.
 - simpl. unfold EpochTime_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EpochTime_r17__Format : T_Format EpochTime_r17__Type EpochTime_r17__cond :=
        proj2_format  EpochTime_r17__cond EpochTime_r17__list__Format
    EpochTime_r17__F1 EpochTime_r17__F2 EpochTime_r17__F1F2_cond  EpochTime_r17__F1F2_cond2 EpochTime_r17__F2F1_cond.
Opaque EpochTime_r17__cond EpochTime_r17__Format.

