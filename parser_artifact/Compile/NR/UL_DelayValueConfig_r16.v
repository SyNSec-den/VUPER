Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.

Definition UL_DelayValueConfig_r16__delay_DRBlist_r16__Type := list DRB_Identity__Type.

Lemma UL_DelayValueConfig_r16__delay_DRBlist_r16__helper1 : (0 <= 1 <= maxDRB)%Z. unfold maxDRB.
 lia. Qed.
Lemma UL_DelayValueConfig_r16__delay_DRBlist_r16__helper2 : to_bit_sz (Z.to_nat (maxDRB - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDRB - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UL_DelayValueConfig_r16__delay_DRBlist_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UL_DelayValueConfig_r16__delay_DRBlist_r16__cond (z : UL_DelayValueConfig_r16__delay_DRBlist_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxDRB)%Z /\ (list_and DRB_Identity__cond z) .

Record UL_DelayValueConfig_r16__Type : Set :=
  make__UL_DelayValueConfig_r16__Type {
    UL_DelayValueConfig_r16__delay_DRBlist_r16 : UL_DelayValueConfig_r16__delay_DRBlist_r16__Type ;
}.
Definition UL_DelayValueConfig_r16__list := (
 Nor UL_DelayValueConfig_r16__delay_DRBlist_r16__Type UL_DelayValueConfig_r16__delay_DRBlist_r16__cond ::
 nil).
Definition UL_DelayValueConfig_r16__cond z := 
  UL_DelayValueConfig_r16__delay_DRBlist_r16__cond (UL_DelayValueConfig_r16__delay_DRBlist_r16 z) /\
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
Definition UL_DelayValueConfig_r16__delay_DRBlist_r16__Format : T_Format UL_DelayValueConfig_r16__delay_DRBlist_r16__Type UL_DelayValueConfig_r16__delay_DRBlist_r16__cond := seq_of_format DRB_Identity__Format 1 maxDRB UL_DelayValueConfig_r16__delay_DRBlist_r16__helper1 UL_DelayValueConfig_r16__delay_DRBlist_r16__helper2.

Opaque UL_DelayValueConfig_r16__delay_DRBlist_r16__cond UL_DelayValueConfig_r16__delay_DRBlist_r16__Format.


Definition UL_DelayValueConfig_r16__Format_Type := Eval cbn in seq_format_prod UL_DelayValueConfig_r16__list.
Definition UL_DelayValueConfig_r16__Format_list : UL_DelayValueConfig_r16__Format_Type :=
  (UL_DelayValueConfig_r16__delay_DRBlist_r16__Format, unit_format).
Definition UL_DelayValueConfig_r16__list__Format := (*Eval compute in *) seq_format UL_DelayValueConfig_r16__list UL_DelayValueConfig_r16__Format_list.
Definition UL_DelayValueConfig_r16__F1 z :=
  (UL_DelayValueConfig_r16__delay_DRBlist_r16 z, tt).
Definition UL_DelayValueConfig_r16__F2 (y : seq_type UL_DelayValueConfig_r16__list) :=
  match y with
  | (i0, _)=>
    make__UL_DelayValueConfig_r16__Type i0
  end.
Lemma UL_DelayValueConfig_r16__F1F2_cond (z : UL_DelayValueConfig_r16__Type)
  : UL_DelayValueConfig_r16__cond z ->
  (seq_cond UL_DelayValueConfig_r16__list (UL_DelayValueConfig_r16__F1 z)).
intro H. unfold UL_DelayValueConfig_r16__cond in H. simpl. auto. Qed.
Lemma UL_DelayValueConfig_r16__F1F2_cond2 (z : UL_DelayValueConfig_r16__Type)
 : UL_DelayValueConfig_r16__F2 (UL_DelayValueConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UL_DelayValueConfig_r16__F2F1_cond (y : seq_type UL_DelayValueConfig_r16__list)
  : seq_cond UL_DelayValueConfig_r16__list y ->
 (UL_DelayValueConfig_r16__cond (UL_DelayValueConfig_r16__F2 y)) /\  UL_DelayValueConfig_r16__F1 (UL_DelayValueConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UL_DelayValueConfig_r16__cond. simpl in *. auto.
 - simpl. unfold UL_DelayValueConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UL_DelayValueConfig_r16__Format : T_Format UL_DelayValueConfig_r16__Type UL_DelayValueConfig_r16__cond :=
        proj2_format  UL_DelayValueConfig_r16__cond UL_DelayValueConfig_r16__list__Format
    UL_DelayValueConfig_r16__F1 UL_DelayValueConfig_r16__F2 UL_DelayValueConfig_r16__F1F2_cond  UL_DelayValueConfig_r16__F1F2_cond2 UL_DelayValueConfig_r16__F2F1_cond.
Opaque UL_DelayValueConfig_r16__cond UL_DelayValueConfig_r16__Format.

