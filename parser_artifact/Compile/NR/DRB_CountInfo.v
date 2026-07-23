Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.

Lemma DRB_CountInfo__count_Uplink__helper1 : (0 <= 4294967295)%Z.  lia. Qed.
Lemma DRB_CountInfo__count_Uplink__helper2 : to_bit_sz (Z.to_nat (4294967295 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4294967295 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRB_CountInfo__count_Uplink__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRB_CountInfo__count_Uplink__Type := Z.
Definition DRB_CountInfo__count_Uplink__cond := (fun z => (0 <= z <= 4294967295)%Z).
Lemma DRB_CountInfo__count_Downlink__helper1 : (0 <= 4294967295)%Z.  lia. Qed.
Lemma DRB_CountInfo__count_Downlink__helper2 : to_bit_sz (Z.to_nat (4294967295 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4294967295 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRB_CountInfo__count_Downlink__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRB_CountInfo__count_Downlink__Type := Z.
Definition DRB_CountInfo__count_Downlink__cond := (fun z => (0 <= z <= 4294967295)%Z).
Record DRB_CountInfo__Type : Set :=
  make__DRB_CountInfo__Type {
    DRB_CountInfo__drb_Identity : DRB_Identity__Type ;
    DRB_CountInfo__count_Uplink : Z ;
    DRB_CountInfo__count_Downlink : Z ;
}.
Definition DRB_CountInfo__list := (
 Nor DRB_Identity__Type DRB_Identity__cond ::
 Nor Z DRB_CountInfo__count_Uplink__cond ::
 Nor Z DRB_CountInfo__count_Downlink__cond ::
 nil).
Definition DRB_CountInfo__cond z := 
  DRB_Identity__cond (DRB_CountInfo__drb_Identity z) /\
  DRB_CountInfo__count_Uplink__cond (DRB_CountInfo__count_Uplink z) /\
  DRB_CountInfo__count_Downlink__cond (DRB_CountInfo__count_Downlink z) /\
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
Definition DRB_CountInfo__count_Uplink__Format : T_Format Z DRB_CountInfo__count_Uplink__cond :=
 ranged_int_format (0) (4294967295) DRB_CountInfo__count_Uplink__helper1 DRB_CountInfo__count_Uplink__helper2.

Opaque DRB_CountInfo__count_Uplink__cond DRB_CountInfo__count_Uplink__Format.

Definition DRB_CountInfo__count_Downlink__Format : T_Format Z DRB_CountInfo__count_Downlink__cond :=
 ranged_int_format (0) (4294967295) DRB_CountInfo__count_Downlink__helper1 DRB_CountInfo__count_Downlink__helper2.

Opaque DRB_CountInfo__count_Downlink__cond DRB_CountInfo__count_Downlink__Format.


Definition DRB_CountInfo__Format_Type := Eval cbn in seq_format_prod DRB_CountInfo__list.
Definition DRB_CountInfo__Format_list : DRB_CountInfo__Format_Type :=
  (DRB_Identity__Format, (DRB_CountInfo__count_Uplink__Format, (DRB_CountInfo__count_Downlink__Format, unit_format))).
Definition DRB_CountInfo__list__Format := (*Eval compute in *) seq_format DRB_CountInfo__list DRB_CountInfo__Format_list.
Definition DRB_CountInfo__F1 z :=
  (DRB_CountInfo__drb_Identity z, (DRB_CountInfo__count_Uplink z, (DRB_CountInfo__count_Downlink z, tt))).
Definition DRB_CountInfo__F2 (y : seq_type DRB_CountInfo__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__DRB_CountInfo__Type i0 i1 i2
  end.
Lemma DRB_CountInfo__F1F2_cond (z : DRB_CountInfo__Type)
  : DRB_CountInfo__cond z ->
  (seq_cond DRB_CountInfo__list (DRB_CountInfo__F1 z)).
intro H. unfold DRB_CountInfo__cond in H. simpl. auto. Qed.
Lemma DRB_CountInfo__F1F2_cond2 (z : DRB_CountInfo__Type)
 : DRB_CountInfo__F2 (DRB_CountInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRB_CountInfo__F2F1_cond (y : seq_type DRB_CountInfo__list)
  : seq_cond DRB_CountInfo__list y ->
 (DRB_CountInfo__cond (DRB_CountInfo__F2 y)) /\  DRB_CountInfo__F1 (DRB_CountInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRB_CountInfo__cond. simpl in *. auto.
 - simpl. unfold DRB_CountInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRB_CountInfo__Format : T_Format DRB_CountInfo__Type DRB_CountInfo__cond :=
        proj2_format  DRB_CountInfo__cond DRB_CountInfo__list__Format
    DRB_CountInfo__F1 DRB_CountInfo__F2 DRB_CountInfo__F1F2_cond  DRB_CountInfo__F1F2_cond2 DRB_CountInfo__F2F1_cond.
Opaque DRB_CountInfo__cond DRB_CountInfo__Format.

