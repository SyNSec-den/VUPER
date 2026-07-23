Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.IAB_IP_Address_r16.

Opaque IAB_IP_Address_r16__cond IAB_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type := list IAB_IP_Address_r16__Type.

Lemma IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__cond (z : IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and IAB_IP_Address_r16__cond z) .

Require Import NR.IAB_IP_Address_r16.

Opaque IAB_IP_Address_r16__cond IAB_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type := list IAB_IP_Address_r16__Type.

Lemma IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__cond (z : IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and IAB_IP_Address_r16__cond z) .

Require Import NR.IAB_IP_Address_r16.

Opaque IAB_IP_Address_r16__cond IAB_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type := list IAB_IP_Address_r16__Type.

Lemma IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__cond (z : IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and IAB_IP_Address_r16__cond z) .

Require Import NR.IAB_IP_Address_r16.

Opaque IAB_IP_Address_r16__cond IAB_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type := list IAB_IP_Address_r16__Type.

Lemma IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__cond (z : IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and IAB_IP_Address_r16__cond z) .

Record IAB_IP_AddressAndTraffic_r16__Type : Set :=
  make__IAB_IP_AddressAndTraffic_r16__Type {
    IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16 : option IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type ;
    IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16 : option IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type ;
    IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16 : option IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type ;
    IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16 : option IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type ;
}.
Definition IAB_IP_AddressAndTraffic_r16__list := (
 Opt IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__cond ::
 Opt IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__cond ::
 Opt IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__cond ::
 Opt IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__cond ::
 nil).
Definition IAB_IP_AddressAndTraffic_r16__cond z := 
  opt_cond IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__cond (IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16 z) /\
  opt_cond IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__cond (IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16 z) /\
  opt_cond IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__cond (IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16 z) /\
  opt_cond IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__cond (IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16 z) /\
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
Definition IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Format : T_Format IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__cond := seq_of_format IAB_IP_Address_r16__Format 1 8 IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__helper1 IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__helper2.

Opaque IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__cond IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Format : T_Format IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__cond := seq_of_format IAB_IP_Address_r16__Format 1 8 IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__helper1 IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__helper2.

Opaque IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__cond IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Format : T_Format IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__cond := seq_of_format IAB_IP_Address_r16__Format 1 8 IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__helper1 IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__helper2.

Opaque IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__cond IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Format.

Definition IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Format : T_Format IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__cond := seq_of_format IAB_IP_Address_r16__Format 1 8 IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__helper1 IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__helper2.

Opaque IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__cond IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Format.


Definition IAB_IP_AddressAndTraffic_r16__Format_Type := Eval cbn in seq_format_prod IAB_IP_AddressAndTraffic_r16__list.
Definition IAB_IP_AddressAndTraffic_r16__Format_list : IAB_IP_AddressAndTraffic_r16__Format_Type :=
  (IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Format, (IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Format, (IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Format, (IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Format, unit_format)))).
Definition IAB_IP_AddressAndTraffic_r16__list__Format := (*Eval compute in *) seq_format IAB_IP_AddressAndTraffic_r16__list IAB_IP_AddressAndTraffic_r16__Format_list.
Definition IAB_IP_AddressAndTraffic_r16__F1 z :=
  (IAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16 z, (IAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16 z, (IAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16 z, (IAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16 z, tt)))).
Definition IAB_IP_AddressAndTraffic_r16__F2 (y : seq_type IAB_IP_AddressAndTraffic_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__IAB_IP_AddressAndTraffic_r16__Type i0 i1 i2 i3
  end.
Lemma IAB_IP_AddressAndTraffic_r16__F1F2_cond (z : IAB_IP_AddressAndTraffic_r16__Type)
  : IAB_IP_AddressAndTraffic_r16__cond z ->
  (seq_cond IAB_IP_AddressAndTraffic_r16__list (IAB_IP_AddressAndTraffic_r16__F1 z)).
intro H. unfold IAB_IP_AddressAndTraffic_r16__cond in H. simpl. auto. Qed.
Lemma IAB_IP_AddressAndTraffic_r16__F1F2_cond2 (z : IAB_IP_AddressAndTraffic_r16__Type)
 : IAB_IP_AddressAndTraffic_r16__F2 (IAB_IP_AddressAndTraffic_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IAB_IP_AddressAndTraffic_r16__F2F1_cond (y : seq_type IAB_IP_AddressAndTraffic_r16__list)
  : seq_cond IAB_IP_AddressAndTraffic_r16__list y ->
 (IAB_IP_AddressAndTraffic_r16__cond (IAB_IP_AddressAndTraffic_r16__F2 y)) /\  IAB_IP_AddressAndTraffic_r16__F1 (IAB_IP_AddressAndTraffic_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IAB_IP_AddressAndTraffic_r16__cond. simpl in *. auto.
 - simpl. unfold IAB_IP_AddressAndTraffic_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IAB_IP_AddressAndTraffic_r16__Format : T_Format IAB_IP_AddressAndTraffic_r16__Type IAB_IP_AddressAndTraffic_r16__cond :=
        proj2_format  IAB_IP_AddressAndTraffic_r16__cond IAB_IP_AddressAndTraffic_r16__list__Format
    IAB_IP_AddressAndTraffic_r16__F1 IAB_IP_AddressAndTraffic_r16__F2 IAB_IP_AddressAndTraffic_r16__F1F2_cond  IAB_IP_AddressAndTraffic_r16__F1F2_cond2 IAB_IP_AddressAndTraffic_r16__F2F1_cond.
Opaque IAB_IP_AddressAndTraffic_r16__cond IAB_IP_AddressAndTraffic_r16__Format.

