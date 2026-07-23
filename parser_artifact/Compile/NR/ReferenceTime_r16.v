Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma ReferenceTime_r16__refDays_r16__helper1 : (0 <= 72999)%Z.  lia. Qed.
Lemma ReferenceTime_r16__refDays_r16__helper2 : to_bit_sz (Z.to_nat (72999 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (72999 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ReferenceTime_r16__refDays_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReferenceTime_r16__refDays_r16__Type := Z.
Definition ReferenceTime_r16__refDays_r16__cond := (fun z => (0 <= z <= 72999)%Z).
Lemma ReferenceTime_r16__refSeconds_r16__helper1 : (0 <= 86399)%Z.  lia. Qed.
Lemma ReferenceTime_r16__refSeconds_r16__helper2 : to_bit_sz (Z.to_nat (86399 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (86399 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ReferenceTime_r16__refSeconds_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReferenceTime_r16__refSeconds_r16__Type := Z.
Definition ReferenceTime_r16__refSeconds_r16__cond := (fun z => (0 <= z <= 86399)%Z).
Lemma ReferenceTime_r16__refMilliSeconds_r16__helper1 : (0 <= 999)%Z.  lia. Qed.
Lemma ReferenceTime_r16__refMilliSeconds_r16__helper2 : to_bit_sz (Z.to_nat (999 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (999 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ReferenceTime_r16__refMilliSeconds_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReferenceTime_r16__refMilliSeconds_r16__Type := Z.
Definition ReferenceTime_r16__refMilliSeconds_r16__cond := (fun z => (0 <= z <= 999)%Z).
Lemma ReferenceTime_r16__refTenNanoSeconds_r16__helper1 : (0 <= 99999)%Z.  lia. Qed.
Lemma ReferenceTime_r16__refTenNanoSeconds_r16__helper2 : to_bit_sz (Z.to_nat (99999 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (99999 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ReferenceTime_r16__refTenNanoSeconds_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReferenceTime_r16__refTenNanoSeconds_r16__Type := Z.
Definition ReferenceTime_r16__refTenNanoSeconds_r16__cond := (fun z => (0 <= z <= 99999)%Z).
Record ReferenceTime_r16__Type : Set :=
  make__ReferenceTime_r16__Type {
    ReferenceTime_r16__refDays_r16 : Z ;
    ReferenceTime_r16__refSeconds_r16 : Z ;
    ReferenceTime_r16__refMilliSeconds_r16 : Z ;
    ReferenceTime_r16__refTenNanoSeconds_r16 : Z ;
}.
Definition ReferenceTime_r16__list := (
 Nor Z ReferenceTime_r16__refDays_r16__cond ::
 Nor Z ReferenceTime_r16__refSeconds_r16__cond ::
 Nor Z ReferenceTime_r16__refMilliSeconds_r16__cond ::
 Nor Z ReferenceTime_r16__refTenNanoSeconds_r16__cond ::
 nil).
Definition ReferenceTime_r16__cond z := 
  ReferenceTime_r16__refDays_r16__cond (ReferenceTime_r16__refDays_r16 z) /\
  ReferenceTime_r16__refSeconds_r16__cond (ReferenceTime_r16__refSeconds_r16 z) /\
  ReferenceTime_r16__refMilliSeconds_r16__cond (ReferenceTime_r16__refMilliSeconds_r16 z) /\
  ReferenceTime_r16__refTenNanoSeconds_r16__cond (ReferenceTime_r16__refTenNanoSeconds_r16 z) /\
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
Definition ReferenceTime_r16__refDays_r16__Format : T_Format Z ReferenceTime_r16__refDays_r16__cond :=
 ranged_int_format (0) (72999) ReferenceTime_r16__refDays_r16__helper1 ReferenceTime_r16__refDays_r16__helper2.

Opaque ReferenceTime_r16__refDays_r16__cond ReferenceTime_r16__refDays_r16__Format.

Definition ReferenceTime_r16__refSeconds_r16__Format : T_Format Z ReferenceTime_r16__refSeconds_r16__cond :=
 ranged_int_format (0) (86399) ReferenceTime_r16__refSeconds_r16__helper1 ReferenceTime_r16__refSeconds_r16__helper2.

Opaque ReferenceTime_r16__refSeconds_r16__cond ReferenceTime_r16__refSeconds_r16__Format.

Definition ReferenceTime_r16__refMilliSeconds_r16__Format : T_Format Z ReferenceTime_r16__refMilliSeconds_r16__cond :=
 ranged_int_format (0) (999) ReferenceTime_r16__refMilliSeconds_r16__helper1 ReferenceTime_r16__refMilliSeconds_r16__helper2.

Opaque ReferenceTime_r16__refMilliSeconds_r16__cond ReferenceTime_r16__refMilliSeconds_r16__Format.

Definition ReferenceTime_r16__refTenNanoSeconds_r16__Format : T_Format Z ReferenceTime_r16__refTenNanoSeconds_r16__cond :=
 ranged_int_format (0) (99999) ReferenceTime_r16__refTenNanoSeconds_r16__helper1 ReferenceTime_r16__refTenNanoSeconds_r16__helper2.

Opaque ReferenceTime_r16__refTenNanoSeconds_r16__cond ReferenceTime_r16__refTenNanoSeconds_r16__Format.


Definition ReferenceTime_r16__Format_Type := Eval cbn in seq_format_prod ReferenceTime_r16__list.
Definition ReferenceTime_r16__Format_list : ReferenceTime_r16__Format_Type :=
  (ReferenceTime_r16__refDays_r16__Format, (ReferenceTime_r16__refSeconds_r16__Format, (ReferenceTime_r16__refMilliSeconds_r16__Format, (ReferenceTime_r16__refTenNanoSeconds_r16__Format, unit_format)))).
Definition ReferenceTime_r16__list__Format := (*Eval compute in *) seq_format ReferenceTime_r16__list ReferenceTime_r16__Format_list.
Definition ReferenceTime_r16__F1 z :=
  (ReferenceTime_r16__refDays_r16 z, (ReferenceTime_r16__refSeconds_r16 z, (ReferenceTime_r16__refMilliSeconds_r16 z, (ReferenceTime_r16__refTenNanoSeconds_r16 z, tt)))).
Definition ReferenceTime_r16__F2 (y : seq_type ReferenceTime_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ReferenceTime_r16__Type i0 i1 i2 i3
  end.
Lemma ReferenceTime_r16__F1F2_cond (z : ReferenceTime_r16__Type)
  : ReferenceTime_r16__cond z ->
  (seq_cond ReferenceTime_r16__list (ReferenceTime_r16__F1 z)).
intro H. unfold ReferenceTime_r16__cond in H. simpl. auto. Qed.
Lemma ReferenceTime_r16__F1F2_cond2 (z : ReferenceTime_r16__Type)
 : ReferenceTime_r16__F2 (ReferenceTime_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReferenceTime_r16__F2F1_cond (y : seq_type ReferenceTime_r16__list)
  : seq_cond ReferenceTime_r16__list y ->
 (ReferenceTime_r16__cond (ReferenceTime_r16__F2 y)) /\  ReferenceTime_r16__F1 (ReferenceTime_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReferenceTime_r16__cond. simpl in *. auto.
 - simpl. unfold ReferenceTime_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReferenceTime_r16__Format : T_Format ReferenceTime_r16__Type ReferenceTime_r16__cond :=
        proj2_format  ReferenceTime_r16__cond ReferenceTime_r16__list__Format
    ReferenceTime_r16__F1 ReferenceTime_r16__F2 ReferenceTime_r16__F1F2_cond  ReferenceTime_r16__F1F2_cond2 ReferenceTime_r16__F2F1_cond.
Opaque ReferenceTime_r16__cond ReferenceTime_r16__Format.

