Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma OffsetValue_r17__offsetValue_r17__helper1 : (-20000 <= 20000)%Z.  lia. Qed.
Lemma OffsetValue_r17__offsetValue_r17__helper2 : to_bit_sz (Z.to_nat (20000 - -20000)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20000 - -20000))%Z). { apply Zorder.Zle_minus_le_0. apply OffsetValue_r17__offsetValue_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition OffsetValue_r17__offsetValue_r17__Type := Z.
Definition OffsetValue_r17__offsetValue_r17__cond := (fun z => (-20000 <= z <= 20000)%Z).
Record OffsetValue_r17__Type : Set :=
  make__OffsetValue_r17__Type {
    OffsetValue_r17__offsetValue_r17 : Z ;
    OffsetValue_r17__shift7dot5kHz_r17 : bool ;
}.
Definition OffsetValue_r17__list := (
 Nor Z OffsetValue_r17__offsetValue_r17__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition OffsetValue_r17__cond z := 
  OffsetValue_r17__offsetValue_r17__cond (OffsetValue_r17__offsetValue_r17 z) /\
  (fun _ => True) (OffsetValue_r17__shift7dot5kHz_r17 z) /\
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
Definition OffsetValue_r17__offsetValue_r17__Format : T_Format Z OffsetValue_r17__offsetValue_r17__cond :=
 ranged_int_format (-20000) (20000) OffsetValue_r17__offsetValue_r17__helper1 OffsetValue_r17__offsetValue_r17__helper2.

Opaque OffsetValue_r17__offsetValue_r17__cond OffsetValue_r17__offsetValue_r17__Format.


Definition OffsetValue_r17__Format_Type := Eval cbn in seq_format_prod OffsetValue_r17__list.
Definition OffsetValue_r17__Format_list : OffsetValue_r17__Format_Type :=
  (OffsetValue_r17__offsetValue_r17__Format, (bool__Format, unit_format)).
Definition OffsetValue_r17__list__Format := (*Eval compute in *) seq_format OffsetValue_r17__list OffsetValue_r17__Format_list.
Definition OffsetValue_r17__F1 z :=
  (OffsetValue_r17__offsetValue_r17 z, (OffsetValue_r17__shift7dot5kHz_r17 z, tt)).
Definition OffsetValue_r17__F2 (y : seq_type OffsetValue_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__OffsetValue_r17__Type i0 i1
  end.
Lemma OffsetValue_r17__F1F2_cond (z : OffsetValue_r17__Type)
  : OffsetValue_r17__cond z ->
  (seq_cond OffsetValue_r17__list (OffsetValue_r17__F1 z)).
intro H. unfold OffsetValue_r17__cond in H. simpl. auto. Qed.
Lemma OffsetValue_r17__F1F2_cond2 (z : OffsetValue_r17__Type)
 : OffsetValue_r17__F2 (OffsetValue_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OffsetValue_r17__F2F1_cond (y : seq_type OffsetValue_r17__list)
  : seq_cond OffsetValue_r17__list y ->
 (OffsetValue_r17__cond (OffsetValue_r17__F2 y)) /\  OffsetValue_r17__F1 (OffsetValue_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OffsetValue_r17__cond. simpl in *. auto.
 - simpl. unfold OffsetValue_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OffsetValue_r17__Format : T_Format OffsetValue_r17__Type OffsetValue_r17__cond :=
        proj2_format  OffsetValue_r17__cond OffsetValue_r17__list__Format
    OffsetValue_r17__F1 OffsetValue_r17__F2 OffsetValue_r17__F1F2_cond  OffsetValue_r17__F1F2_cond2 OffsetValue_r17__F2F1_cond.
Opaque OffsetValue_r17__cond OffsetValue_r17__Format.

