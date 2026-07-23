Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DummyH__burstLength__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma DummyH__burstLength__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyH__burstLength__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyH__burstLength__Type := Z.
Definition DummyH__burstLength__cond := (fun z => (1 <= z <= 2)%Z).
Lemma DummyH__maxSimultaneousResourceSetsPerCC__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma DummyH__maxSimultaneousResourceSetsPerCC__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyH__maxSimultaneousResourceSetsPerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyH__maxSimultaneousResourceSetsPerCC__Type := Z.
Definition DummyH__maxSimultaneousResourceSetsPerCC__cond := (fun z => (1 <= z <= 8)%Z).
Lemma DummyH__maxConfiguredResourceSetsPerCC__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma DummyH__maxConfiguredResourceSetsPerCC__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyH__maxConfiguredResourceSetsPerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyH__maxConfiguredResourceSetsPerCC__Type := Z.
Definition DummyH__maxConfiguredResourceSetsPerCC__cond := (fun z => (1 <= z <= 64)%Z).
Lemma DummyH__maxConfiguredResourceSetsAllCC__helper1 : (1 <= 128)%Z.  lia. Qed.
Lemma DummyH__maxConfiguredResourceSetsAllCC__helper2 : to_bit_sz (Z.to_nat (128 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyH__maxConfiguredResourceSetsAllCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyH__maxConfiguredResourceSetsAllCC__Type := Z.
Definition DummyH__maxConfiguredResourceSetsAllCC__cond := (fun z => (1 <= z <= 128)%Z).
Record DummyH__Type : Set :=
  make__DummyH__Type {
    DummyH__burstLength : Z ;
    DummyH__maxSimultaneousResourceSetsPerCC : Z ;
    DummyH__maxConfiguredResourceSetsPerCC : Z ;
    DummyH__maxConfiguredResourceSetsAllCC : Z ;
}.
Definition DummyH__list := (
 Nor Z DummyH__burstLength__cond ::
 Nor Z DummyH__maxSimultaneousResourceSetsPerCC__cond ::
 Nor Z DummyH__maxConfiguredResourceSetsPerCC__cond ::
 Nor Z DummyH__maxConfiguredResourceSetsAllCC__cond ::
 nil).
Definition DummyH__cond z := 
  DummyH__burstLength__cond (DummyH__burstLength z) /\
  DummyH__maxSimultaneousResourceSetsPerCC__cond (DummyH__maxSimultaneousResourceSetsPerCC z) /\
  DummyH__maxConfiguredResourceSetsPerCC__cond (DummyH__maxConfiguredResourceSetsPerCC z) /\
  DummyH__maxConfiguredResourceSetsAllCC__cond (DummyH__maxConfiguredResourceSetsAllCC z) /\
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
Definition DummyH__burstLength__Format : T_Format Z DummyH__burstLength__cond :=
 ranged_int_format (1) (2) DummyH__burstLength__helper1 DummyH__burstLength__helper2.

Opaque DummyH__burstLength__cond DummyH__burstLength__Format.

Definition DummyH__maxSimultaneousResourceSetsPerCC__Format : T_Format Z DummyH__maxSimultaneousResourceSetsPerCC__cond :=
 ranged_int_format (1) (8) DummyH__maxSimultaneousResourceSetsPerCC__helper1 DummyH__maxSimultaneousResourceSetsPerCC__helper2.

Opaque DummyH__maxSimultaneousResourceSetsPerCC__cond DummyH__maxSimultaneousResourceSetsPerCC__Format.

Definition DummyH__maxConfiguredResourceSetsPerCC__Format : T_Format Z DummyH__maxConfiguredResourceSetsPerCC__cond :=
 ranged_int_format (1) (64) DummyH__maxConfiguredResourceSetsPerCC__helper1 DummyH__maxConfiguredResourceSetsPerCC__helper2.

Opaque DummyH__maxConfiguredResourceSetsPerCC__cond DummyH__maxConfiguredResourceSetsPerCC__Format.

Definition DummyH__maxConfiguredResourceSetsAllCC__Format : T_Format Z DummyH__maxConfiguredResourceSetsAllCC__cond :=
 ranged_int_format (1) (128) DummyH__maxConfiguredResourceSetsAllCC__helper1 DummyH__maxConfiguredResourceSetsAllCC__helper2.

Opaque DummyH__maxConfiguredResourceSetsAllCC__cond DummyH__maxConfiguredResourceSetsAllCC__Format.


Definition DummyH__Format_Type := Eval cbn in seq_format_prod DummyH__list.
Definition DummyH__Format_list : DummyH__Format_Type :=
  (DummyH__burstLength__Format, (DummyH__maxSimultaneousResourceSetsPerCC__Format, (DummyH__maxConfiguredResourceSetsPerCC__Format, (DummyH__maxConfiguredResourceSetsAllCC__Format, unit_format)))).
Definition DummyH__list__Format := (*Eval compute in *) seq_format DummyH__list DummyH__Format_list.
Definition DummyH__F1 z :=
  (DummyH__burstLength z, (DummyH__maxSimultaneousResourceSetsPerCC z, (DummyH__maxConfiguredResourceSetsPerCC z, (DummyH__maxConfiguredResourceSetsAllCC z, tt)))).
Definition DummyH__F2 (y : seq_type DummyH__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__DummyH__Type i0 i1 i2 i3
  end.
Lemma DummyH__F1F2_cond (z : DummyH__Type)
  : DummyH__cond z ->
  (seq_cond DummyH__list (DummyH__F1 z)).
intro H. unfold DummyH__cond in H. simpl. auto. Qed.
Lemma DummyH__F1F2_cond2 (z : DummyH__Type)
 : DummyH__F2 (DummyH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyH__F2F1_cond (y : seq_type DummyH__list)
  : seq_cond DummyH__list y ->
 (DummyH__cond (DummyH__F2 y)) /\  DummyH__F1 (DummyH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyH__cond. simpl in *. auto.
 - simpl. unfold DummyH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyH__Format : T_Format DummyH__Type DummyH__cond :=
        proj2_format  DummyH__cond DummyH__list__Format
    DummyH__F1 DummyH__F2 DummyH__F1F2_cond  DummyH__F1F2_cond2 DummyH__F2F1_cond.
Opaque DummyH__cond DummyH__Format.

