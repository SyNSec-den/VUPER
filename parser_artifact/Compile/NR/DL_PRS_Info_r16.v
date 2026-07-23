Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DL_PRS_Info_r16__dl_PRS_ID_r16__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma DL_PRS_Info_r16__dl_PRS_ID_r16__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PRS_Info_r16__dl_PRS_ID_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PRS_Info_r16__dl_PRS_ID_r16__Type := Z.
Definition DL_PRS_Info_r16__dl_PRS_ID_r16__cond := (fun z => (0 <= z <= 255)%Z).
Lemma DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__Type := Z.
Definition DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__cond := (fun z => (0 <= z <= 7)%Z).
Lemma DL_PRS_Info_r16__dl_PRS_ResourceId_r16__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DL_PRS_Info_r16__dl_PRS_ResourceId_r16__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PRS_Info_r16__dl_PRS_ResourceId_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PRS_Info_r16__dl_PRS_ResourceId_r16__Type := Z.
Definition DL_PRS_Info_r16__dl_PRS_ResourceId_r16__cond := (fun z => (0 <= z <= 63)%Z).
Record DL_PRS_Info_r16__Type : Set :=
  make__DL_PRS_Info_r16__Type {
    DL_PRS_Info_r16__dl_PRS_ID_r16 : Z ;
    DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16 : Z ;
    DL_PRS_Info_r16__dl_PRS_ResourceId_r16 : option Z ;
}.
Definition DL_PRS_Info_r16__list := (
 Nor Z DL_PRS_Info_r16__dl_PRS_ID_r16__cond ::
 Nor Z DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__cond ::
 Opt Z DL_PRS_Info_r16__dl_PRS_ResourceId_r16__cond ::
 nil).
Definition DL_PRS_Info_r16__cond z := 
  DL_PRS_Info_r16__dl_PRS_ID_r16__cond (DL_PRS_Info_r16__dl_PRS_ID_r16 z) /\
  DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__cond (DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16 z) /\
  opt_cond DL_PRS_Info_r16__dl_PRS_ResourceId_r16__cond (DL_PRS_Info_r16__dl_PRS_ResourceId_r16 z) /\
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
Definition DL_PRS_Info_r16__dl_PRS_ID_r16__Format : T_Format Z DL_PRS_Info_r16__dl_PRS_ID_r16__cond :=
 ranged_int_format (0) (255) DL_PRS_Info_r16__dl_PRS_ID_r16__helper1 DL_PRS_Info_r16__dl_PRS_ID_r16__helper2.

Opaque DL_PRS_Info_r16__dl_PRS_ID_r16__cond DL_PRS_Info_r16__dl_PRS_ID_r16__Format.

Definition DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__Format : T_Format Z DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__cond :=
 ranged_int_format (0) (7) DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__helper1 DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__helper2.

Opaque DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__cond DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__Format.

Definition DL_PRS_Info_r16__dl_PRS_ResourceId_r16__Format : T_Format Z DL_PRS_Info_r16__dl_PRS_ResourceId_r16__cond :=
 ranged_int_format (0) (63) DL_PRS_Info_r16__dl_PRS_ResourceId_r16__helper1 DL_PRS_Info_r16__dl_PRS_ResourceId_r16__helper2.

Opaque DL_PRS_Info_r16__dl_PRS_ResourceId_r16__cond DL_PRS_Info_r16__dl_PRS_ResourceId_r16__Format.


Definition DL_PRS_Info_r16__Format_Type := Eval cbn in seq_format_prod DL_PRS_Info_r16__list.
Definition DL_PRS_Info_r16__Format_list : DL_PRS_Info_r16__Format_Type :=
  (DL_PRS_Info_r16__dl_PRS_ID_r16__Format, (DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16__Format, (DL_PRS_Info_r16__dl_PRS_ResourceId_r16__Format, unit_format))).
Definition DL_PRS_Info_r16__list__Format := (*Eval compute in *) seq_format DL_PRS_Info_r16__list DL_PRS_Info_r16__Format_list.
Definition DL_PRS_Info_r16__F1 z :=
  (DL_PRS_Info_r16__dl_PRS_ID_r16 z, (DL_PRS_Info_r16__dl_PRS_ResourceSetId_r16 z, (DL_PRS_Info_r16__dl_PRS_ResourceId_r16 z, tt))).
Definition DL_PRS_Info_r16__F2 (y : seq_type DL_PRS_Info_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__DL_PRS_Info_r16__Type i0 i1 i2
  end.
Lemma DL_PRS_Info_r16__F1F2_cond (z : DL_PRS_Info_r16__Type)
  : DL_PRS_Info_r16__cond z ->
  (seq_cond DL_PRS_Info_r16__list (DL_PRS_Info_r16__F1 z)).
intro H. unfold DL_PRS_Info_r16__cond in H. simpl. auto. Qed.
Lemma DL_PRS_Info_r16__F1F2_cond2 (z : DL_PRS_Info_r16__Type)
 : DL_PRS_Info_r16__F2 (DL_PRS_Info_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DL_PRS_Info_r16__F2F1_cond (y : seq_type DL_PRS_Info_r16__list)
  : seq_cond DL_PRS_Info_r16__list y ->
 (DL_PRS_Info_r16__cond (DL_PRS_Info_r16__F2 y)) /\  DL_PRS_Info_r16__F1 (DL_PRS_Info_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DL_PRS_Info_r16__cond. simpl in *. auto.
 - simpl. unfold DL_PRS_Info_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DL_PRS_Info_r16__Format : T_Format DL_PRS_Info_r16__Type DL_PRS_Info_r16__cond :=
        proj2_format  DL_PRS_Info_r16__cond DL_PRS_Info_r16__list__Format
    DL_PRS_Info_r16__F1 DL_PRS_Info_r16__F2 DL_PRS_Info_r16__F1F2_cond  DL_PRS_Info_r16__F1F2_cond2 DL_PRS_Info_r16__F2F1_cond.
Opaque DL_PRS_Info_r16__cond DL_PRS_Info_r16__Format.

