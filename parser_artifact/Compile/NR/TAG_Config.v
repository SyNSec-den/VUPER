Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TAG_Id.

Opaque TAG_Id__cond TAG_Id__Format.

Definition TAG_Config__tag_ToReleaseList__Type := list TAG_Id__Type.

Lemma TAG_Config__tag_ToReleaseList__helper1 : (0 <= 1 <= maxNrofTAGs)%Z. unfold maxNrofTAGs.
 lia. Qed.
Lemma TAG_Config__tag_ToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofTAGs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTAGs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TAG_Config__tag_ToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TAG_Config__tag_ToReleaseList__cond (z : TAG_Config__tag_ToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTAGs)%Z /\ (list_and TAG_Id__cond z) .

Require Import NR.TAG.

Opaque TAG__cond TAG__Format.

Definition TAG_Config__tag_ToAddModList__Type := list TAG__Type.

Lemma TAG_Config__tag_ToAddModList__helper1 : (0 <= 1 <= maxNrofTAGs)%Z. unfold maxNrofTAGs.
 lia. Qed.
Lemma TAG_Config__tag_ToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofTAGs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTAGs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TAG_Config__tag_ToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TAG_Config__tag_ToAddModList__cond (z : TAG_Config__tag_ToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTAGs)%Z /\ (list_and TAG__cond z) .

Record TAG_Config__Type : Set :=
  make__TAG_Config__Type {
    TAG_Config__tag_ToReleaseList : option TAG_Config__tag_ToReleaseList__Type ;
    TAG_Config__tag_ToAddModList : option TAG_Config__tag_ToAddModList__Type ;
}.
Definition TAG_Config__list := (
 Opt TAG_Config__tag_ToReleaseList__Type TAG_Config__tag_ToReleaseList__cond ::
 Opt TAG_Config__tag_ToAddModList__Type TAG_Config__tag_ToAddModList__cond ::
 nil).
Definition TAG_Config__cond z := 
  opt_cond TAG_Config__tag_ToReleaseList__cond (TAG_Config__tag_ToReleaseList z) /\
  opt_cond TAG_Config__tag_ToAddModList__cond (TAG_Config__tag_ToAddModList z) /\
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
Definition TAG_Config__tag_ToReleaseList__Format : T_Format TAG_Config__tag_ToReleaseList__Type TAG_Config__tag_ToReleaseList__cond := seq_of_format TAG_Id__Format 1 maxNrofTAGs TAG_Config__tag_ToReleaseList__helper1 TAG_Config__tag_ToReleaseList__helper2.

Opaque TAG_Config__tag_ToReleaseList__cond TAG_Config__tag_ToReleaseList__Format.

Definition TAG_Config__tag_ToAddModList__Format : T_Format TAG_Config__tag_ToAddModList__Type TAG_Config__tag_ToAddModList__cond := seq_of_format TAG__Format 1 maxNrofTAGs TAG_Config__tag_ToAddModList__helper1 TAG_Config__tag_ToAddModList__helper2.

Opaque TAG_Config__tag_ToAddModList__cond TAG_Config__tag_ToAddModList__Format.


Definition TAG_Config__Format_Type := Eval cbn in seq_format_prod TAG_Config__list.
Definition TAG_Config__Format_list : TAG_Config__Format_Type :=
  (TAG_Config__tag_ToReleaseList__Format, (TAG_Config__tag_ToAddModList__Format, unit_format)).
Definition TAG_Config__list__Format := (*Eval compute in *) seq_format TAG_Config__list TAG_Config__Format_list.
Definition TAG_Config__F1 z :=
  (TAG_Config__tag_ToReleaseList z, (TAG_Config__tag_ToAddModList z, tt)).
Definition TAG_Config__F2 (y : seq_type TAG_Config__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TAG_Config__Type i0 i1
  end.
Lemma TAG_Config__F1F2_cond (z : TAG_Config__Type)
  : TAG_Config__cond z ->
  (seq_cond TAG_Config__list (TAG_Config__F1 z)).
intro H. unfold TAG_Config__cond in H. simpl. auto. Qed.
Lemma TAG_Config__F1F2_cond2 (z : TAG_Config__Type)
 : TAG_Config__F2 (TAG_Config__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TAG_Config__F2F1_cond (y : seq_type TAG_Config__list)
  : seq_cond TAG_Config__list y ->
 (TAG_Config__cond (TAG_Config__F2 y)) /\  TAG_Config__F1 (TAG_Config__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TAG_Config__cond. simpl in *. auto.
 - simpl. unfold TAG_Config__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TAG_Config__Format : T_Format TAG_Config__Type TAG_Config__cond :=
        proj2_format  TAG_Config__cond TAG_Config__list__Format
    TAG_Config__F1 TAG_Config__F2 TAG_Config__F1F2_cond  TAG_Config__F1F2_cond2 TAG_Config__F2F1_cond.
Opaque TAG_Config__cond TAG_Config__Format.

