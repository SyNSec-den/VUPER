Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__helper1 : (1 <= 96)%Z.  lia. Qed.
Lemma PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__helper2 : to_bit_sz (Z.to_nat (96 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (96 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__Type := Z.
Definition PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__cond := (fun z => (1 <= z <= 96)%Z).
Record PerRACSI_RSInfo_v1660__Type : Set :=
  make__PerRACSI_RSInfo_v1660__Type {
    PerRACSI_RSInfo_v1660__csi_RS_Index_v1660 : option Z ;
}.
Definition PerRACSI_RSInfo_v1660__list := (
 Opt Z PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__cond ::
 nil).
Definition PerRACSI_RSInfo_v1660__cond z := 
  opt_cond PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__cond (PerRACSI_RSInfo_v1660__csi_RS_Index_v1660 z) /\
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
Definition PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__Format : T_Format Z PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__cond :=
 ranged_int_format (1) (96) PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__helper1 PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__helper2.

Opaque PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__cond PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__Format.


Definition PerRACSI_RSInfo_v1660__Format_Type := Eval cbn in seq_format_prod PerRACSI_RSInfo_v1660__list.
Definition PerRACSI_RSInfo_v1660__Format_list : PerRACSI_RSInfo_v1660__Format_Type :=
  (PerRACSI_RSInfo_v1660__csi_RS_Index_v1660__Format, unit_format).
Definition PerRACSI_RSInfo_v1660__list__Format := (*Eval compute in *) seq_format PerRACSI_RSInfo_v1660__list PerRACSI_RSInfo_v1660__Format_list.
Definition PerRACSI_RSInfo_v1660__F1 z :=
  (PerRACSI_RSInfo_v1660__csi_RS_Index_v1660 z, tt).
Definition PerRACSI_RSInfo_v1660__F2 (y : seq_type PerRACSI_RSInfo_v1660__list) :=
  match y with
  | (i0, _)=>
    make__PerRACSI_RSInfo_v1660__Type i0
  end.
Lemma PerRACSI_RSInfo_v1660__F1F2_cond (z : PerRACSI_RSInfo_v1660__Type)
  : PerRACSI_RSInfo_v1660__cond z ->
  (seq_cond PerRACSI_RSInfo_v1660__list (PerRACSI_RSInfo_v1660__F1 z)).
intro H. unfold PerRACSI_RSInfo_v1660__cond in H. simpl. auto. Qed.
Lemma PerRACSI_RSInfo_v1660__F1F2_cond2 (z : PerRACSI_RSInfo_v1660__Type)
 : PerRACSI_RSInfo_v1660__F2 (PerRACSI_RSInfo_v1660__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PerRACSI_RSInfo_v1660__F2F1_cond (y : seq_type PerRACSI_RSInfo_v1660__list)
  : seq_cond PerRACSI_RSInfo_v1660__list y ->
 (PerRACSI_RSInfo_v1660__cond (PerRACSI_RSInfo_v1660__F2 y)) /\  PerRACSI_RSInfo_v1660__F1 (PerRACSI_RSInfo_v1660__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PerRACSI_RSInfo_v1660__cond. simpl in *. auto.
 - simpl. unfold PerRACSI_RSInfo_v1660__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PerRACSI_RSInfo_v1660__Format : T_Format PerRACSI_RSInfo_v1660__Type PerRACSI_RSInfo_v1660__cond :=
        proj2_format  PerRACSI_RSInfo_v1660__cond PerRACSI_RSInfo_v1660__list__Format
    PerRACSI_RSInfo_v1660__F1 PerRACSI_RSInfo_v1660__F2 PerRACSI_RSInfo_v1660__F1F2_cond  PerRACSI_RSInfo_v1660__F1F2_cond2 PerRACSI_RSInfo_v1660__F2F1_cond.
Opaque PerRACSI_RSInfo_v1660__cond PerRACSI_RSInfo_v1660__Format.

