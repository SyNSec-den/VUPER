Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Lemma UplinkTxDirectCurrentBWP__txDirectCurrentLocation__helper1 : (0 <= 3301)%Z.  lia. Qed.
Lemma UplinkTxDirectCurrentBWP__txDirectCurrentLocation__helper2 : to_bit_sz (Z.to_nat (3301 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3301 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkTxDirectCurrentBWP__txDirectCurrentLocation__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkTxDirectCurrentBWP__txDirectCurrentLocation__Type := Z.
Definition UplinkTxDirectCurrentBWP__txDirectCurrentLocation__cond := (fun z => (0 <= z <= 3301)%Z).
Record UplinkTxDirectCurrentBWP__Type : Set :=
  make__UplinkTxDirectCurrentBWP__Type {
    UplinkTxDirectCurrentBWP__bwp_Id : BWP_Id__Type ;
    UplinkTxDirectCurrentBWP__shift7dot5kHz : bool ;
    UplinkTxDirectCurrentBWP__txDirectCurrentLocation : Z ;
}.
Definition UplinkTxDirectCurrentBWP__list := (
 Nor BWP_Id__Type BWP_Id__cond ::
 Nor bool (fun _ => True) ::
 Nor Z UplinkTxDirectCurrentBWP__txDirectCurrentLocation__cond ::
 nil).
Definition UplinkTxDirectCurrentBWP__cond z := 
  BWP_Id__cond (UplinkTxDirectCurrentBWP__bwp_Id z) /\
  (fun _ => True) (UplinkTxDirectCurrentBWP__shift7dot5kHz z) /\
  UplinkTxDirectCurrentBWP__txDirectCurrentLocation__cond (UplinkTxDirectCurrentBWP__txDirectCurrentLocation z) /\
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
Definition UplinkTxDirectCurrentBWP__txDirectCurrentLocation__Format : T_Format Z UplinkTxDirectCurrentBWP__txDirectCurrentLocation__cond :=
 ranged_int_format (0) (3301) UplinkTxDirectCurrentBWP__txDirectCurrentLocation__helper1 UplinkTxDirectCurrentBWP__txDirectCurrentLocation__helper2.

Opaque UplinkTxDirectCurrentBWP__txDirectCurrentLocation__cond UplinkTxDirectCurrentBWP__txDirectCurrentLocation__Format.


Definition UplinkTxDirectCurrentBWP__Format_Type := Eval cbn in seq_format_prod UplinkTxDirectCurrentBWP__list.
Definition UplinkTxDirectCurrentBWP__Format_list : UplinkTxDirectCurrentBWP__Format_Type :=
  (BWP_Id__Format, (bool__Format, (UplinkTxDirectCurrentBWP__txDirectCurrentLocation__Format, unit_format))).
Definition UplinkTxDirectCurrentBWP__list__Format := (*Eval compute in *) seq_format UplinkTxDirectCurrentBWP__list UplinkTxDirectCurrentBWP__Format_list.
Definition UplinkTxDirectCurrentBWP__F1 z :=
  (UplinkTxDirectCurrentBWP__bwp_Id z, (UplinkTxDirectCurrentBWP__shift7dot5kHz z, (UplinkTxDirectCurrentBWP__txDirectCurrentLocation z, tt))).
Definition UplinkTxDirectCurrentBWP__F2 (y : seq_type UplinkTxDirectCurrentBWP__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UplinkTxDirectCurrentBWP__Type i0 i1 i2
  end.
Lemma UplinkTxDirectCurrentBWP__F1F2_cond (z : UplinkTxDirectCurrentBWP__Type)
  : UplinkTxDirectCurrentBWP__cond z ->
  (seq_cond UplinkTxDirectCurrentBWP__list (UplinkTxDirectCurrentBWP__F1 z)).
intro H. unfold UplinkTxDirectCurrentBWP__cond in H. simpl. auto. Qed.
Lemma UplinkTxDirectCurrentBWP__F1F2_cond2 (z : UplinkTxDirectCurrentBWP__Type)
 : UplinkTxDirectCurrentBWP__F2 (UplinkTxDirectCurrentBWP__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkTxDirectCurrentBWP__F2F1_cond (y : seq_type UplinkTxDirectCurrentBWP__list)
  : seq_cond UplinkTxDirectCurrentBWP__list y ->
 (UplinkTxDirectCurrentBWP__cond (UplinkTxDirectCurrentBWP__F2 y)) /\  UplinkTxDirectCurrentBWP__F1 (UplinkTxDirectCurrentBWP__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkTxDirectCurrentBWP__cond. simpl in *. auto.
 - simpl. unfold UplinkTxDirectCurrentBWP__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkTxDirectCurrentBWP__Format : T_Format UplinkTxDirectCurrentBWP__Type UplinkTxDirectCurrentBWP__cond :=
        proj2_format  UplinkTxDirectCurrentBWP__cond UplinkTxDirectCurrentBWP__list__Format
    UplinkTxDirectCurrentBWP__F1 UplinkTxDirectCurrentBWP__F2 UplinkTxDirectCurrentBWP__F1F2_cond  UplinkTxDirectCurrentBWP__F1F2_cond2 UplinkTxDirectCurrentBWP__F2F1_cond.
Opaque UplinkTxDirectCurrentBWP__cond UplinkTxDirectCurrentBWP__Format.

