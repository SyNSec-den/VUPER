Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.RAN_AreaConfig.

Opaque RAN_AreaConfig__cond RAN_AreaConfig__Format.

Definition PLMN_RAN_AreaConfig__ran_Area__Type := list RAN_AreaConfig__Type.

Lemma PLMN_RAN_AreaConfig__ran_Area__helper1 : (0 <= 1 <= 16)%Z.  lia. Qed.
Lemma PLMN_RAN_AreaConfig__ran_Area__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PLMN_RAN_AreaConfig__ran_Area__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PLMN_RAN_AreaConfig__ran_Area__cond (z : PLMN_RAN_AreaConfig__ran_Area__Type) :=  (1 <= Z.of_nat (length z) <= 16)%Z /\ (list_and RAN_AreaConfig__cond z) .

Record PLMN_RAN_AreaConfig__Type : Set :=
  make__PLMN_RAN_AreaConfig__Type {
    PLMN_RAN_AreaConfig__plmn_Identity : option PLMN_Identity__Type ;
    PLMN_RAN_AreaConfig__ran_Area : PLMN_RAN_AreaConfig__ran_Area__Type ;
}.
Definition PLMN_RAN_AreaConfig__list := (
 Opt PLMN_Identity__Type PLMN_Identity__cond ::
 Nor PLMN_RAN_AreaConfig__ran_Area__Type PLMN_RAN_AreaConfig__ran_Area__cond ::
 nil).
Definition PLMN_RAN_AreaConfig__cond z := 
  opt_cond PLMN_Identity__cond (PLMN_RAN_AreaConfig__plmn_Identity z) /\
  PLMN_RAN_AreaConfig__ran_Area__cond (PLMN_RAN_AreaConfig__ran_Area z) /\
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
Definition PLMN_RAN_AreaConfig__ran_Area__Format : T_Format PLMN_RAN_AreaConfig__ran_Area__Type PLMN_RAN_AreaConfig__ran_Area__cond := seq_of_format RAN_AreaConfig__Format 1 16 PLMN_RAN_AreaConfig__ran_Area__helper1 PLMN_RAN_AreaConfig__ran_Area__helper2.

Opaque PLMN_RAN_AreaConfig__ran_Area__cond PLMN_RAN_AreaConfig__ran_Area__Format.


Definition PLMN_RAN_AreaConfig__Format_Type := Eval cbn in seq_format_prod PLMN_RAN_AreaConfig__list.
Definition PLMN_RAN_AreaConfig__Format_list : PLMN_RAN_AreaConfig__Format_Type :=
  (PLMN_Identity__Format, (PLMN_RAN_AreaConfig__ran_Area__Format, unit_format)).
Definition PLMN_RAN_AreaConfig__list__Format := (*Eval compute in *) seq_format PLMN_RAN_AreaConfig__list PLMN_RAN_AreaConfig__Format_list.
Definition PLMN_RAN_AreaConfig__F1 z :=
  (PLMN_RAN_AreaConfig__plmn_Identity z, (PLMN_RAN_AreaConfig__ran_Area z, tt)).
Definition PLMN_RAN_AreaConfig__F2 (y : seq_type PLMN_RAN_AreaConfig__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PLMN_RAN_AreaConfig__Type i0 i1
  end.
Lemma PLMN_RAN_AreaConfig__F1F2_cond (z : PLMN_RAN_AreaConfig__Type)
  : PLMN_RAN_AreaConfig__cond z ->
  (seq_cond PLMN_RAN_AreaConfig__list (PLMN_RAN_AreaConfig__F1 z)).
intro H. unfold PLMN_RAN_AreaConfig__cond in H. simpl. auto. Qed.
Lemma PLMN_RAN_AreaConfig__F1F2_cond2 (z : PLMN_RAN_AreaConfig__Type)
 : PLMN_RAN_AreaConfig__F2 (PLMN_RAN_AreaConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PLMN_RAN_AreaConfig__F2F1_cond (y : seq_type PLMN_RAN_AreaConfig__list)
  : seq_cond PLMN_RAN_AreaConfig__list y ->
 (PLMN_RAN_AreaConfig__cond (PLMN_RAN_AreaConfig__F2 y)) /\  PLMN_RAN_AreaConfig__F1 (PLMN_RAN_AreaConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PLMN_RAN_AreaConfig__cond. simpl in *. auto.
 - simpl. unfold PLMN_RAN_AreaConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PLMN_RAN_AreaConfig__Format : T_Format PLMN_RAN_AreaConfig__Type PLMN_RAN_AreaConfig__cond :=
        proj2_format  PLMN_RAN_AreaConfig__cond PLMN_RAN_AreaConfig__list__Format
    PLMN_RAN_AreaConfig__F1 PLMN_RAN_AreaConfig__F2 PLMN_RAN_AreaConfig__F1F2_cond  PLMN_RAN_AreaConfig__F1F2_cond2 PLMN_RAN_AreaConfig__F2F1_cond.
Opaque PLMN_RAN_AreaConfig__cond PLMN_RAN_AreaConfig__Format.

