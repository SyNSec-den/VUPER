Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Require Import NR.RAN_AreaCode.

Opaque RAN_AreaCode__cond RAN_AreaCode__Format.

Definition RAN_AreaConfig__ran_AreaCodeList__Type := list RAN_AreaCode__Type.

Lemma RAN_AreaConfig__ran_AreaCodeList__helper1 : (0 <= 1 <= 32)%Z.  lia. Qed.
Lemma RAN_AreaConfig__ran_AreaCodeList__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RAN_AreaConfig__ran_AreaCodeList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RAN_AreaConfig__ran_AreaCodeList__cond (z : RAN_AreaConfig__ran_AreaCodeList__Type) :=  (1 <= Z.of_nat (length z) <= 32)%Z /\ (list_and RAN_AreaCode__cond z) .

Record RAN_AreaConfig__Type : Set :=
  make__RAN_AreaConfig__Type {
    RAN_AreaConfig__trackingAreaCode : TrackingAreaCode__Type ;
    RAN_AreaConfig__ran_AreaCodeList : option RAN_AreaConfig__ran_AreaCodeList__Type ;
}.
Definition RAN_AreaConfig__list := (
 Nor TrackingAreaCode__Type TrackingAreaCode__cond ::
 Opt RAN_AreaConfig__ran_AreaCodeList__Type RAN_AreaConfig__ran_AreaCodeList__cond ::
 nil).
Definition RAN_AreaConfig__cond z := 
  TrackingAreaCode__cond (RAN_AreaConfig__trackingAreaCode z) /\
  opt_cond RAN_AreaConfig__ran_AreaCodeList__cond (RAN_AreaConfig__ran_AreaCodeList z) /\
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
Definition RAN_AreaConfig__ran_AreaCodeList__Format : T_Format RAN_AreaConfig__ran_AreaCodeList__Type RAN_AreaConfig__ran_AreaCodeList__cond := seq_of_format RAN_AreaCode__Format 1 32 RAN_AreaConfig__ran_AreaCodeList__helper1 RAN_AreaConfig__ran_AreaCodeList__helper2.

Opaque RAN_AreaConfig__ran_AreaCodeList__cond RAN_AreaConfig__ran_AreaCodeList__Format.


Definition RAN_AreaConfig__Format_Type := Eval cbn in seq_format_prod RAN_AreaConfig__list.
Definition RAN_AreaConfig__Format_list : RAN_AreaConfig__Format_Type :=
  (TrackingAreaCode__Format, (RAN_AreaConfig__ran_AreaCodeList__Format, unit_format)).
Definition RAN_AreaConfig__list__Format := (*Eval compute in *) seq_format RAN_AreaConfig__list RAN_AreaConfig__Format_list.
Definition RAN_AreaConfig__F1 z :=
  (RAN_AreaConfig__trackingAreaCode z, (RAN_AreaConfig__ran_AreaCodeList z, tt)).
Definition RAN_AreaConfig__F2 (y : seq_type RAN_AreaConfig__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RAN_AreaConfig__Type i0 i1
  end.
Lemma RAN_AreaConfig__F1F2_cond (z : RAN_AreaConfig__Type)
  : RAN_AreaConfig__cond z ->
  (seq_cond RAN_AreaConfig__list (RAN_AreaConfig__F1 z)).
intro H. unfold RAN_AreaConfig__cond in H. simpl. auto. Qed.
Lemma RAN_AreaConfig__F1F2_cond2 (z : RAN_AreaConfig__Type)
 : RAN_AreaConfig__F2 (RAN_AreaConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RAN_AreaConfig__F2F1_cond (y : seq_type RAN_AreaConfig__list)
  : seq_cond RAN_AreaConfig__list y ->
 (RAN_AreaConfig__cond (RAN_AreaConfig__F2 y)) /\  RAN_AreaConfig__F1 (RAN_AreaConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RAN_AreaConfig__cond. simpl in *. auto.
 - simpl. unfold RAN_AreaConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RAN_AreaConfig__Format : T_Format RAN_AreaConfig__Type RAN_AreaConfig__cond :=
        proj2_format  RAN_AreaConfig__cond RAN_AreaConfig__list__Format
    RAN_AreaConfig__F1 RAN_AreaConfig__F2 RAN_AreaConfig__F1F2_cond  RAN_AreaConfig__F1F2_cond2 RAN_AreaConfig__F2F1_cond.
Opaque RAN_AreaConfig__cond RAN_AreaConfig__Format.

