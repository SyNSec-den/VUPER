Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Definition CellGrouping_r16__mcg_r16__Type := list FreqBandIndicatorNR__Type.

Lemma CellGrouping_r16__mcg_r16__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma CellGrouping_r16__mcg_r16__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGrouping_r16__mcg_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGrouping_r16__mcg_r16__cond (z : CellGrouping_r16__mcg_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and FreqBandIndicatorNR__cond z) .

Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Definition CellGrouping_r16__scg_r16__Type := list FreqBandIndicatorNR__Type.

Lemma CellGrouping_r16__scg_r16__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma CellGrouping_r16__scg_r16__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGrouping_r16__scg_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGrouping_r16__scg_r16__cond (z : CellGrouping_r16__scg_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and FreqBandIndicatorNR__cond z) .

Inductive CellGrouping_r16__mode_r16__Type : Set :=
 | CellGrouping_r16__mode_r16__sync
 | CellGrouping_r16__mode_r16__async
.
Definition CellGrouping_r16__mode_r16__cond := (fun (_ : CellGrouping_r16__mode_r16__Type) => True).
Lemma CellGrouping_r16__mode_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGrouping_r16__mode_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CellGrouping_r16__mode_r16__nat__helper.

Definition CellGrouping_r16__mode_r16__F1 t :=
  match t with
  | CellGrouping_r16__mode_r16__sync => 0
  | CellGrouping_r16__mode_r16__async => 1
  end.
Definition CellGrouping_r16__mode_r16__F2 n :=
  match n with
  | 0 => CellGrouping_r16__mode_r16__sync
  | 1 => CellGrouping_r16__mode_r16__async
  | _ => CellGrouping_r16__mode_r16__sync
  end.
Lemma CellGrouping_r16__mode_r16__F1F2 : forall x : CellGrouping_r16__mode_r16__Type, (CellGrouping_r16__mode_r16__F1 x <= 1) /\ CellGrouping_r16__mode_r16__F2 (CellGrouping_r16__mode_r16__F1 x) = x. imp_solve. Qed.
Lemma CellGrouping_r16__mode_r16__F2F1 : forall (y : nat) (H : y <= 1), CellGrouping_r16__mode_r16__F1 (CellGrouping_r16__mode_r16__F2 y) = y. enum_solve H y. Qed.

Record CellGrouping_r16__Type : Set :=
  make__CellGrouping_r16__Type {
    CellGrouping_r16__mcg_r16 : CellGrouping_r16__mcg_r16__Type ;
    CellGrouping_r16__scg_r16 : CellGrouping_r16__scg_r16__Type ;
    CellGrouping_r16__mode_r16 : CellGrouping_r16__mode_r16__Type ;
}.
Definition CellGrouping_r16__list := (
 Nor CellGrouping_r16__mcg_r16__Type CellGrouping_r16__mcg_r16__cond ::
 Nor CellGrouping_r16__scg_r16__Type CellGrouping_r16__scg_r16__cond ::
 Nor CellGrouping_r16__mode_r16__Type CellGrouping_r16__mode_r16__cond ::
 nil).
Definition CellGrouping_r16__cond z := 
  CellGrouping_r16__mcg_r16__cond (CellGrouping_r16__mcg_r16 z) /\
  CellGrouping_r16__scg_r16__cond (CellGrouping_r16__scg_r16 z) /\
  CellGrouping_r16__mode_r16__cond (CellGrouping_r16__mode_r16 z) /\
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
Definition CellGrouping_r16__mcg_r16__Format : T_Format CellGrouping_r16__mcg_r16__Type CellGrouping_r16__mcg_r16__cond := seq_of_format FreqBandIndicatorNR__Format 1 maxBands CellGrouping_r16__mcg_r16__helper1 CellGrouping_r16__mcg_r16__helper2.

Opaque CellGrouping_r16__mcg_r16__cond CellGrouping_r16__mcg_r16__Format.

Definition CellGrouping_r16__scg_r16__Format : T_Format CellGrouping_r16__scg_r16__Type CellGrouping_r16__scg_r16__cond := seq_of_format FreqBandIndicatorNR__Format 1 maxBands CellGrouping_r16__scg_r16__helper1 CellGrouping_r16__scg_r16__helper2.

Opaque CellGrouping_r16__scg_r16__cond CellGrouping_r16__scg_r16__Format.

Definition CellGrouping_r16__mode_r16__Format : T_Format CellGrouping_r16__mode_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGrouping_r16__mode_r16__nat__Format CellGrouping_r16__mode_r16__F1 CellGrouping_r16__mode_r16__F2 CellGrouping_r16__mode_r16__F1F2 CellGrouping_r16__mode_r16__F2F1.

Opaque CellGrouping_r16__mode_r16__cond CellGrouping_r16__mode_r16__Format.


Definition CellGrouping_r16__Format_Type := Eval cbn in seq_format_prod CellGrouping_r16__list.
Definition CellGrouping_r16__Format_list : CellGrouping_r16__Format_Type :=
  (CellGrouping_r16__mcg_r16__Format, (CellGrouping_r16__scg_r16__Format, (CellGrouping_r16__mode_r16__Format, unit_format))).
Definition CellGrouping_r16__list__Format := (*Eval compute in *) seq_format CellGrouping_r16__list CellGrouping_r16__Format_list.
Definition CellGrouping_r16__F1 z :=
  (CellGrouping_r16__mcg_r16 z, (CellGrouping_r16__scg_r16 z, (CellGrouping_r16__mode_r16 z, tt))).
Definition CellGrouping_r16__F2 (y : seq_type CellGrouping_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CellGrouping_r16__Type i0 i1 i2
  end.
Lemma CellGrouping_r16__F1F2_cond (z : CellGrouping_r16__Type)
  : CellGrouping_r16__cond z ->
  (seq_cond CellGrouping_r16__list (CellGrouping_r16__F1 z)).
intro H. unfold CellGrouping_r16__cond in H. simpl. auto. Qed.
Lemma CellGrouping_r16__F1F2_cond2 (z : CellGrouping_r16__Type)
 : CellGrouping_r16__F2 (CellGrouping_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellGrouping_r16__F2F1_cond (y : seq_type CellGrouping_r16__list)
  : seq_cond CellGrouping_r16__list y ->
 (CellGrouping_r16__cond (CellGrouping_r16__F2 y)) /\  CellGrouping_r16__F1 (CellGrouping_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellGrouping_r16__cond. simpl in *. auto.
 - simpl. unfold CellGrouping_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellGrouping_r16__Format : T_Format CellGrouping_r16__Type CellGrouping_r16__cond :=
        proj2_format  CellGrouping_r16__cond CellGrouping_r16__list__Format
    CellGrouping_r16__F1 CellGrouping_r16__F2 CellGrouping_r16__F1F2_cond  CellGrouping_r16__F1F2_cond2 CellGrouping_r16__F2F1_cond.
Opaque CellGrouping_r16__cond CellGrouping_r16__Format.

