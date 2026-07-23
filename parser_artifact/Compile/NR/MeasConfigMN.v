Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.NR_FreqInfo.

Opaque NR_FreqInfo__cond NR_FreqInfo__Format.

Definition MeasConfigMN__measuredFrequenciesMN__Type := list NR_FreqInfo__Type.

Lemma MeasConfigMN__measuredFrequenciesMN__helper1 : (0 <= 1 <= maxMeasFreqsMN)%Z. unfold maxMeasFreqsMN.
 lia. Qed.
Lemma MeasConfigMN__measuredFrequenciesMN__helper2 : to_bit_sz (Z.to_nat (maxMeasFreqsMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasFreqsMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasConfigMN__measuredFrequenciesMN__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasConfigMN__measuredFrequenciesMN__cond (z : MeasConfigMN__measuredFrequenciesMN__Type) :=  (1 <= Z.of_nat (length z) <= maxMeasFreqsMN)%Z /\ (list_and NR_FreqInfo__cond z) .

Require Import NR.SetupRelease.
Require Import NR.GapConfig.
Definition MeasConfigMN__measGapConfig__Type := SetupRelease__Type GapConfig__Type.
Definition MeasConfigMN__measGapConfig__cond := SetupRelease__cond _ GapConfig__cond.
Definition MeasConfigMN__measGapConfig__Format : T_Format MeasConfigMN__measGapConfig__Type MeasConfigMN__measGapConfig__cond := SetupRelease__Format _ _ GapConfig__Format.
Opaque MeasConfigMN__measGapConfig__cond MeasConfigMN__measGapConfig__Format.

Inductive MeasConfigMN__gapPurpose__Type : Set :=
 | MeasConfigMN__gapPurpose__perUE
 | MeasConfigMN__gapPurpose__perFR1
.
Definition MeasConfigMN__gapPurpose__cond := (fun (_ : MeasConfigMN__gapPurpose__Type) => True).
Lemma MeasConfigMN__gapPurpose__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasConfigMN__gapPurpose__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MeasConfigMN__gapPurpose__nat__helper.

Definition MeasConfigMN__gapPurpose__F1 t :=
  match t with
  | MeasConfigMN__gapPurpose__perUE => 0
  | MeasConfigMN__gapPurpose__perFR1 => 1
  end.
Definition MeasConfigMN__gapPurpose__F2 n :=
  match n with
  | 0 => MeasConfigMN__gapPurpose__perUE
  | 1 => MeasConfigMN__gapPurpose__perFR1
  | _ => MeasConfigMN__gapPurpose__perUE
  end.
Lemma MeasConfigMN__gapPurpose__F1F2 : forall x : MeasConfigMN__gapPurpose__Type, (MeasConfigMN__gapPurpose__F1 x <= 1) /\ MeasConfigMN__gapPurpose__F2 (MeasConfigMN__gapPurpose__F1 x) = x. imp_solve. Qed.
Lemma MeasConfigMN__gapPurpose__F2F1 : forall (y : nat) (H : y <= 1), MeasConfigMN__gapPurpose__F1 (MeasConfigMN__gapPurpose__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.GapConfig.
Definition MeasConfigMN__ext0O__measGapConfigFR2__Type := SetupRelease__Type GapConfig__Type.
Definition MeasConfigMN__ext0O__measGapConfigFR2__cond := SetupRelease__cond _ GapConfig__cond.
Definition MeasConfigMN__ext0O__measGapConfigFR2__Format : T_Format MeasConfigMN__ext0O__measGapConfigFR2__Type MeasConfigMN__ext0O__measGapConfigFR2__cond := SetupRelease__Format _ _ GapConfig__Format.
Opaque MeasConfigMN__ext0O__measGapConfigFR2__cond MeasConfigMN__ext0O__measGapConfigFR2__Format.

Record MeasConfigMN__ext0O__Type : Set :=
  make__MeasConfigMN__ext0O__Type {
    MeasConfigMN__ext0O__measGapConfigFR2 : option MeasConfigMN__ext0O__measGapConfigFR2__Type ;
}.
Definition MeasConfigMN__ext0O__list := (
 Opt MeasConfigMN__ext0O__measGapConfigFR2__Type MeasConfigMN__ext0O__measGapConfigFR2__cond ::
 nil).
Definition MeasConfigMN__ext0O__cond z := 
  opt_cond MeasConfigMN__ext0O__measGapConfigFR2__cond (MeasConfigMN__ext0O__measGapConfigFR2 z) /\
  True.

Definition MeasConfigMN__ext0__Type := MeasConfigMN__ext0O__Type.
Definition MeasConfigMN__ext0__cond := MeasConfigMN__ext0O__cond.

Inductive MeasConfigMN__ext1O__interFreqNoGap_r16__Type : Set :=
 | MeasConfigMN__ext1O__interFreqNoGap_r16__true
.
Definition MeasConfigMN__ext1O__interFreqNoGap_r16__cond := (fun (_ : MeasConfigMN__ext1O__interFreqNoGap_r16__Type) => True).
Lemma MeasConfigMN__ext1O__interFreqNoGap_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasConfigMN__ext1O__interFreqNoGap_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasConfigMN__ext1O__interFreqNoGap_r16__nat__helper.

Definition MeasConfigMN__ext1O__interFreqNoGap_r16__F1 t :=
  match t with
  | MeasConfigMN__ext1O__interFreqNoGap_r16__true => 0
  end.
Definition MeasConfigMN__ext1O__interFreqNoGap_r16__F2 n :=
  match n with
  | 0 => MeasConfigMN__ext1O__interFreqNoGap_r16__true
  | _ => MeasConfigMN__ext1O__interFreqNoGap_r16__true
  end.
Lemma MeasConfigMN__ext1O__interFreqNoGap_r16__F1F2 : forall x : MeasConfigMN__ext1O__interFreqNoGap_r16__Type, (MeasConfigMN__ext1O__interFreqNoGap_r16__F1 x <= 0) /\ MeasConfigMN__ext1O__interFreqNoGap_r16__F2 (MeasConfigMN__ext1O__interFreqNoGap_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasConfigMN__ext1O__interFreqNoGap_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasConfigMN__ext1O__interFreqNoGap_r16__F1 (MeasConfigMN__ext1O__interFreqNoGap_r16__F2 y) = y. enum_solve H y. Qed.

Record MeasConfigMN__ext1O__Type : Set :=
  make__MeasConfigMN__ext1O__Type {
    MeasConfigMN__ext1O__interFreqNoGap_r16 : option MeasConfigMN__ext1O__interFreqNoGap_r16__Type ;
}.
Definition MeasConfigMN__ext1O__list := (
 Opt MeasConfigMN__ext1O__interFreqNoGap_r16__Type MeasConfigMN__ext1O__interFreqNoGap_r16__cond ::
 nil).
Definition MeasConfigMN__ext1O__cond z := 
  opt_cond MeasConfigMN__ext1O__interFreqNoGap_r16__cond (MeasConfigMN__ext1O__interFreqNoGap_r16 z) /\
  True.

Definition MeasConfigMN__ext1__Type := MeasConfigMN__ext1O__Type.
Definition MeasConfigMN__ext1__cond := MeasConfigMN__ext1O__cond.

Record MeasConfigMN__Type : Set :=
  make__MeasConfigMN__Type {
    MeasConfigMN__measuredFrequenciesMN : option MeasConfigMN__measuredFrequenciesMN__Type ;
    MeasConfigMN__measGapConfig : option MeasConfigMN__measGapConfig__Type ;
    MeasConfigMN__gapPurpose : option MeasConfigMN__gapPurpose__Type ;
    MeasConfigMN__ext0 : option MeasConfigMN__ext0__Type ;
    MeasConfigMN__ext1 : option MeasConfigMN__ext1__Type ;
}.
Definition MeasConfigMN__root_list : list seq_elem := (
 Opt MeasConfigMN__measuredFrequenciesMN__Type MeasConfigMN__measuredFrequenciesMN__cond ::
 Opt MeasConfigMN__measGapConfig__Type MeasConfigMN__measGapConfig__cond ::
 Opt MeasConfigMN__gapPurpose__Type MeasConfigMN__gapPurpose__cond ::
 nil).
Definition MeasConfigMN__ext_list : list typ := (
  typ_cons MeasConfigMN__ext0__Type MeasConfigMN__ext0__cond ::
  typ_cons MeasConfigMN__ext1__Type MeasConfigMN__ext1__cond ::
  nil).
Definition MeasConfigMN__cond (z : MeasConfigMN__Type) := 
(  opt_cond MeasConfigMN__measuredFrequenciesMN__cond (MeasConfigMN__measuredFrequenciesMN z) /\
  opt_cond MeasConfigMN__measGapConfig__cond (MeasConfigMN__measGapConfig z) /\
  opt_cond MeasConfigMN__gapPurpose__cond (MeasConfigMN__gapPurpose z) /\
  True) /\ 
(  opt_cond MeasConfigMN__ext0__cond (MeasConfigMN__ext0 z) /\
  opt_cond MeasConfigMN__ext1__cond (MeasConfigMN__ext1 z) /\
  True).


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
Definition MeasConfigMN__measuredFrequenciesMN__Format : T_Format MeasConfigMN__measuredFrequenciesMN__Type MeasConfigMN__measuredFrequenciesMN__cond := seq_of_format NR_FreqInfo__Format 1 maxMeasFreqsMN MeasConfigMN__measuredFrequenciesMN__helper1 MeasConfigMN__measuredFrequenciesMN__helper2.

Opaque MeasConfigMN__measuredFrequenciesMN__cond MeasConfigMN__measuredFrequenciesMN__Format.

Opaque MeasConfigMN__measGapConfig__cond MeasConfigMN__measGapConfig__Format.

Definition MeasConfigMN__gapPurpose__Format : T_Format MeasConfigMN__gapPurpose__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasConfigMN__gapPurpose__nat__Format MeasConfigMN__gapPurpose__F1 MeasConfigMN__gapPurpose__F2 MeasConfigMN__gapPurpose__F1F2 MeasConfigMN__gapPurpose__F2F1.

Opaque MeasConfigMN__gapPurpose__cond MeasConfigMN__gapPurpose__Format.

Opaque MeasConfigMN__ext0O__measGapConfigFR2__cond MeasConfigMN__ext0O__measGapConfigFR2__Format.


Definition MeasConfigMN__ext0O__Format_Type := Eval cbn in seq_format_prod MeasConfigMN__ext0O__list.
Definition MeasConfigMN__ext0O__Format_list : MeasConfigMN__ext0O__Format_Type :=
  (MeasConfigMN__ext0O__measGapConfigFR2__Format, unit_format).
Definition MeasConfigMN__ext0O__list__Format := (*Eval compute in *) seq_format MeasConfigMN__ext0O__list MeasConfigMN__ext0O__Format_list.
Definition MeasConfigMN__ext0O__F1 z :=
  (MeasConfigMN__ext0O__measGapConfigFR2 z, tt).
Definition MeasConfigMN__ext0O__F2 (y : seq_type MeasConfigMN__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MeasConfigMN__ext0O__Type i0
  end.
Lemma MeasConfigMN__ext0O__F1F2_cond (z : MeasConfigMN__ext0O__Type)
  : MeasConfigMN__ext0O__cond z ->
  (seq_cond MeasConfigMN__ext0O__list (MeasConfigMN__ext0O__F1 z)).
intro H. unfold MeasConfigMN__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasConfigMN__ext0O__F1F2_cond2 (z : MeasConfigMN__ext0O__Type)
 : MeasConfigMN__ext0O__F2 (MeasConfigMN__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasConfigMN__ext0O__F2F1_cond (y : seq_type MeasConfigMN__ext0O__list)
  : seq_cond MeasConfigMN__ext0O__list y ->
 (MeasConfigMN__ext0O__cond (MeasConfigMN__ext0O__F2 y)) /\  MeasConfigMN__ext0O__F1 (MeasConfigMN__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasConfigMN__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasConfigMN__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasConfigMN__ext0O__Format : T_Format MeasConfigMN__ext0O__Type MeasConfigMN__ext0O__cond :=
        proj2_format  MeasConfigMN__ext0O__cond MeasConfigMN__ext0O__list__Format
    MeasConfigMN__ext0O__F1 MeasConfigMN__ext0O__F2 MeasConfigMN__ext0O__F1F2_cond  MeasConfigMN__ext0O__F1F2_cond2 MeasConfigMN__ext0O__F2F1_cond.
Opaque MeasConfigMN__ext0O__cond MeasConfigMN__ext0O__Format.

Definition MeasConfigMN__ext0__check_all_none (b : MeasConfigMN__ext0O__Type) : bool :=
match b with 
  | make__MeasConfigMN__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MeasConfigMN__ext0__Format : T_Format MeasConfigMN__ext0__Type MeasConfigMN__ext0__cond :=
  restrict_add_format MeasConfigMN__ext0__check_all_none MeasConfigMN__ext0O__Format.

Opaque MeasConfigMN__ext0__cond MeasConfigMN__ext0__Format.

Definition MeasConfigMN__ext1O__interFreqNoGap_r16__Format : T_Format MeasConfigMN__ext1O__interFreqNoGap_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasConfigMN__ext1O__interFreqNoGap_r16__nat__Format MeasConfigMN__ext1O__interFreqNoGap_r16__F1 MeasConfigMN__ext1O__interFreqNoGap_r16__F2 MeasConfigMN__ext1O__interFreqNoGap_r16__F1F2 MeasConfigMN__ext1O__interFreqNoGap_r16__F2F1.

Opaque MeasConfigMN__ext1O__interFreqNoGap_r16__cond MeasConfigMN__ext1O__interFreqNoGap_r16__Format.


Definition MeasConfigMN__ext1O__Format_Type := Eval cbn in seq_format_prod MeasConfigMN__ext1O__list.
Definition MeasConfigMN__ext1O__Format_list : MeasConfigMN__ext1O__Format_Type :=
  (MeasConfigMN__ext1O__interFreqNoGap_r16__Format, unit_format).
Definition MeasConfigMN__ext1O__list__Format := (*Eval compute in *) seq_format MeasConfigMN__ext1O__list MeasConfigMN__ext1O__Format_list.
Definition MeasConfigMN__ext1O__F1 z :=
  (MeasConfigMN__ext1O__interFreqNoGap_r16 z, tt).
Definition MeasConfigMN__ext1O__F2 (y : seq_type MeasConfigMN__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__MeasConfigMN__ext1O__Type i0
  end.
Lemma MeasConfigMN__ext1O__F1F2_cond (z : MeasConfigMN__ext1O__Type)
  : MeasConfigMN__ext1O__cond z ->
  (seq_cond MeasConfigMN__ext1O__list (MeasConfigMN__ext1O__F1 z)).
intro H. unfold MeasConfigMN__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasConfigMN__ext1O__F1F2_cond2 (z : MeasConfigMN__ext1O__Type)
 : MeasConfigMN__ext1O__F2 (MeasConfigMN__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasConfigMN__ext1O__F2F1_cond (y : seq_type MeasConfigMN__ext1O__list)
  : seq_cond MeasConfigMN__ext1O__list y ->
 (MeasConfigMN__ext1O__cond (MeasConfigMN__ext1O__F2 y)) /\  MeasConfigMN__ext1O__F1 (MeasConfigMN__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasConfigMN__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasConfigMN__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasConfigMN__ext1O__Format : T_Format MeasConfigMN__ext1O__Type MeasConfigMN__ext1O__cond :=
        proj2_format  MeasConfigMN__ext1O__cond MeasConfigMN__ext1O__list__Format
    MeasConfigMN__ext1O__F1 MeasConfigMN__ext1O__F2 MeasConfigMN__ext1O__F1F2_cond  MeasConfigMN__ext1O__F1F2_cond2 MeasConfigMN__ext1O__F2F1_cond.
Opaque MeasConfigMN__ext1O__cond MeasConfigMN__ext1O__Format.

Definition MeasConfigMN__ext1__check_all_none (b : MeasConfigMN__ext1O__Type) : bool :=
match b with 
  | make__MeasConfigMN__ext1O__Type None  => false 
  | _ => true 
 end.
Definition MeasConfigMN__ext1__Format : T_Format MeasConfigMN__ext1__Type MeasConfigMN__ext1__cond :=
  restrict_add_format MeasConfigMN__ext1__check_all_none MeasConfigMN__ext1O__Format.

Opaque MeasConfigMN__ext1__cond MeasConfigMN__ext1__Format.


Definition MeasConfigMN__root_Format_Type := Eval cbn in seq_format_prod MeasConfigMN__root_list.
Definition MeasConfigMN__root_Format_list : MeasConfigMN__root_Format_Type :=
  (MeasConfigMN__measuredFrequenciesMN__Format, (MeasConfigMN__measGapConfig__Format, (MeasConfigMN__gapPurpose__Format, unit_format))).

Definition MeasConfigMN__ext_Format_Type := Eval cbn in get_formats MeasConfigMN__ext_list.
Definition MeasConfigMN__ext_Format_list : MeasConfigMN__ext_Format_Type :=
  (MeasConfigMN__ext0__Format, (MeasConfigMN__ext1__Format, unit__Format)).

Definition MeasConfigMN__list_type : Set := (seq_type MeasConfigMN__root_list) * (seq_ext_type MeasConfigMN__ext_list).
Definition MeasConfigMN__list_cond (z : MeasConfigMN__list_type) : Prop :=
        (seq_cond MeasConfigMN__root_list (fst z)) /\ (seq_ext_cond MeasConfigMN__ext_list (snd z)).
Definition MeasConfigMN__list_format : T_Format MeasConfigMN__list_type MeasConfigMN__list_cond :=
 (* Eval compute in *) seq_ext_format MeasConfigMN__root_list MeasConfigMN__root_Format_list MeasConfigMN__ext_list MeasConfigMN__ext_Format_list.

Opaque MeasConfigMN__list_format.
Definition MeasConfigMN__F1 (z : MeasConfigMN__Type) : MeasConfigMN__list_type :=
  (((MeasConfigMN__measuredFrequenciesMN z, (MeasConfigMN__measGapConfig z, (MeasConfigMN__gapPurpose z, tt)))), (
(MeasConfigMN__ext0 z, (MeasConfigMN__ext1 z, tt)))).
Definition MeasConfigMN__F2 (y : MeasConfigMN__list_type) : MeasConfigMN__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, _)))=>
    make__MeasConfigMN__Type j0 j1 j2 i0 i1
  end.
Definition MeasConfigMN__helper1 : (forall a : MeasConfigMN__Type, MeasConfigMN__cond a -> MeasConfigMN__list_cond (MeasConfigMN__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasConfigMN__helper2 : (forall a : MeasConfigMN__Type, MeasConfigMN__F2 (MeasConfigMN__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasConfigMN__helper3 : (forall b : MeasConfigMN__list_type, MeasConfigMN__list_cond b -> MeasConfigMN__cond (MeasConfigMN__F2 b) /\ MeasConfigMN__F1 (MeasConfigMN__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasConfigMN__cond, MeasConfigMN__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasConfigMN__Format : T_Format MeasConfigMN__Type MeasConfigMN__cond :=
 proj2_format MeasConfigMN__cond MeasConfigMN__list_format  MeasConfigMN__F1 MeasConfigMN__F2 MeasConfigMN__helper1 MeasConfigMN__helper2 MeasConfigMN__helper3.

Opaque MeasConfigMN__cond MeasConfigMN__Format.

