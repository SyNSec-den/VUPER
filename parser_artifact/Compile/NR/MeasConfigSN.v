Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.NR_FreqInfo.

Opaque NR_FreqInfo__cond NR_FreqInfo__Format.

Definition MeasConfigSN__measuredFrequenciesSN__Type := list NR_FreqInfo__Type.

Lemma MeasConfigSN__measuredFrequenciesSN__helper1 : (0 <= 1 <= maxMeasFreqsSN)%Z. unfold maxMeasFreqsSN.
 lia. Qed.
Lemma MeasConfigSN__measuredFrequenciesSN__helper2 : to_bit_sz (Z.to_nat (maxMeasFreqsSN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasFreqsSN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasConfigSN__measuredFrequenciesSN__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasConfigSN__measuredFrequenciesSN__cond (z : MeasConfigSN__measuredFrequenciesSN__Type) :=  (1 <= Z.of_nat (length z) <= maxMeasFreqsSN)%Z /\ (list_and NR_FreqInfo__cond z) .

Record MeasConfigSN__Type : Set :=
  make__MeasConfigSN__Type {
    MeasConfigSN__measuredFrequenciesSN : option MeasConfigSN__measuredFrequenciesSN__Type ;
}.
Definition MeasConfigSN__root_list : list seq_elem := (
 Opt MeasConfigSN__measuredFrequenciesSN__Type MeasConfigSN__measuredFrequenciesSN__cond ::
 nil).
Definition MeasConfigSN__ext_list : list typ := (
  nil).
Definition MeasConfigSN__cond (z : MeasConfigSN__Type) := 
(  opt_cond MeasConfigSN__measuredFrequenciesSN__cond (MeasConfigSN__measuredFrequenciesSN z) /\
  True) /\ 
(  True).


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
Definition MeasConfigSN__measuredFrequenciesSN__Format : T_Format MeasConfigSN__measuredFrequenciesSN__Type MeasConfigSN__measuredFrequenciesSN__cond := seq_of_format NR_FreqInfo__Format 1 maxMeasFreqsSN MeasConfigSN__measuredFrequenciesSN__helper1 MeasConfigSN__measuredFrequenciesSN__helper2.

Opaque MeasConfigSN__measuredFrequenciesSN__cond MeasConfigSN__measuredFrequenciesSN__Format.


Definition MeasConfigSN__root_Format_Type := Eval cbn in seq_format_prod MeasConfigSN__root_list.
Definition MeasConfigSN__root_Format_list : MeasConfigSN__root_Format_Type :=
  (MeasConfigSN__measuredFrequenciesSN__Format, unit_format).

Definition MeasConfigSN__ext_Format_Type := Eval cbn in get_formats MeasConfigSN__ext_list.
Definition MeasConfigSN__ext_Format_list : MeasConfigSN__ext_Format_Type :=
  unit__Format.

Definition MeasConfigSN__list_type : Set := (seq_type MeasConfigSN__root_list) * (seq_ext_type MeasConfigSN__ext_list).
Definition MeasConfigSN__list_cond (z : MeasConfigSN__list_type) : Prop :=
        (seq_cond MeasConfigSN__root_list (fst z)) /\ (seq_ext_cond MeasConfigSN__ext_list (snd z)).
Definition MeasConfigSN__list_format : T_Format MeasConfigSN__list_type MeasConfigSN__list_cond :=
 (* Eval compute in *) seq_ext_format MeasConfigSN__root_list MeasConfigSN__root_Format_list MeasConfigSN__ext_list MeasConfigSN__ext_Format_list.

Opaque MeasConfigSN__list_format.
Definition MeasConfigSN__F1 (z : MeasConfigSN__Type) : MeasConfigSN__list_type :=
  (((MeasConfigSN__measuredFrequenciesSN z, tt)), (
tt)).
Definition MeasConfigSN__F2 (y : MeasConfigSN__list_type) : MeasConfigSN__Type :=
  match y with
  | ((j0, _), _)=>
    make__MeasConfigSN__Type j0
  end.
Definition MeasConfigSN__helper1 : (forall a : MeasConfigSN__Type, MeasConfigSN__cond a -> MeasConfigSN__list_cond (MeasConfigSN__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasConfigSN__helper2 : (forall a : MeasConfigSN__Type, MeasConfigSN__F2 (MeasConfigSN__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasConfigSN__helper3 : (forall b : MeasConfigSN__list_type, MeasConfigSN__list_cond b -> MeasConfigSN__cond (MeasConfigSN__F2 b) /\ MeasConfigSN__F1 (MeasConfigSN__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasConfigSN__cond, MeasConfigSN__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasConfigSN__Format : T_Format MeasConfigSN__Type MeasConfigSN__cond :=
 proj2_format MeasConfigSN__cond MeasConfigSN__list_format  MeasConfigSN__F1 MeasConfigSN__F2 MeasConfigSN__helper1 MeasConfigSN__helper2 MeasConfigSN__helper3.

Opaque MeasConfigSN__cond MeasConfigSN__Format.

