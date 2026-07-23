Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Record NR_FreqInfo__Type : Set :=
  make__NR_FreqInfo__Type {
    NR_FreqInfo__measuredFrequency : option ARFCN_ValueNR__Type ;
}.
Definition NR_FreqInfo__root_list : list seq_elem := (
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 nil).
Definition NR_FreqInfo__ext_list : list typ := (
  nil).
Definition NR_FreqInfo__cond (z : NR_FreqInfo__Type) := 
(  opt_cond ARFCN_ValueNR__cond (NR_FreqInfo__measuredFrequency z) /\
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

Definition NR_FreqInfo__root_Format_Type := Eval cbn in seq_format_prod NR_FreqInfo__root_list.
Definition NR_FreqInfo__root_Format_list : NR_FreqInfo__root_Format_Type :=
  (ARFCN_ValueNR__Format, unit_format).

Definition NR_FreqInfo__ext_Format_Type := Eval cbn in get_formats NR_FreqInfo__ext_list.
Definition NR_FreqInfo__ext_Format_list : NR_FreqInfo__ext_Format_Type :=
  unit__Format.

Definition NR_FreqInfo__list_type : Set := (seq_type NR_FreqInfo__root_list) * (seq_ext_type NR_FreqInfo__ext_list).
Definition NR_FreqInfo__list_cond (z : NR_FreqInfo__list_type) : Prop :=
        (seq_cond NR_FreqInfo__root_list (fst z)) /\ (seq_ext_cond NR_FreqInfo__ext_list (snd z)).
Definition NR_FreqInfo__list_format : T_Format NR_FreqInfo__list_type NR_FreqInfo__list_cond :=
 (* Eval compute in *) seq_ext_format NR_FreqInfo__root_list NR_FreqInfo__root_Format_list NR_FreqInfo__ext_list NR_FreqInfo__ext_Format_list.

Opaque NR_FreqInfo__list_format.
Definition NR_FreqInfo__F1 (z : NR_FreqInfo__Type) : NR_FreqInfo__list_type :=
  (((NR_FreqInfo__measuredFrequency z, tt)), (
tt)).
Definition NR_FreqInfo__F2 (y : NR_FreqInfo__list_type) : NR_FreqInfo__Type :=
  match y with
  | ((j0, _), _)=>
    make__NR_FreqInfo__Type j0
  end.
Definition NR_FreqInfo__helper1 : (forall a : NR_FreqInfo__Type, NR_FreqInfo__cond a -> NR_FreqInfo__list_cond (NR_FreqInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NR_FreqInfo__helper2 : (forall a : NR_FreqInfo__Type, NR_FreqInfo__F2 (NR_FreqInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NR_FreqInfo__helper3 : (forall b : NR_FreqInfo__list_type, NR_FreqInfo__list_cond b -> NR_FreqInfo__cond (NR_FreqInfo__F2 b) /\ NR_FreqInfo__F1 (NR_FreqInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NR_FreqInfo__cond, NR_FreqInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NR_FreqInfo__Format : T_Format NR_FreqInfo__Type NR_FreqInfo__cond :=
 proj2_format NR_FreqInfo__cond NR_FreqInfo__list_format  NR_FreqInfo__F1 NR_FreqInfo__F2 NR_FreqInfo__helper1 NR_FreqInfo__helper2 NR_FreqInfo__helper3.

Opaque NR_FreqInfo__cond NR_FreqInfo__Format.

