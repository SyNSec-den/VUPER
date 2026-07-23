Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.MeasResultEUTRA.

Opaque MeasResultEUTRA__cond MeasResultEUTRA__Format.

Require Import NR.MeasResultEUTRA.

Opaque MeasResultEUTRA__cond MeasResultEUTRA__Format.

Record MeasResult2EUTRA__Type : Set :=
  make__MeasResult2EUTRA__Type {
    MeasResult2EUTRA__carrierFreq : ARFCN_ValueEUTRA__Type ;
    MeasResult2EUTRA__measResultServingCell : option MeasResultEUTRA__Type ;
    MeasResult2EUTRA__measResultBestNeighCell : option MeasResultEUTRA__Type ;
}.
Definition MeasResult2EUTRA__root_list : list seq_elem := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Opt MeasResultEUTRA__Type MeasResultEUTRA__cond ::
 Opt MeasResultEUTRA__Type MeasResultEUTRA__cond ::
 nil).
Definition MeasResult2EUTRA__ext_list : list typ := (
  nil).
Definition MeasResult2EUTRA__cond (z : MeasResult2EUTRA__Type) := 
(  ARFCN_ValueEUTRA__cond (MeasResult2EUTRA__carrierFreq z) /\
  opt_cond MeasResultEUTRA__cond (MeasResult2EUTRA__measResultServingCell z) /\
  opt_cond MeasResultEUTRA__cond (MeasResult2EUTRA__measResultBestNeighCell z) /\
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

Definition MeasResult2EUTRA__root_Format_Type := Eval cbn in seq_format_prod MeasResult2EUTRA__root_list.
Definition MeasResult2EUTRA__root_Format_list : MeasResult2EUTRA__root_Format_Type :=
  (ARFCN_ValueEUTRA__Format, (MeasResultEUTRA__Format, (MeasResultEUTRA__Format, unit_format))).

Definition MeasResult2EUTRA__ext_Format_Type := Eval cbn in get_formats MeasResult2EUTRA__ext_list.
Definition MeasResult2EUTRA__ext_Format_list : MeasResult2EUTRA__ext_Format_Type :=
  unit__Format.

Definition MeasResult2EUTRA__list_type : Set := (seq_type MeasResult2EUTRA__root_list) * (seq_ext_type MeasResult2EUTRA__ext_list).
Definition MeasResult2EUTRA__list_cond (z : MeasResult2EUTRA__list_type) : Prop :=
        (seq_cond MeasResult2EUTRA__root_list (fst z)) /\ (seq_ext_cond MeasResult2EUTRA__ext_list (snd z)).
Definition MeasResult2EUTRA__list_format : T_Format MeasResult2EUTRA__list_type MeasResult2EUTRA__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResult2EUTRA__root_list MeasResult2EUTRA__root_Format_list MeasResult2EUTRA__ext_list MeasResult2EUTRA__ext_Format_list.

Opaque MeasResult2EUTRA__list_format.
Definition MeasResult2EUTRA__F1 (z : MeasResult2EUTRA__Type) : MeasResult2EUTRA__list_type :=
  (((MeasResult2EUTRA__carrierFreq z, (MeasResult2EUTRA__measResultServingCell z, (MeasResult2EUTRA__measResultBestNeighCell z, tt)))), (
tt)).
Definition MeasResult2EUTRA__F2 (y : MeasResult2EUTRA__list_type) : MeasResult2EUTRA__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__MeasResult2EUTRA__Type j0 j1 j2
  end.
Definition MeasResult2EUTRA__helper1 : (forall a : MeasResult2EUTRA__Type, MeasResult2EUTRA__cond a -> MeasResult2EUTRA__list_cond (MeasResult2EUTRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResult2EUTRA__helper2 : (forall a : MeasResult2EUTRA__Type, MeasResult2EUTRA__F2 (MeasResult2EUTRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResult2EUTRA__helper3 : (forall b : MeasResult2EUTRA__list_type, MeasResult2EUTRA__list_cond b -> MeasResult2EUTRA__cond (MeasResult2EUTRA__F2 b) /\ MeasResult2EUTRA__F1 (MeasResult2EUTRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResult2EUTRA__cond, MeasResult2EUTRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResult2EUTRA__Format : T_Format MeasResult2EUTRA__Type MeasResult2EUTRA__cond :=
 proj2_format MeasResult2EUTRA__cond MeasResult2EUTRA__list_format  MeasResult2EUTRA__F1 MeasResult2EUTRA__F2 MeasResult2EUTRA__helper1 MeasResult2EUTRA__helper2 MeasResult2EUTRA__helper3.

Opaque MeasResult2EUTRA__cond MeasResult2EUTRA__Format.

