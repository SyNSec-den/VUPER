Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.MeasResultNR.

Opaque MeasResultNR__cond MeasResultNR__Format.

Require Import NR.MeasResultListNR.

Opaque MeasResultListNR__cond MeasResultListNR__Format.

Record MeasResult2NR__Type : Set :=
  make__MeasResult2NR__Type {
    MeasResult2NR__ssbFrequency : option ARFCN_ValueNR__Type ;
    MeasResult2NR__refFreqCSI_RS : option ARFCN_ValueNR__Type ;
    MeasResult2NR__measResultServingCell : option MeasResultNR__Type ;
    MeasResult2NR__measResultNeighCellListNR : option MeasResultListNR__Type ;
}.
Definition MeasResult2NR__root_list : list seq_elem := (
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt MeasResultNR__Type MeasResultNR__cond ::
 Opt MeasResultListNR__Type MeasResultListNR__cond ::
 nil).
Definition MeasResult2NR__ext_list : list typ := (
  nil).
Definition MeasResult2NR__cond (z : MeasResult2NR__Type) := 
(  opt_cond ARFCN_ValueNR__cond (MeasResult2NR__ssbFrequency z) /\
  opt_cond ARFCN_ValueNR__cond (MeasResult2NR__refFreqCSI_RS z) /\
  opt_cond MeasResultNR__cond (MeasResult2NR__measResultServingCell z) /\
  opt_cond MeasResultListNR__cond (MeasResult2NR__measResultNeighCellListNR z) /\
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

Definition MeasResult2NR__root_Format_Type := Eval cbn in seq_format_prod MeasResult2NR__root_list.
Definition MeasResult2NR__root_Format_list : MeasResult2NR__root_Format_Type :=
  (ARFCN_ValueNR__Format, (ARFCN_ValueNR__Format, (MeasResultNR__Format, (MeasResultListNR__Format, unit_format)))).

Definition MeasResult2NR__ext_Format_Type := Eval cbn in get_formats MeasResult2NR__ext_list.
Definition MeasResult2NR__ext_Format_list : MeasResult2NR__ext_Format_Type :=
  unit__Format.

Definition MeasResult2NR__list_type : Set := (seq_type MeasResult2NR__root_list) * (seq_ext_type MeasResult2NR__ext_list).
Definition MeasResult2NR__list_cond (z : MeasResult2NR__list_type) : Prop :=
        (seq_cond MeasResult2NR__root_list (fst z)) /\ (seq_ext_cond MeasResult2NR__ext_list (snd z)).
Definition MeasResult2NR__list_format : T_Format MeasResult2NR__list_type MeasResult2NR__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResult2NR__root_list MeasResult2NR__root_Format_list MeasResult2NR__ext_list MeasResult2NR__ext_Format_list.

Opaque MeasResult2NR__list_format.
Definition MeasResult2NR__F1 (z : MeasResult2NR__Type) : MeasResult2NR__list_type :=
  (((MeasResult2NR__ssbFrequency z, (MeasResult2NR__refFreqCSI_RS z, (MeasResult2NR__measResultServingCell z, (MeasResult2NR__measResultNeighCellListNR z, tt))))), (
tt)).
Definition MeasResult2NR__F2 (y : MeasResult2NR__list_type) : MeasResult2NR__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__MeasResult2NR__Type j0 j1 j2 j3
  end.
Definition MeasResult2NR__helper1 : (forall a : MeasResult2NR__Type, MeasResult2NR__cond a -> MeasResult2NR__list_cond (MeasResult2NR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResult2NR__helper2 : (forall a : MeasResult2NR__Type, MeasResult2NR__F2 (MeasResult2NR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResult2NR__helper3 : (forall b : MeasResult2NR__list_type, MeasResult2NR__list_cond b -> MeasResult2NR__cond (MeasResult2NR__F2 b) /\ MeasResult2NR__F1 (MeasResult2NR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResult2NR__cond, MeasResult2NR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResult2NR__Format : T_Format MeasResult2NR__Type MeasResult2NR__cond :=
 proj2_format MeasResult2NR__cond MeasResult2NR__list_format  MeasResult2NR__F1 MeasResult2NR__F2 MeasResult2NR__helper1 MeasResult2NR__helper2 MeasResult2NR__helper3.

Opaque MeasResult2NR__cond MeasResult2NR__Format.

