Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.MeasResultNR.

Opaque MeasResultNR__cond MeasResultNR__Format.

Require Import NR.MeasResultNR.

Opaque MeasResultNR__cond MeasResultNR__Format.

Record MeasResultServMO__Type : Set :=
  make__MeasResultServMO__Type {
    MeasResultServMO__servCellId : ServCellIndex__Type ;
    MeasResultServMO__measResultServingCell : MeasResultNR__Type ;
    MeasResultServMO__measResultBestNeighCell : option MeasResultNR__Type ;
}.
Definition MeasResultServMO__root_list : list seq_elem := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor MeasResultNR__Type MeasResultNR__cond ::
 Opt MeasResultNR__Type MeasResultNR__cond ::
 nil).
Definition MeasResultServMO__ext_list : list typ := (
  nil).
Definition MeasResultServMO__cond (z : MeasResultServMO__Type) := 
(  ServCellIndex__cond (MeasResultServMO__servCellId z) /\
  MeasResultNR__cond (MeasResultServMO__measResultServingCell z) /\
  opt_cond MeasResultNR__cond (MeasResultServMO__measResultBestNeighCell z) /\
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

Definition MeasResultServMO__root_Format_Type := Eval cbn in seq_format_prod MeasResultServMO__root_list.
Definition MeasResultServMO__root_Format_list : MeasResultServMO__root_Format_Type :=
  (ServCellIndex__Format, (MeasResultNR__Format, (MeasResultNR__Format, unit_format))).

Definition MeasResultServMO__ext_Format_Type := Eval cbn in get_formats MeasResultServMO__ext_list.
Definition MeasResultServMO__ext_Format_list : MeasResultServMO__ext_Format_Type :=
  unit__Format.

Definition MeasResultServMO__list_type : Set := (seq_type MeasResultServMO__root_list) * (seq_ext_type MeasResultServMO__ext_list).
Definition MeasResultServMO__list_cond (z : MeasResultServMO__list_type) : Prop :=
        (seq_cond MeasResultServMO__root_list (fst z)) /\ (seq_ext_cond MeasResultServMO__ext_list (snd z)).
Definition MeasResultServMO__list_format : T_Format MeasResultServMO__list_type MeasResultServMO__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultServMO__root_list MeasResultServMO__root_Format_list MeasResultServMO__ext_list MeasResultServMO__ext_Format_list.

Opaque MeasResultServMO__list_format.
Definition MeasResultServMO__F1 (z : MeasResultServMO__Type) : MeasResultServMO__list_type :=
  (((MeasResultServMO__servCellId z, (MeasResultServMO__measResultServingCell z, (MeasResultServMO__measResultBestNeighCell z, tt)))), (
tt)).
Definition MeasResultServMO__F2 (y : MeasResultServMO__list_type) : MeasResultServMO__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__MeasResultServMO__Type j0 j1 j2
  end.
Definition MeasResultServMO__helper1 : (forall a : MeasResultServMO__Type, MeasResultServMO__cond a -> MeasResultServMO__list_cond (MeasResultServMO__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultServMO__helper2 : (forall a : MeasResultServMO__Type, MeasResultServMO__F2 (MeasResultServMO__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultServMO__helper3 : (forall b : MeasResultServMO__list_type, MeasResultServMO__list_cond b -> MeasResultServMO__cond (MeasResultServMO__F2 b) /\ MeasResultServMO__F1 (MeasResultServMO__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultServMO__cond, MeasResultServMO__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultServMO__Format : T_Format MeasResultServMO__Type MeasResultServMO__cond :=
 proj2_format MeasResultServMO__cond MeasResultServMO__list_format  MeasResultServMO__F1 MeasResultServMO__F2 MeasResultServMO__helper1 MeasResultServMO__helper2 MeasResultServMO__helper3.

Opaque MeasResultServMO__cond MeasResultServMO__Format.

