Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueUTRA_FDD_r16.

Opaque ARFCN_ValueUTRA_FDD_r16__cond ARFCN_ValueUTRA_FDD_r16__Format.

Require Import NR.UTRA_FDD_Q_OffsetRange_r16.

Opaque UTRA_FDD_Q_OffsetRange_r16__cond UTRA_FDD_Q_OffsetRange_r16__Format.

Require Import NR.UTRA_FDD_CellIndexList_r16.

Opaque UTRA_FDD_CellIndexList_r16__cond UTRA_FDD_CellIndexList_r16__Format.

Require Import NR.CellsToAddModListUTRA_FDD_r16.

Opaque CellsToAddModListUTRA_FDD_r16__cond CellsToAddModListUTRA_FDD_r16__Format.

Record MeasObjectUTRA_FDD_r16__Type : Set :=
  make__MeasObjectUTRA_FDD_r16__Type {
    MeasObjectUTRA_FDD_r16__carrierFreq_r16 : ARFCN_ValueUTRA_FDD_r16__Type ;
    MeasObjectUTRA_FDD_r16__utra_FDD_Q_OffsetRange_r16 : option UTRA_FDD_Q_OffsetRange_r16__Type ;
    MeasObjectUTRA_FDD_r16__cellsToRemoveList_r16 : option UTRA_FDD_CellIndexList_r16__Type ;
    MeasObjectUTRA_FDD_r16__cellsToAddModList_r16 : option CellsToAddModListUTRA_FDD_r16__Type ;
}.
Definition MeasObjectUTRA_FDD_r16__root_list : list seq_elem := (
 Nor ARFCN_ValueUTRA_FDD_r16__Type ARFCN_ValueUTRA_FDD_r16__cond ::
 Opt UTRA_FDD_Q_OffsetRange_r16__Type UTRA_FDD_Q_OffsetRange_r16__cond ::
 Opt UTRA_FDD_CellIndexList_r16__Type UTRA_FDD_CellIndexList_r16__cond ::
 Opt CellsToAddModListUTRA_FDD_r16__Type CellsToAddModListUTRA_FDD_r16__cond ::
 nil).
Definition MeasObjectUTRA_FDD_r16__ext_list : list typ := (
  nil).
Definition MeasObjectUTRA_FDD_r16__cond (z : MeasObjectUTRA_FDD_r16__Type) := 
(  ARFCN_ValueUTRA_FDD_r16__cond (MeasObjectUTRA_FDD_r16__carrierFreq_r16 z) /\
  opt_cond UTRA_FDD_Q_OffsetRange_r16__cond (MeasObjectUTRA_FDD_r16__utra_FDD_Q_OffsetRange_r16 z) /\
  opt_cond UTRA_FDD_CellIndexList_r16__cond (MeasObjectUTRA_FDD_r16__cellsToRemoveList_r16 z) /\
  opt_cond CellsToAddModListUTRA_FDD_r16__cond (MeasObjectUTRA_FDD_r16__cellsToAddModList_r16 z) /\
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

Definition MeasObjectUTRA_FDD_r16__root_Format_Type := Eval cbn in seq_format_prod MeasObjectUTRA_FDD_r16__root_list.
Definition MeasObjectUTRA_FDD_r16__root_Format_list : MeasObjectUTRA_FDD_r16__root_Format_Type :=
  (ARFCN_ValueUTRA_FDD_r16__Format, (UTRA_FDD_Q_OffsetRange_r16__Format, (UTRA_FDD_CellIndexList_r16__Format, (CellsToAddModListUTRA_FDD_r16__Format, unit_format)))).

Definition MeasObjectUTRA_FDD_r16__ext_Format_Type := Eval cbn in get_formats MeasObjectUTRA_FDD_r16__ext_list.
Definition MeasObjectUTRA_FDD_r16__ext_Format_list : MeasObjectUTRA_FDD_r16__ext_Format_Type :=
  unit__Format.

Definition MeasObjectUTRA_FDD_r16__list_type : Set := (seq_type MeasObjectUTRA_FDD_r16__root_list) * (seq_ext_type MeasObjectUTRA_FDD_r16__ext_list).
Definition MeasObjectUTRA_FDD_r16__list_cond (z : MeasObjectUTRA_FDD_r16__list_type) : Prop :=
        (seq_cond MeasObjectUTRA_FDD_r16__root_list (fst z)) /\ (seq_ext_cond MeasObjectUTRA_FDD_r16__ext_list (snd z)).
Definition MeasObjectUTRA_FDD_r16__list_format : T_Format MeasObjectUTRA_FDD_r16__list_type MeasObjectUTRA_FDD_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasObjectUTRA_FDD_r16__root_list MeasObjectUTRA_FDD_r16__root_Format_list MeasObjectUTRA_FDD_r16__ext_list MeasObjectUTRA_FDD_r16__ext_Format_list.

Opaque MeasObjectUTRA_FDD_r16__list_format.
Definition MeasObjectUTRA_FDD_r16__F1 (z : MeasObjectUTRA_FDD_r16__Type) : MeasObjectUTRA_FDD_r16__list_type :=
  (((MeasObjectUTRA_FDD_r16__carrierFreq_r16 z, (MeasObjectUTRA_FDD_r16__utra_FDD_Q_OffsetRange_r16 z, (MeasObjectUTRA_FDD_r16__cellsToRemoveList_r16 z, (MeasObjectUTRA_FDD_r16__cellsToAddModList_r16 z, tt))))), (
tt)).
Definition MeasObjectUTRA_FDD_r16__F2 (y : MeasObjectUTRA_FDD_r16__list_type) : MeasObjectUTRA_FDD_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__MeasObjectUTRA_FDD_r16__Type j0 j1 j2 j3
  end.
Definition MeasObjectUTRA_FDD_r16__helper1 : (forall a : MeasObjectUTRA_FDD_r16__Type, MeasObjectUTRA_FDD_r16__cond a -> MeasObjectUTRA_FDD_r16__list_cond (MeasObjectUTRA_FDD_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasObjectUTRA_FDD_r16__helper2 : (forall a : MeasObjectUTRA_FDD_r16__Type, MeasObjectUTRA_FDD_r16__F2 (MeasObjectUTRA_FDD_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasObjectUTRA_FDD_r16__helper3 : (forall b : MeasObjectUTRA_FDD_r16__list_type, MeasObjectUTRA_FDD_r16__list_cond b -> MeasObjectUTRA_FDD_r16__cond (MeasObjectUTRA_FDD_r16__F2 b) /\ MeasObjectUTRA_FDD_r16__F1 (MeasObjectUTRA_FDD_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasObjectUTRA_FDD_r16__cond, MeasObjectUTRA_FDD_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasObjectUTRA_FDD_r16__Format : T_Format MeasObjectUTRA_FDD_r16__Type MeasObjectUTRA_FDD_r16__cond :=
 proj2_format MeasObjectUTRA_FDD_r16__cond MeasObjectUTRA_FDD_r16__list_format  MeasObjectUTRA_FDD_r16__F1 MeasObjectUTRA_FDD_r16__F2 MeasObjectUTRA_FDD_r16__helper1 MeasObjectUTRA_FDD_r16__helper2 MeasObjectUTRA_FDD_r16__helper3.

Opaque MeasObjectUTRA_FDD_r16__cond MeasObjectUTRA_FDD_r16__Format.

