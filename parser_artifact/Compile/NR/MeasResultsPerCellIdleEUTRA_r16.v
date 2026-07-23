Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Require Import NR.RSRP_RangeEUTRA.

Opaque RSRP_RangeEUTRA__cond RSRP_RangeEUTRA__Format.

Require Import NR.RSRQ_RangeEUTRA_r16.

Opaque RSRQ_RangeEUTRA_r16__cond RSRQ_RangeEUTRA_r16__Format.

Record MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type : Set :=
  make__MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type {
    MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrp_ResultEUTRA_r16 : option RSRP_RangeEUTRA__Type ;
    MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrq_ResultEUTRA_r16 : option RSRQ_RangeEUTRA_r16__Type ;
}.
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list := (
 Opt RSRP_RangeEUTRA__Type RSRP_RangeEUTRA__cond ::
 Opt RSRQ_RangeEUTRA_r16__Type RSRQ_RangeEUTRA_r16__cond ::
 nil).
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond z := 
  opt_cond RSRP_RangeEUTRA__cond (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrp_ResultEUTRA_r16 z) /\
  opt_cond RSRQ_RangeEUTRA_r16__cond (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrq_ResultEUTRA_r16 z) /\
  True.

Record MeasResultsPerCellIdleEUTRA_r16__Type : Set :=
  make__MeasResultsPerCellIdleEUTRA_r16__Type {
    MeasResultsPerCellIdleEUTRA_r16__eutra_PhysCellId_r16 : EUTRA_PhysCellId__Type ;
    MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16 : MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type ;
}.
Definition MeasResultsPerCellIdleEUTRA_r16__root_list : list seq_elem := (
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Nor MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond ::
 nil).
Definition MeasResultsPerCellIdleEUTRA_r16__ext_list : list typ := (
  nil).
Definition MeasResultsPerCellIdleEUTRA_r16__cond (z : MeasResultsPerCellIdleEUTRA_r16__Type) := 
(  EUTRA_PhysCellId__cond (MeasResultsPerCellIdleEUTRA_r16__eutra_PhysCellId_r16 z) /\
  MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16 z) /\
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

Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_Type := Eval cbn in seq_format_prod MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list.
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_list : MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_Type :=
  (RSRP_RangeEUTRA__Format, (RSRQ_RangeEUTRA_r16__Format, unit_format)).
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list__Format := (*Eval compute in *) seq_format MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_list.
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1 z :=
  (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrp_ResultEUTRA_r16 z, (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrq_ResultEUTRA_r16 z, tt)).
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2 (y : seq_type MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type i0 i1
  end.
Lemma MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1F2_cond (z : MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type)
  : MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond z ->
  (seq_cond MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1 z)).
intro H. unfold MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1F2_cond2 (z : MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type)
 : MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2 (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2F1_cond (y : seq_type MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list)
  : seq_cond MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list y ->
 (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2 y)) /\  MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1 (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format : T_Format MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond :=
        proj2_format  MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list__Format
    MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1 MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2 MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1F2_cond  MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1F2_cond2 MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2F1_cond.
Opaque MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__cond MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format.


Definition MeasResultsPerCellIdleEUTRA_r16__root_Format_Type := Eval cbn in seq_format_prod MeasResultsPerCellIdleEUTRA_r16__root_list.
Definition MeasResultsPerCellIdleEUTRA_r16__root_Format_list : MeasResultsPerCellIdleEUTRA_r16__root_Format_Type :=
  (EUTRA_PhysCellId__Format, (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format, unit_format)).

Definition MeasResultsPerCellIdleEUTRA_r16__ext_Format_Type := Eval cbn in get_formats MeasResultsPerCellIdleEUTRA_r16__ext_list.
Definition MeasResultsPerCellIdleEUTRA_r16__ext_Format_list : MeasResultsPerCellIdleEUTRA_r16__ext_Format_Type :=
  unit__Format.

Definition MeasResultsPerCellIdleEUTRA_r16__list_type : Set := (seq_type MeasResultsPerCellIdleEUTRA_r16__root_list) * (seq_ext_type MeasResultsPerCellIdleEUTRA_r16__ext_list).
Definition MeasResultsPerCellIdleEUTRA_r16__list_cond (z : MeasResultsPerCellIdleEUTRA_r16__list_type) : Prop :=
        (seq_cond MeasResultsPerCellIdleEUTRA_r16__root_list (fst z)) /\ (seq_ext_cond MeasResultsPerCellIdleEUTRA_r16__ext_list (snd z)).
Definition MeasResultsPerCellIdleEUTRA_r16__list_format : T_Format MeasResultsPerCellIdleEUTRA_r16__list_type MeasResultsPerCellIdleEUTRA_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultsPerCellIdleEUTRA_r16__root_list MeasResultsPerCellIdleEUTRA_r16__root_Format_list MeasResultsPerCellIdleEUTRA_r16__ext_list MeasResultsPerCellIdleEUTRA_r16__ext_Format_list.

Opaque MeasResultsPerCellIdleEUTRA_r16__list_format.
Definition MeasResultsPerCellIdleEUTRA_r16__F1 (z : MeasResultsPerCellIdleEUTRA_r16__Type) : MeasResultsPerCellIdleEUTRA_r16__list_type :=
  (((MeasResultsPerCellIdleEUTRA_r16__eutra_PhysCellId_r16 z, (MeasResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16 z, tt))), (
tt)).
Definition MeasResultsPerCellIdleEUTRA_r16__F2 (y : MeasResultsPerCellIdleEUTRA_r16__list_type) : MeasResultsPerCellIdleEUTRA_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__MeasResultsPerCellIdleEUTRA_r16__Type j0 j1
  end.
Definition MeasResultsPerCellIdleEUTRA_r16__helper1 : (forall a : MeasResultsPerCellIdleEUTRA_r16__Type, MeasResultsPerCellIdleEUTRA_r16__cond a -> MeasResultsPerCellIdleEUTRA_r16__list_cond (MeasResultsPerCellIdleEUTRA_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultsPerCellIdleEUTRA_r16__helper2 : (forall a : MeasResultsPerCellIdleEUTRA_r16__Type, MeasResultsPerCellIdleEUTRA_r16__F2 (MeasResultsPerCellIdleEUTRA_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultsPerCellIdleEUTRA_r16__helper3 : (forall b : MeasResultsPerCellIdleEUTRA_r16__list_type, MeasResultsPerCellIdleEUTRA_r16__list_cond b -> MeasResultsPerCellIdleEUTRA_r16__cond (MeasResultsPerCellIdleEUTRA_r16__F2 b) /\ MeasResultsPerCellIdleEUTRA_r16__F1 (MeasResultsPerCellIdleEUTRA_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultsPerCellIdleEUTRA_r16__cond, MeasResultsPerCellIdleEUTRA_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultsPerCellIdleEUTRA_r16__Format : T_Format MeasResultsPerCellIdleEUTRA_r16__Type MeasResultsPerCellIdleEUTRA_r16__cond :=
 proj2_format MeasResultsPerCellIdleEUTRA_r16__cond MeasResultsPerCellIdleEUTRA_r16__list_format  MeasResultsPerCellIdleEUTRA_r16__F1 MeasResultsPerCellIdleEUTRA_r16__F2 MeasResultsPerCellIdleEUTRA_r16__helper1 MeasResultsPerCellIdleEUTRA_r16__helper2 MeasResultsPerCellIdleEUTRA_r16__helper3.

Opaque MeasResultsPerCellIdleEUTRA_r16__cond MeasResultsPerCellIdleEUTRA_r16__Format.

