Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.MeasResultsPerCellIdleNR_r16.

Opaque MeasResultsPerCellIdleNR_r16__cond MeasResultsPerCellIdleNR_r16__Format.

Definition MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type := list MeasResultsPerCellIdleNR_r16__Type.

Lemma MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__helper1 : (0 <= 1 <= maxCellMeasIdle_r16)%Z. unfold maxCellMeasIdle_r16.
 lia. Qed.
Lemma MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__helper2 : to_bit_sz (Z.to_nat (maxCellMeasIdle_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellMeasIdle_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__cond (z : MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxCellMeasIdle_r16)%Z /\ (list_and MeasResultsPerCellIdleNR_r16__cond z) .

Record MeasResultsPerCarrierIdleNR_r16__Type : Set :=
  make__MeasResultsPerCarrierIdleNR_r16__Type {
    MeasResultsPerCarrierIdleNR_r16__carrierFreq_r16 : ARFCN_ValueNR__Type ;
    MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16 : MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type ;
}.
Definition MeasResultsPerCarrierIdleNR_r16__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__cond ::
 nil).
Definition MeasResultsPerCarrierIdleNR_r16__ext_list : list typ := (
  nil).
Definition MeasResultsPerCarrierIdleNR_r16__cond (z : MeasResultsPerCarrierIdleNR_r16__Type) := 
(  ARFCN_ValueNR__cond (MeasResultsPerCarrierIdleNR_r16__carrierFreq_r16 z) /\
  MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__cond (MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16 z) /\
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
Definition MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Format : T_Format MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__cond := seq_of_format MeasResultsPerCellIdleNR_r16__Format 1 maxCellMeasIdle_r16 MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__helper1 MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__helper2.

Opaque MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__cond MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Format.


Definition MeasResultsPerCarrierIdleNR_r16__root_Format_Type := Eval cbn in seq_format_prod MeasResultsPerCarrierIdleNR_r16__root_list.
Definition MeasResultsPerCarrierIdleNR_r16__root_Format_list : MeasResultsPerCarrierIdleNR_r16__root_Format_Type :=
  (ARFCN_ValueNR__Format, (MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Format, unit_format)).

Definition MeasResultsPerCarrierIdleNR_r16__ext_Format_Type := Eval cbn in get_formats MeasResultsPerCarrierIdleNR_r16__ext_list.
Definition MeasResultsPerCarrierIdleNR_r16__ext_Format_list : MeasResultsPerCarrierIdleNR_r16__ext_Format_Type :=
  unit__Format.

Definition MeasResultsPerCarrierIdleNR_r16__list_type : Set := (seq_type MeasResultsPerCarrierIdleNR_r16__root_list) * (seq_ext_type MeasResultsPerCarrierIdleNR_r16__ext_list).
Definition MeasResultsPerCarrierIdleNR_r16__list_cond (z : MeasResultsPerCarrierIdleNR_r16__list_type) : Prop :=
        (seq_cond MeasResultsPerCarrierIdleNR_r16__root_list (fst z)) /\ (seq_ext_cond MeasResultsPerCarrierIdleNR_r16__ext_list (snd z)).
Definition MeasResultsPerCarrierIdleNR_r16__list_format : T_Format MeasResultsPerCarrierIdleNR_r16__list_type MeasResultsPerCarrierIdleNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultsPerCarrierIdleNR_r16__root_list MeasResultsPerCarrierIdleNR_r16__root_Format_list MeasResultsPerCarrierIdleNR_r16__ext_list MeasResultsPerCarrierIdleNR_r16__ext_Format_list.

Opaque MeasResultsPerCarrierIdleNR_r16__list_format.
Definition MeasResultsPerCarrierIdleNR_r16__F1 (z : MeasResultsPerCarrierIdleNR_r16__Type) : MeasResultsPerCarrierIdleNR_r16__list_type :=
  (((MeasResultsPerCarrierIdleNR_r16__carrierFreq_r16 z, (MeasResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16 z, tt))), (
tt)).
Definition MeasResultsPerCarrierIdleNR_r16__F2 (y : MeasResultsPerCarrierIdleNR_r16__list_type) : MeasResultsPerCarrierIdleNR_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__MeasResultsPerCarrierIdleNR_r16__Type j0 j1
  end.
Definition MeasResultsPerCarrierIdleNR_r16__helper1 : (forall a : MeasResultsPerCarrierIdleNR_r16__Type, MeasResultsPerCarrierIdleNR_r16__cond a -> MeasResultsPerCarrierIdleNR_r16__list_cond (MeasResultsPerCarrierIdleNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultsPerCarrierIdleNR_r16__helper2 : (forall a : MeasResultsPerCarrierIdleNR_r16__Type, MeasResultsPerCarrierIdleNR_r16__F2 (MeasResultsPerCarrierIdleNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultsPerCarrierIdleNR_r16__helper3 : (forall b : MeasResultsPerCarrierIdleNR_r16__list_type, MeasResultsPerCarrierIdleNR_r16__list_cond b -> MeasResultsPerCarrierIdleNR_r16__cond (MeasResultsPerCarrierIdleNR_r16__F2 b) /\ MeasResultsPerCarrierIdleNR_r16__F1 (MeasResultsPerCarrierIdleNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultsPerCarrierIdleNR_r16__cond, MeasResultsPerCarrierIdleNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultsPerCarrierIdleNR_r16__Format : T_Format MeasResultsPerCarrierIdleNR_r16__Type MeasResultsPerCarrierIdleNR_r16__cond :=
 proj2_format MeasResultsPerCarrierIdleNR_r16__cond MeasResultsPerCarrierIdleNR_r16__list_format  MeasResultsPerCarrierIdleNR_r16__F1 MeasResultsPerCarrierIdleNR_r16__F2 MeasResultsPerCarrierIdleNR_r16__helper1 MeasResultsPerCarrierIdleNR_r16__helper2 MeasResultsPerCarrierIdleNR_r16__helper3.

Opaque MeasResultsPerCarrierIdleNR_r16__cond MeasResultsPerCarrierIdleNR_r16__Format.

