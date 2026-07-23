Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasResultFailedCell_r16.

Opaque MeasResultFailedCell_r16__cond MeasResultFailedCell_r16__Format.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Require Import NR.MeasResultList2NR_r16.

Opaque MeasResultList2NR_r16__cond MeasResultList2NR_r16__Format.

Require Import NR.MeasResultList2EUTRA_r16.

Opaque MeasResultList2EUTRA_r16__cond MeasResultList2EUTRA_r16__Format.

Record ConnEstFailReport_r16__measResultNeighCells_r16__Type : Set :=
  make__ConnEstFailReport_r16__measResultNeighCells_r16__Type {
    ConnEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListNR : option MeasResultList2NR_r16__Type ;
    ConnEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA : option MeasResultList2EUTRA_r16__Type ;
}.
Definition ConnEstFailReport_r16__measResultNeighCells_r16__list := (
 Opt MeasResultList2NR_r16__Type MeasResultList2NR_r16__cond ::
 Opt MeasResultList2EUTRA_r16__Type MeasResultList2EUTRA_r16__cond ::
 nil).
Definition ConnEstFailReport_r16__measResultNeighCells_r16__cond z := 
  opt_cond MeasResultList2NR_r16__cond (ConnEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListNR z) /\
  opt_cond MeasResultList2EUTRA_r16__cond (ConnEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA z) /\
  True.

Lemma ConnEstFailReport_r16__numberOfConnFail_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma ConnEstFailReport_r16__numberOfConnFail_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConnEstFailReport_r16__numberOfConnFail_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConnEstFailReport_r16__numberOfConnFail_r16__Type := Z.
Definition ConnEstFailReport_r16__numberOfConnFail_r16__cond := (fun z => (1 <= z <= 8)%Z).
Require Import NR.PerRAInfoList_r16.

Opaque PerRAInfoList_r16__cond PerRAInfoList_r16__Format.

Require Import NR.TimeSinceFailure_r16.

Opaque TimeSinceFailure_r16__cond TimeSinceFailure_r16__Format.

Record ConnEstFailReport_r16__Type : Set :=
  make__ConnEstFailReport_r16__Type {
    ConnEstFailReport_r16__measResultFailedCell_r16 : MeasResultFailedCell_r16__Type ;
    ConnEstFailReport_r16__locationInfo_r16 : option LocationInfo_r16__Type ;
    ConnEstFailReport_r16__measResultNeighCells_r16 : ConnEstFailReport_r16__measResultNeighCells_r16__Type ;
    ConnEstFailReport_r16__numberOfConnFail_r16 : Z ;
    ConnEstFailReport_r16__perRAInfoList_r16 : PerRAInfoList_r16__Type ;
    ConnEstFailReport_r16__timeSinceFailure_r16 : TimeSinceFailure_r16__Type ;
}.
Definition ConnEstFailReport_r16__root_list : list seq_elem := (
 Nor MeasResultFailedCell_r16__Type MeasResultFailedCell_r16__cond ::
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 Nor ConnEstFailReport_r16__measResultNeighCells_r16__Type ConnEstFailReport_r16__measResultNeighCells_r16__cond ::
 Nor Z ConnEstFailReport_r16__numberOfConnFail_r16__cond ::
 Nor PerRAInfoList_r16__Type PerRAInfoList_r16__cond ::
 Nor TimeSinceFailure_r16__Type TimeSinceFailure_r16__cond ::
 nil).
Definition ConnEstFailReport_r16__ext_list : list typ := (
  nil).
Definition ConnEstFailReport_r16__cond (z : ConnEstFailReport_r16__Type) := 
(  MeasResultFailedCell_r16__cond (ConnEstFailReport_r16__measResultFailedCell_r16 z) /\
  opt_cond LocationInfo_r16__cond (ConnEstFailReport_r16__locationInfo_r16 z) /\
  ConnEstFailReport_r16__measResultNeighCells_r16__cond (ConnEstFailReport_r16__measResultNeighCells_r16 z) /\
  ConnEstFailReport_r16__numberOfConnFail_r16__cond (ConnEstFailReport_r16__numberOfConnFail_r16 z) /\
  PerRAInfoList_r16__cond (ConnEstFailReport_r16__perRAInfoList_r16 z) /\
  TimeSinceFailure_r16__cond (ConnEstFailReport_r16__timeSinceFailure_r16 z) /\
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

Definition ConnEstFailReport_r16__measResultNeighCells_r16__Format_Type := Eval cbn in seq_format_prod ConnEstFailReport_r16__measResultNeighCells_r16__list.
Definition ConnEstFailReport_r16__measResultNeighCells_r16__Format_list : ConnEstFailReport_r16__measResultNeighCells_r16__Format_Type :=
  (MeasResultList2NR_r16__Format, (MeasResultList2EUTRA_r16__Format, unit_format)).
Definition ConnEstFailReport_r16__measResultNeighCells_r16__list__Format := (*Eval compute in *) seq_format ConnEstFailReport_r16__measResultNeighCells_r16__list ConnEstFailReport_r16__measResultNeighCells_r16__Format_list.
Definition ConnEstFailReport_r16__measResultNeighCells_r16__F1 z :=
  (ConnEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListNR z, (ConnEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA z, tt)).
Definition ConnEstFailReport_r16__measResultNeighCells_r16__F2 (y : seq_type ConnEstFailReport_r16__measResultNeighCells_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ConnEstFailReport_r16__measResultNeighCells_r16__Type i0 i1
  end.
Lemma ConnEstFailReport_r16__measResultNeighCells_r16__F1F2_cond (z : ConnEstFailReport_r16__measResultNeighCells_r16__Type)
  : ConnEstFailReport_r16__measResultNeighCells_r16__cond z ->
  (seq_cond ConnEstFailReport_r16__measResultNeighCells_r16__list (ConnEstFailReport_r16__measResultNeighCells_r16__F1 z)).
intro H. unfold ConnEstFailReport_r16__measResultNeighCells_r16__cond in H. simpl. auto. Qed.
Lemma ConnEstFailReport_r16__measResultNeighCells_r16__F1F2_cond2 (z : ConnEstFailReport_r16__measResultNeighCells_r16__Type)
 : ConnEstFailReport_r16__measResultNeighCells_r16__F2 (ConnEstFailReport_r16__measResultNeighCells_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConnEstFailReport_r16__measResultNeighCells_r16__F2F1_cond (y : seq_type ConnEstFailReport_r16__measResultNeighCells_r16__list)
  : seq_cond ConnEstFailReport_r16__measResultNeighCells_r16__list y ->
 (ConnEstFailReport_r16__measResultNeighCells_r16__cond (ConnEstFailReport_r16__measResultNeighCells_r16__F2 y)) /\  ConnEstFailReport_r16__measResultNeighCells_r16__F1 (ConnEstFailReport_r16__measResultNeighCells_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConnEstFailReport_r16__measResultNeighCells_r16__cond. simpl in *. auto.
 - simpl. unfold ConnEstFailReport_r16__measResultNeighCells_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConnEstFailReport_r16__measResultNeighCells_r16__Format : T_Format ConnEstFailReport_r16__measResultNeighCells_r16__Type ConnEstFailReport_r16__measResultNeighCells_r16__cond :=
        proj2_format  ConnEstFailReport_r16__measResultNeighCells_r16__cond ConnEstFailReport_r16__measResultNeighCells_r16__list__Format
    ConnEstFailReport_r16__measResultNeighCells_r16__F1 ConnEstFailReport_r16__measResultNeighCells_r16__F2 ConnEstFailReport_r16__measResultNeighCells_r16__F1F2_cond  ConnEstFailReport_r16__measResultNeighCells_r16__F1F2_cond2 ConnEstFailReport_r16__measResultNeighCells_r16__F2F1_cond.
Opaque ConnEstFailReport_r16__measResultNeighCells_r16__cond ConnEstFailReport_r16__measResultNeighCells_r16__Format.

Definition ConnEstFailReport_r16__numberOfConnFail_r16__Format : T_Format Z ConnEstFailReport_r16__numberOfConnFail_r16__cond :=
 ranged_int_format (1) (8) ConnEstFailReport_r16__numberOfConnFail_r16__helper1 ConnEstFailReport_r16__numberOfConnFail_r16__helper2.

Opaque ConnEstFailReport_r16__numberOfConnFail_r16__cond ConnEstFailReport_r16__numberOfConnFail_r16__Format.


Definition ConnEstFailReport_r16__root_Format_Type := Eval cbn in seq_format_prod ConnEstFailReport_r16__root_list.
Definition ConnEstFailReport_r16__root_Format_list : ConnEstFailReport_r16__root_Format_Type :=
  (MeasResultFailedCell_r16__Format, (LocationInfo_r16__Format, (ConnEstFailReport_r16__measResultNeighCells_r16__Format, (ConnEstFailReport_r16__numberOfConnFail_r16__Format, (PerRAInfoList_r16__Format, (TimeSinceFailure_r16__Format, unit_format)))))).

Definition ConnEstFailReport_r16__ext_Format_Type := Eval cbn in get_formats ConnEstFailReport_r16__ext_list.
Definition ConnEstFailReport_r16__ext_Format_list : ConnEstFailReport_r16__ext_Format_Type :=
  unit__Format.

Definition ConnEstFailReport_r16__list_type : Set := (seq_type ConnEstFailReport_r16__root_list) * (seq_ext_type ConnEstFailReport_r16__ext_list).
Definition ConnEstFailReport_r16__list_cond (z : ConnEstFailReport_r16__list_type) : Prop :=
        (seq_cond ConnEstFailReport_r16__root_list (fst z)) /\ (seq_ext_cond ConnEstFailReport_r16__ext_list (snd z)).
Definition ConnEstFailReport_r16__list_format : T_Format ConnEstFailReport_r16__list_type ConnEstFailReport_r16__list_cond :=
 (* Eval compute in *) seq_ext_format ConnEstFailReport_r16__root_list ConnEstFailReport_r16__root_Format_list ConnEstFailReport_r16__ext_list ConnEstFailReport_r16__ext_Format_list.

Opaque ConnEstFailReport_r16__list_format.
Definition ConnEstFailReport_r16__F1 (z : ConnEstFailReport_r16__Type) : ConnEstFailReport_r16__list_type :=
  (((ConnEstFailReport_r16__measResultFailedCell_r16 z, (ConnEstFailReport_r16__locationInfo_r16 z, (ConnEstFailReport_r16__measResultNeighCells_r16 z, (ConnEstFailReport_r16__numberOfConnFail_r16 z, (ConnEstFailReport_r16__perRAInfoList_r16 z, (ConnEstFailReport_r16__timeSinceFailure_r16 z, tt))))))), (
tt)).
Definition ConnEstFailReport_r16__F2 (y : ConnEstFailReport_r16__list_type) : ConnEstFailReport_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__ConnEstFailReport_r16__Type j0 j1 j2 j3 j4 j5
  end.
Definition ConnEstFailReport_r16__helper1 : (forall a : ConnEstFailReport_r16__Type, ConnEstFailReport_r16__cond a -> ConnEstFailReport_r16__list_cond (ConnEstFailReport_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ConnEstFailReport_r16__helper2 : (forall a : ConnEstFailReport_r16__Type, ConnEstFailReport_r16__F2 (ConnEstFailReport_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ConnEstFailReport_r16__helper3 : (forall b : ConnEstFailReport_r16__list_type, ConnEstFailReport_r16__list_cond b -> ConnEstFailReport_r16__cond (ConnEstFailReport_r16__F2 b) /\ ConnEstFailReport_r16__F1 (ConnEstFailReport_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ConnEstFailReport_r16__cond, ConnEstFailReport_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ConnEstFailReport_r16__Format : T_Format ConnEstFailReport_r16__Type ConnEstFailReport_r16__cond :=
 proj2_format ConnEstFailReport_r16__cond ConnEstFailReport_r16__list_format  ConnEstFailReport_r16__F1 ConnEstFailReport_r16__F2 ConnEstFailReport_r16__helper1 ConnEstFailReport_r16__helper2 ConnEstFailReport_r16__helper3.

Opaque ConnEstFailReport_r16__cond ConnEstFailReport_r16__Format.

