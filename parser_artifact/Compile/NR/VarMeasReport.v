Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.MeasId.

Opaque MeasId__cond MeasId__Format.

Require Import NR.CellsTriggeredList.

Opaque CellsTriggeredList__cond CellsTriggeredList__Format.

Require Import NR.CLI_TriggeredList_r16.

Opaque CLI_TriggeredList_r16__cond CLI_TriggeredList_r16__Format.

Require Import NR.Tx_PoolMeasList_r16.

Opaque Tx_PoolMeasList_r16__cond Tx_PoolMeasList_r16__Format.

Require Import NR.RelaysTriggeredList_r17.

Opaque RelaysTriggeredList_r17__cond RelaysTriggeredList_r17__Format.

Record VarMeasReport__Type : Set :=
  make__VarMeasReport__Type {
    VarMeasReport__measId : MeasId__Type ;
    VarMeasReport__cellsTriggeredList : option CellsTriggeredList__Type ;
    VarMeasReport__numberOfReportsSent : Z ;
    VarMeasReport__cli_TriggeredList_r16 : option CLI_TriggeredList_r16__Type ;
    VarMeasReport__tx_PoolMeasToAddModListNR_r16 : option Tx_PoolMeasList_r16__Type ;
    VarMeasReport__relaysTriggeredList_r17 : option RelaysTriggeredList_r17__Type ;
}.
Definition VarMeasReport__list := (
 Nor MeasId__Type MeasId__cond ::
 Opt CellsTriggeredList__Type CellsTriggeredList__cond ::
 Nor Z (fun z : Z => (- Z.pow 2 47 <= z <= Z.pow 2 47 - 1)%Z) ::
 Opt CLI_TriggeredList_r16__Type CLI_TriggeredList_r16__cond ::
 Opt Tx_PoolMeasList_r16__Type Tx_PoolMeasList_r16__cond ::
 Opt RelaysTriggeredList_r17__Type RelaysTriggeredList_r17__cond ::
 nil).
Definition VarMeasReport__cond z := 
  MeasId__cond (VarMeasReport__measId z) /\
  opt_cond CellsTriggeredList__cond (VarMeasReport__cellsTriggeredList z) /\
  (fun z : Z => (- Z.pow 2 47 <= z <= Z.pow 2 47 - 1)%Z) (VarMeasReport__numberOfReportsSent z) /\
  opt_cond CLI_TriggeredList_r16__cond (VarMeasReport__cli_TriggeredList_r16 z) /\
  opt_cond Tx_PoolMeasList_r16__cond (VarMeasReport__tx_PoolMeasToAddModListNR_r16 z) /\
  opt_cond RelaysTriggeredList_r17__cond (VarMeasReport__relaysTriggeredList_r17 z) /\
  True.


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

Definition VarMeasReport__Format_Type := Eval cbn in seq_format_prod VarMeasReport__list.
Definition VarMeasReport__Format_list : VarMeasReport__Format_Type :=
  (MeasId__Format, (CellsTriggeredList__Format, (int__Format, (CLI_TriggeredList_r16__Format, (Tx_PoolMeasList_r16__Format, (RelaysTriggeredList_r17__Format, unit_format)))))).
Definition VarMeasReport__list__Format := (*Eval compute in *) seq_format VarMeasReport__list VarMeasReport__Format_list.
Definition VarMeasReport__F1 z :=
  (VarMeasReport__measId z, (VarMeasReport__cellsTriggeredList z, (VarMeasReport__numberOfReportsSent z, (VarMeasReport__cli_TriggeredList_r16 z, (VarMeasReport__tx_PoolMeasToAddModListNR_r16 z, (VarMeasReport__relaysTriggeredList_r17 z, tt)))))).
Definition VarMeasReport__F2 (y : seq_type VarMeasReport__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__VarMeasReport__Type i0 i1 i2 i3 i4 i5
  end.
Lemma VarMeasReport__F1F2_cond (z : VarMeasReport__Type)
  : VarMeasReport__cond z ->
  (seq_cond VarMeasReport__list (VarMeasReport__F1 z)).
intro H. unfold VarMeasReport__cond in H. simpl. auto. Qed.
Lemma VarMeasReport__F1F2_cond2 (z : VarMeasReport__Type)
 : VarMeasReport__F2 (VarMeasReport__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarMeasReport__F2F1_cond (y : seq_type VarMeasReport__list)
  : seq_cond VarMeasReport__list y ->
 (VarMeasReport__cond (VarMeasReport__F2 y)) /\  VarMeasReport__F1 (VarMeasReport__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarMeasReport__cond. simpl in *. auto.
 - simpl. unfold VarMeasReport__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarMeasReport__Format : T_Format VarMeasReport__Type VarMeasReport__cond :=
        proj2_format  VarMeasReport__cond VarMeasReport__list__Format
    VarMeasReport__F1 VarMeasReport__F2 VarMeasReport__F1F2_cond  VarMeasReport__F1F2_cond2 VarMeasReport__F2F1_cond.
Opaque VarMeasReport__cond VarMeasReport__Format.

