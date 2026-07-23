Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_MeasId_r16.

Opaque SL_MeasId_r16__cond SL_MeasId_r16__Format.

Require Import NR.SL_MeasObjectId_r16.

Opaque SL_MeasObjectId_r16__cond SL_MeasObjectId_r16__Format.

Require Import NR.SL_ReportConfigId_r16.

Opaque SL_ReportConfigId_r16__cond SL_ReportConfigId_r16__Format.

Record SL_MeasIdInfo_r16__Type : Set :=
  make__SL_MeasIdInfo_r16__Type {
    SL_MeasIdInfo_r16__sl_MeasId_r16 : SL_MeasId_r16__Type ;
    SL_MeasIdInfo_r16__sl_MeasObjectId_r16 : SL_MeasObjectId_r16__Type ;
    SL_MeasIdInfo_r16__sl_ReportConfigId_r16 : SL_ReportConfigId_r16__Type ;
}.
Definition SL_MeasIdInfo_r16__root_list : list seq_elem := (
 Nor SL_MeasId_r16__Type SL_MeasId_r16__cond ::
 Nor SL_MeasObjectId_r16__Type SL_MeasObjectId_r16__cond ::
 Nor SL_ReportConfigId_r16__Type SL_ReportConfigId_r16__cond ::
 nil).
Definition SL_MeasIdInfo_r16__ext_list : list typ := (
  nil).
Definition SL_MeasIdInfo_r16__cond (z : SL_MeasIdInfo_r16__Type) := 
(  SL_MeasId_r16__cond (SL_MeasIdInfo_r16__sl_MeasId_r16 z) /\
  SL_MeasObjectId_r16__cond (SL_MeasIdInfo_r16__sl_MeasObjectId_r16 z) /\
  SL_ReportConfigId_r16__cond (SL_MeasIdInfo_r16__sl_ReportConfigId_r16 z) /\
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

Definition SL_MeasIdInfo_r16__root_Format_Type := Eval cbn in seq_format_prod SL_MeasIdInfo_r16__root_list.
Definition SL_MeasIdInfo_r16__root_Format_list : SL_MeasIdInfo_r16__root_Format_Type :=
  (SL_MeasId_r16__Format, (SL_MeasObjectId_r16__Format, (SL_ReportConfigId_r16__Format, unit_format))).

Definition SL_MeasIdInfo_r16__ext_Format_Type := Eval cbn in get_formats SL_MeasIdInfo_r16__ext_list.
Definition SL_MeasIdInfo_r16__ext_Format_list : SL_MeasIdInfo_r16__ext_Format_Type :=
  unit__Format.

Definition SL_MeasIdInfo_r16__list_type : Set := (seq_type SL_MeasIdInfo_r16__root_list) * (seq_ext_type SL_MeasIdInfo_r16__ext_list).
Definition SL_MeasIdInfo_r16__list_cond (z : SL_MeasIdInfo_r16__list_type) : Prop :=
        (seq_cond SL_MeasIdInfo_r16__root_list (fst z)) /\ (seq_ext_cond SL_MeasIdInfo_r16__ext_list (snd z)).
Definition SL_MeasIdInfo_r16__list_format : T_Format SL_MeasIdInfo_r16__list_type SL_MeasIdInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_MeasIdInfo_r16__root_list SL_MeasIdInfo_r16__root_Format_list SL_MeasIdInfo_r16__ext_list SL_MeasIdInfo_r16__ext_Format_list.

Opaque SL_MeasIdInfo_r16__list_format.
Definition SL_MeasIdInfo_r16__F1 (z : SL_MeasIdInfo_r16__Type) : SL_MeasIdInfo_r16__list_type :=
  (((SL_MeasIdInfo_r16__sl_MeasId_r16 z, (SL_MeasIdInfo_r16__sl_MeasObjectId_r16 z, (SL_MeasIdInfo_r16__sl_ReportConfigId_r16 z, tt)))), (
tt)).
Definition SL_MeasIdInfo_r16__F2 (y : SL_MeasIdInfo_r16__list_type) : SL_MeasIdInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__SL_MeasIdInfo_r16__Type j0 j1 j2
  end.
Definition SL_MeasIdInfo_r16__helper1 : (forall a : SL_MeasIdInfo_r16__Type, SL_MeasIdInfo_r16__cond a -> SL_MeasIdInfo_r16__list_cond (SL_MeasIdInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_MeasIdInfo_r16__helper2 : (forall a : SL_MeasIdInfo_r16__Type, SL_MeasIdInfo_r16__F2 (SL_MeasIdInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_MeasIdInfo_r16__helper3 : (forall b : SL_MeasIdInfo_r16__list_type, SL_MeasIdInfo_r16__list_cond b -> SL_MeasIdInfo_r16__cond (SL_MeasIdInfo_r16__F2 b) /\ SL_MeasIdInfo_r16__F1 (SL_MeasIdInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_MeasIdInfo_r16__cond, SL_MeasIdInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_MeasIdInfo_r16__Format : T_Format SL_MeasIdInfo_r16__Type SL_MeasIdInfo_r16__cond :=
 proj2_format SL_MeasIdInfo_r16__cond SL_MeasIdInfo_r16__list_format  SL_MeasIdInfo_r16__F1 SL_MeasIdInfo_r16__F2 SL_MeasIdInfo_r16__helper1 SL_MeasIdInfo_r16__helper2 SL_MeasIdInfo_r16__helper3.

Opaque SL_MeasIdInfo_r16__cond SL_MeasIdInfo_r16__Format.

