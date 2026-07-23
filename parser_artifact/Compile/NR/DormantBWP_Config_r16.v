Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.SetupRelease.
Require Import NR.WithinActiveTimeConfig_r16.
Definition DormantBWP_Config_r16__withinActiveTimeConfig_r16__Type := SetupRelease__Type WithinActiveTimeConfig_r16__Type.
Definition DormantBWP_Config_r16__withinActiveTimeConfig_r16__cond := SetupRelease__cond _ WithinActiveTimeConfig_r16__cond.
Definition DormantBWP_Config_r16__withinActiveTimeConfig_r16__Format : T_Format DormantBWP_Config_r16__withinActiveTimeConfig_r16__Type DormantBWP_Config_r16__withinActiveTimeConfig_r16__cond := SetupRelease__Format _ _ WithinActiveTimeConfig_r16__Format.
Opaque DormantBWP_Config_r16__withinActiveTimeConfig_r16__cond DormantBWP_Config_r16__withinActiveTimeConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.OutsideActiveTimeConfig_r16.
Definition DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Type := SetupRelease__Type OutsideActiveTimeConfig_r16__Type.
Definition DormantBWP_Config_r16__outsideActiveTimeConfig_r16__cond := SetupRelease__cond _ OutsideActiveTimeConfig_r16__cond.
Definition DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Format : T_Format DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Type DormantBWP_Config_r16__outsideActiveTimeConfig_r16__cond := SetupRelease__Format _ _ OutsideActiveTimeConfig_r16__Format.
Opaque DormantBWP_Config_r16__outsideActiveTimeConfig_r16__cond DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Format.

Record DormantBWP_Config_r16__Type : Set :=
  make__DormantBWP_Config_r16__Type {
    DormantBWP_Config_r16__dormantBWP_Id_r16 : option BWP_Id__Type ;
    DormantBWP_Config_r16__withinActiveTimeConfig_r16 : option DormantBWP_Config_r16__withinActiveTimeConfig_r16__Type ;
    DormantBWP_Config_r16__outsideActiveTimeConfig_r16 : option DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Type ;
}.
Definition DormantBWP_Config_r16__list := (
 Opt BWP_Id__Type BWP_Id__cond ::
 Opt DormantBWP_Config_r16__withinActiveTimeConfig_r16__Type DormantBWP_Config_r16__withinActiveTimeConfig_r16__cond ::
 Opt DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Type DormantBWP_Config_r16__outsideActiveTimeConfig_r16__cond ::
 nil).
Definition DormantBWP_Config_r16__cond z := 
  opt_cond BWP_Id__cond (DormantBWP_Config_r16__dormantBWP_Id_r16 z) /\
  opt_cond DormantBWP_Config_r16__withinActiveTimeConfig_r16__cond (DormantBWP_Config_r16__withinActiveTimeConfig_r16 z) /\
  opt_cond DormantBWP_Config_r16__outsideActiveTimeConfig_r16__cond (DormantBWP_Config_r16__outsideActiveTimeConfig_r16 z) /\
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
Opaque DormantBWP_Config_r16__withinActiveTimeConfig_r16__cond DormantBWP_Config_r16__withinActiveTimeConfig_r16__Format.

Opaque DormantBWP_Config_r16__outsideActiveTimeConfig_r16__cond DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Format.


Definition DormantBWP_Config_r16__Format_Type := Eval cbn in seq_format_prod DormantBWP_Config_r16__list.
Definition DormantBWP_Config_r16__Format_list : DormantBWP_Config_r16__Format_Type :=
  (BWP_Id__Format, (DormantBWP_Config_r16__withinActiveTimeConfig_r16__Format, (DormantBWP_Config_r16__outsideActiveTimeConfig_r16__Format, unit_format))).
Definition DormantBWP_Config_r16__list__Format := (*Eval compute in *) seq_format DormantBWP_Config_r16__list DormantBWP_Config_r16__Format_list.
Definition DormantBWP_Config_r16__F1 z :=
  (DormantBWP_Config_r16__dormantBWP_Id_r16 z, (DormantBWP_Config_r16__withinActiveTimeConfig_r16 z, (DormantBWP_Config_r16__outsideActiveTimeConfig_r16 z, tt))).
Definition DormantBWP_Config_r16__F2 (y : seq_type DormantBWP_Config_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__DormantBWP_Config_r16__Type i0 i1 i2
  end.
Lemma DormantBWP_Config_r16__F1F2_cond (z : DormantBWP_Config_r16__Type)
  : DormantBWP_Config_r16__cond z ->
  (seq_cond DormantBWP_Config_r16__list (DormantBWP_Config_r16__F1 z)).
intro H. unfold DormantBWP_Config_r16__cond in H. simpl. auto. Qed.
Lemma DormantBWP_Config_r16__F1F2_cond2 (z : DormantBWP_Config_r16__Type)
 : DormantBWP_Config_r16__F2 (DormantBWP_Config_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DormantBWP_Config_r16__F2F1_cond (y : seq_type DormantBWP_Config_r16__list)
  : seq_cond DormantBWP_Config_r16__list y ->
 (DormantBWP_Config_r16__cond (DormantBWP_Config_r16__F2 y)) /\  DormantBWP_Config_r16__F1 (DormantBWP_Config_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DormantBWP_Config_r16__cond. simpl in *. auto.
 - simpl. unfold DormantBWP_Config_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DormantBWP_Config_r16__Format : T_Format DormantBWP_Config_r16__Type DormantBWP_Config_r16__cond :=
        proj2_format  DormantBWP_Config_r16__cond DormantBWP_Config_r16__list__Format
    DormantBWP_Config_r16__F1 DormantBWP_Config_r16__F2 DormantBWP_Config_r16__F1F2_cond  DormantBWP_Config_r16__F1F2_cond2 DormantBWP_Config_r16__F2F1_cond.
Opaque DormantBWP_Config_r16__cond DormantBWP_Config_r16__Format.

