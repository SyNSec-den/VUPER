Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SLRB_PC5_ConfigIndex_r16.

Opaque SLRB_PC5_ConfigIndex_r16__cond SLRB_PC5_ConfigIndex_r16__Format.

Require Import NR.SL_SDAP_ConfigPC5_r16.

Opaque SL_SDAP_ConfigPC5_r16__cond SL_SDAP_ConfigPC5_r16__Format.

Require Import NR.SL_PDCP_ConfigPC5_r16.

Opaque SL_PDCP_ConfigPC5_r16__cond SL_PDCP_ConfigPC5_r16__Format.

Require Import NR.SL_RLC_ConfigPC5_r16.

Opaque SL_RLC_ConfigPC5_r16__cond SL_RLC_ConfigPC5_r16__Format.

Require Import NR.SL_LogicalChannelConfigPC5_r16.

Opaque SL_LogicalChannelConfigPC5_r16__cond SL_LogicalChannelConfigPC5_r16__Format.

Record SLRB_Config_r16__Type : Set :=
  make__SLRB_Config_r16__Type {
    SLRB_Config_r16__slrb_PC5_ConfigIndex_r16 : SLRB_PC5_ConfigIndex_r16__Type ;
    SLRB_Config_r16__sl_SDAP_ConfigPC5_r16 : option SL_SDAP_ConfigPC5_r16__Type ;
    SLRB_Config_r16__sl_PDCP_ConfigPC5_r16 : option SL_PDCP_ConfigPC5_r16__Type ;
    SLRB_Config_r16__sl_RLC_ConfigPC5_r16 : option SL_RLC_ConfigPC5_r16__Type ;
    SLRB_Config_r16__sl_MAC_LogicalChannelConfigPC5_r16 : option SL_LogicalChannelConfigPC5_r16__Type ;
}.
Definition SLRB_Config_r16__root_list : list seq_elem := (
 Nor SLRB_PC5_ConfigIndex_r16__Type SLRB_PC5_ConfigIndex_r16__cond ::
 Opt SL_SDAP_ConfigPC5_r16__Type SL_SDAP_ConfigPC5_r16__cond ::
 Opt SL_PDCP_ConfigPC5_r16__Type SL_PDCP_ConfigPC5_r16__cond ::
 Opt SL_RLC_ConfigPC5_r16__Type SL_RLC_ConfigPC5_r16__cond ::
 Opt SL_LogicalChannelConfigPC5_r16__Type SL_LogicalChannelConfigPC5_r16__cond ::
 nil).
Definition SLRB_Config_r16__ext_list : list typ := (
  nil).
Definition SLRB_Config_r16__cond (z : SLRB_Config_r16__Type) := 
(  SLRB_PC5_ConfigIndex_r16__cond (SLRB_Config_r16__slrb_PC5_ConfigIndex_r16 z) /\
  opt_cond SL_SDAP_ConfigPC5_r16__cond (SLRB_Config_r16__sl_SDAP_ConfigPC5_r16 z) /\
  opt_cond SL_PDCP_ConfigPC5_r16__cond (SLRB_Config_r16__sl_PDCP_ConfigPC5_r16 z) /\
  opt_cond SL_RLC_ConfigPC5_r16__cond (SLRB_Config_r16__sl_RLC_ConfigPC5_r16 z) /\
  opt_cond SL_LogicalChannelConfigPC5_r16__cond (SLRB_Config_r16__sl_MAC_LogicalChannelConfigPC5_r16 z) /\
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

Definition SLRB_Config_r16__root_Format_Type := Eval cbn in seq_format_prod SLRB_Config_r16__root_list.
Definition SLRB_Config_r16__root_Format_list : SLRB_Config_r16__root_Format_Type :=
  (SLRB_PC5_ConfigIndex_r16__Format, (SL_SDAP_ConfigPC5_r16__Format, (SL_PDCP_ConfigPC5_r16__Format, (SL_RLC_ConfigPC5_r16__Format, (SL_LogicalChannelConfigPC5_r16__Format, unit_format))))).

Definition SLRB_Config_r16__ext_Format_Type := Eval cbn in get_formats SLRB_Config_r16__ext_list.
Definition SLRB_Config_r16__ext_Format_list : SLRB_Config_r16__ext_Format_Type :=
  unit__Format.

Definition SLRB_Config_r16__list_type : Set := (seq_type SLRB_Config_r16__root_list) * (seq_ext_type SLRB_Config_r16__ext_list).
Definition SLRB_Config_r16__list_cond (z : SLRB_Config_r16__list_type) : Prop :=
        (seq_cond SLRB_Config_r16__root_list (fst z)) /\ (seq_ext_cond SLRB_Config_r16__ext_list (snd z)).
Definition SLRB_Config_r16__list_format : T_Format SLRB_Config_r16__list_type SLRB_Config_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SLRB_Config_r16__root_list SLRB_Config_r16__root_Format_list SLRB_Config_r16__ext_list SLRB_Config_r16__ext_Format_list.

Opaque SLRB_Config_r16__list_format.
Definition SLRB_Config_r16__F1 (z : SLRB_Config_r16__Type) : SLRB_Config_r16__list_type :=
  (((SLRB_Config_r16__slrb_PC5_ConfigIndex_r16 z, (SLRB_Config_r16__sl_SDAP_ConfigPC5_r16 z, (SLRB_Config_r16__sl_PDCP_ConfigPC5_r16 z, (SLRB_Config_r16__sl_RLC_ConfigPC5_r16 z, (SLRB_Config_r16__sl_MAC_LogicalChannelConfigPC5_r16 z, tt)))))), (
tt)).
Definition SLRB_Config_r16__F2 (y : SLRB_Config_r16__list_type) : SLRB_Config_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__SLRB_Config_r16__Type j0 j1 j2 j3 j4
  end.
Definition SLRB_Config_r16__helper1 : (forall a : SLRB_Config_r16__Type, SLRB_Config_r16__cond a -> SLRB_Config_r16__list_cond (SLRB_Config_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SLRB_Config_r16__helper2 : (forall a : SLRB_Config_r16__Type, SLRB_Config_r16__F2 (SLRB_Config_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SLRB_Config_r16__helper3 : (forall b : SLRB_Config_r16__list_type, SLRB_Config_r16__list_cond b -> SLRB_Config_r16__cond (SLRB_Config_r16__F2 b) /\ SLRB_Config_r16__F1 (SLRB_Config_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SLRB_Config_r16__cond, SLRB_Config_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SLRB_Config_r16__Format : T_Format SLRB_Config_r16__Type SLRB_Config_r16__cond :=
 proj2_format SLRB_Config_r16__cond SLRB_Config_r16__list_format  SLRB_Config_r16__F1 SLRB_Config_r16__F2 SLRB_Config_r16__helper1 SLRB_Config_r16__helper2 SLRB_Config_r16__helper3.

Opaque SLRB_Config_r16__cond SLRB_Config_r16__Format.

