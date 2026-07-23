Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RACH_ConfigCommon.

Opaque RACH_ConfigCommon__cond RACH_ConfigCommon__Format.

Require Import NR.MsgA_ConfigCommon_r16.

Opaque MsgA_ConfigCommon_r16__cond MsgA_ConfigCommon_r16__Format.

Record AdditionalRACH_Config_r17__Type : Set :=
  make__AdditionalRACH_Config_r17__Type {
    AdditionalRACH_Config_r17__rach_ConfigCommon_r17 : option RACH_ConfigCommon__Type ;
    AdditionalRACH_Config_r17__msgA_ConfigCommon_r17 : option MsgA_ConfigCommon_r16__Type ;
}.
Definition AdditionalRACH_Config_r17__root_list : list seq_elem := (
 Opt RACH_ConfigCommon__Type RACH_ConfigCommon__cond ::
 Opt MsgA_ConfigCommon_r16__Type MsgA_ConfigCommon_r16__cond ::
 nil).
Definition AdditionalRACH_Config_r17__ext_list : list typ := (
  nil).
Definition AdditionalRACH_Config_r17__cond (z : AdditionalRACH_Config_r17__Type) := 
(  opt_cond RACH_ConfigCommon__cond (AdditionalRACH_Config_r17__rach_ConfigCommon_r17 z) /\
  opt_cond MsgA_ConfigCommon_r16__cond (AdditionalRACH_Config_r17__msgA_ConfigCommon_r17 z) /\
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

Definition AdditionalRACH_Config_r17__root_Format_Type := Eval cbn in seq_format_prod AdditionalRACH_Config_r17__root_list.
Definition AdditionalRACH_Config_r17__root_Format_list : AdditionalRACH_Config_r17__root_Format_Type :=
  (RACH_ConfigCommon__Format, (MsgA_ConfigCommon_r16__Format, unit_format)).

Definition AdditionalRACH_Config_r17__ext_Format_Type := Eval cbn in get_formats AdditionalRACH_Config_r17__ext_list.
Definition AdditionalRACH_Config_r17__ext_Format_list : AdditionalRACH_Config_r17__ext_Format_Type :=
  unit__Format.

Definition AdditionalRACH_Config_r17__list_type : Set := (seq_type AdditionalRACH_Config_r17__root_list) * (seq_ext_type AdditionalRACH_Config_r17__ext_list).
Definition AdditionalRACH_Config_r17__list_cond (z : AdditionalRACH_Config_r17__list_type) : Prop :=
        (seq_cond AdditionalRACH_Config_r17__root_list (fst z)) /\ (seq_ext_cond AdditionalRACH_Config_r17__ext_list (snd z)).
Definition AdditionalRACH_Config_r17__list_format : T_Format AdditionalRACH_Config_r17__list_type AdditionalRACH_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format AdditionalRACH_Config_r17__root_list AdditionalRACH_Config_r17__root_Format_list AdditionalRACH_Config_r17__ext_list AdditionalRACH_Config_r17__ext_Format_list.

Opaque AdditionalRACH_Config_r17__list_format.
Definition AdditionalRACH_Config_r17__F1 (z : AdditionalRACH_Config_r17__Type) : AdditionalRACH_Config_r17__list_type :=
  (((AdditionalRACH_Config_r17__rach_ConfigCommon_r17 z, (AdditionalRACH_Config_r17__msgA_ConfigCommon_r17 z, tt))), (
tt)).
Definition AdditionalRACH_Config_r17__F2 (y : AdditionalRACH_Config_r17__list_type) : AdditionalRACH_Config_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__AdditionalRACH_Config_r17__Type j0 j1
  end.
Definition AdditionalRACH_Config_r17__helper1 : (forall a : AdditionalRACH_Config_r17__Type, AdditionalRACH_Config_r17__cond a -> AdditionalRACH_Config_r17__list_cond (AdditionalRACH_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition AdditionalRACH_Config_r17__helper2 : (forall a : AdditionalRACH_Config_r17__Type, AdditionalRACH_Config_r17__F2 (AdditionalRACH_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition AdditionalRACH_Config_r17__helper3 : (forall b : AdditionalRACH_Config_r17__list_type, AdditionalRACH_Config_r17__list_cond b -> AdditionalRACH_Config_r17__cond (AdditionalRACH_Config_r17__F2 b) /\ AdditionalRACH_Config_r17__F1 (AdditionalRACH_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold AdditionalRACH_Config_r17__cond, AdditionalRACH_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition AdditionalRACH_Config_r17__Format : T_Format AdditionalRACH_Config_r17__Type AdditionalRACH_Config_r17__cond :=
 proj2_format AdditionalRACH_Config_r17__cond AdditionalRACH_Config_r17__list_format  AdditionalRACH_Config_r17__F1 AdditionalRACH_Config_r17__F2 AdditionalRACH_Config_r17__helper1 AdditionalRACH_Config_r17__helper2 AdditionalRACH_Config_r17__helper3.

Opaque AdditionalRACH_Config_r17__cond AdditionalRACH_Config_r17__Format.

