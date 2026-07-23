Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.BWP_DownlinkCommon.

Opaque BWP_DownlinkCommon__cond BWP_DownlinkCommon__Format.

Require Import NR.BWP_DownlinkDedicated.

Opaque BWP_DownlinkDedicated__cond BWP_DownlinkDedicated__Format.

Record BWP_Downlink__Type : Set :=
  make__BWP_Downlink__Type {
    BWP_Downlink__bwp_Id : BWP_Id__Type ;
    BWP_Downlink__bwp_Common : option BWP_DownlinkCommon__Type ;
    BWP_Downlink__bwp_Dedicated : option BWP_DownlinkDedicated__Type ;
}.
Definition BWP_Downlink__root_list : list seq_elem := (
 Nor BWP_Id__Type BWP_Id__cond ::
 Opt BWP_DownlinkCommon__Type BWP_DownlinkCommon__cond ::
 Opt BWP_DownlinkDedicated__Type BWP_DownlinkDedicated__cond ::
 nil).
Definition BWP_Downlink__ext_list : list typ := (
  nil).
Definition BWP_Downlink__cond (z : BWP_Downlink__Type) := 
(  BWP_Id__cond (BWP_Downlink__bwp_Id z) /\
  opt_cond BWP_DownlinkCommon__cond (BWP_Downlink__bwp_Common z) /\
  opt_cond BWP_DownlinkDedicated__cond (BWP_Downlink__bwp_Dedicated z) /\
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

Definition BWP_Downlink__root_Format_Type := Eval cbn in seq_format_prod BWP_Downlink__root_list.
Definition BWP_Downlink__root_Format_list : BWP_Downlink__root_Format_Type :=
  (BWP_Id__Format, (BWP_DownlinkCommon__Format, (BWP_DownlinkDedicated__Format, unit_format))).

Definition BWP_Downlink__ext_Format_Type := Eval cbn in get_formats BWP_Downlink__ext_list.
Definition BWP_Downlink__ext_Format_list : BWP_Downlink__ext_Format_Type :=
  unit__Format.

Definition BWP_Downlink__list_type : Set := (seq_type BWP_Downlink__root_list) * (seq_ext_type BWP_Downlink__ext_list).
Definition BWP_Downlink__list_cond (z : BWP_Downlink__list_type) : Prop :=
        (seq_cond BWP_Downlink__root_list (fst z)) /\ (seq_ext_cond BWP_Downlink__ext_list (snd z)).
Definition BWP_Downlink__list_format : T_Format BWP_Downlink__list_type BWP_Downlink__list_cond :=
 (* Eval compute in *) seq_ext_format BWP_Downlink__root_list BWP_Downlink__root_Format_list BWP_Downlink__ext_list BWP_Downlink__ext_Format_list.

Opaque BWP_Downlink__list_format.
Definition BWP_Downlink__F1 (z : BWP_Downlink__Type) : BWP_Downlink__list_type :=
  (((BWP_Downlink__bwp_Id z, (BWP_Downlink__bwp_Common z, (BWP_Downlink__bwp_Dedicated z, tt)))), (
tt)).
Definition BWP_Downlink__F2 (y : BWP_Downlink__list_type) : BWP_Downlink__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__BWP_Downlink__Type j0 j1 j2
  end.
Definition BWP_Downlink__helper1 : (forall a : BWP_Downlink__Type, BWP_Downlink__cond a -> BWP_Downlink__list_cond (BWP_Downlink__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BWP_Downlink__helper2 : (forall a : BWP_Downlink__Type, BWP_Downlink__F2 (BWP_Downlink__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BWP_Downlink__helper3 : (forall b : BWP_Downlink__list_type, BWP_Downlink__list_cond b -> BWP_Downlink__cond (BWP_Downlink__F2 b) /\ BWP_Downlink__F1 (BWP_Downlink__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BWP_Downlink__cond, BWP_Downlink__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BWP_Downlink__Format : T_Format BWP_Downlink__Type BWP_Downlink__cond :=
 proj2_format BWP_Downlink__cond BWP_Downlink__list_format  BWP_Downlink__F1 BWP_Downlink__F2 BWP_Downlink__helper1 BWP_Downlink__helper2 BWP_Downlink__helper3.

Opaque BWP_Downlink__cond BWP_Downlink__Format.

