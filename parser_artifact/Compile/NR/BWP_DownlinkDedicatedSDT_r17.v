Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.PDCCH_Config.
Definition BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Type := SetupRelease__Type PDCCH_Config__Type.
Definition BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__cond := SetupRelease__cond _ PDCCH_Config__cond.
Definition BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Format : T_Format BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Type BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__cond := SetupRelease__Format _ _ PDCCH_Config__Format.
Opaque BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__cond BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PDSCH_Config.
Definition BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Type := SetupRelease__Type PDSCH_Config__Type.
Definition BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__cond := SetupRelease__cond _ PDSCH_Config__cond.
Definition BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Format : T_Format BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Type BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__cond := SetupRelease__Format _ _ PDSCH_Config__Format.
Opaque BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__cond BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Format.

Record BWP_DownlinkDedicatedSDT_r17__Type : Set :=
  make__BWP_DownlinkDedicatedSDT_r17__Type {
    BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17 : option BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Type ;
    BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17 : option BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Type ;
}.
Definition BWP_DownlinkDedicatedSDT_r17__root_list : list seq_elem := (
 Opt BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Type BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__cond ::
 Opt BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Type BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__cond ::
 nil).
Definition BWP_DownlinkDedicatedSDT_r17__ext_list : list typ := (
  nil).
Definition BWP_DownlinkDedicatedSDT_r17__cond (z : BWP_DownlinkDedicatedSDT_r17__Type) := 
(  opt_cond BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__cond (BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17 z) /\
  opt_cond BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__cond (BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17 z) /\
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
Opaque BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__cond BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Format.

Opaque BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__cond BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Format.


Definition BWP_DownlinkDedicatedSDT_r17__root_Format_Type := Eval cbn in seq_format_prod BWP_DownlinkDedicatedSDT_r17__root_list.
Definition BWP_DownlinkDedicatedSDT_r17__root_Format_list : BWP_DownlinkDedicatedSDT_r17__root_Format_Type :=
  (BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17__Format, (BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17__Format, unit_format)).

Definition BWP_DownlinkDedicatedSDT_r17__ext_Format_Type := Eval cbn in get_formats BWP_DownlinkDedicatedSDT_r17__ext_list.
Definition BWP_DownlinkDedicatedSDT_r17__ext_Format_list : BWP_DownlinkDedicatedSDT_r17__ext_Format_Type :=
  unit__Format.

Definition BWP_DownlinkDedicatedSDT_r17__list_type : Set := (seq_type BWP_DownlinkDedicatedSDT_r17__root_list) * (seq_ext_type BWP_DownlinkDedicatedSDT_r17__ext_list).
Definition BWP_DownlinkDedicatedSDT_r17__list_cond (z : BWP_DownlinkDedicatedSDT_r17__list_type) : Prop :=
        (seq_cond BWP_DownlinkDedicatedSDT_r17__root_list (fst z)) /\ (seq_ext_cond BWP_DownlinkDedicatedSDT_r17__ext_list (snd z)).
Definition BWP_DownlinkDedicatedSDT_r17__list_format : T_Format BWP_DownlinkDedicatedSDT_r17__list_type BWP_DownlinkDedicatedSDT_r17__list_cond :=
 (* Eval compute in *) seq_ext_format BWP_DownlinkDedicatedSDT_r17__root_list BWP_DownlinkDedicatedSDT_r17__root_Format_list BWP_DownlinkDedicatedSDT_r17__ext_list BWP_DownlinkDedicatedSDT_r17__ext_Format_list.

Opaque BWP_DownlinkDedicatedSDT_r17__list_format.
Definition BWP_DownlinkDedicatedSDT_r17__F1 (z : BWP_DownlinkDedicatedSDT_r17__Type) : BWP_DownlinkDedicatedSDT_r17__list_type :=
  (((BWP_DownlinkDedicatedSDT_r17__pdcch_Config_r17 z, (BWP_DownlinkDedicatedSDT_r17__pdsch_Config_r17 z, tt))), (
tt)).
Definition BWP_DownlinkDedicatedSDT_r17__F2 (y : BWP_DownlinkDedicatedSDT_r17__list_type) : BWP_DownlinkDedicatedSDT_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__BWP_DownlinkDedicatedSDT_r17__Type j0 j1
  end.
Definition BWP_DownlinkDedicatedSDT_r17__helper1 : (forall a : BWP_DownlinkDedicatedSDT_r17__Type, BWP_DownlinkDedicatedSDT_r17__cond a -> BWP_DownlinkDedicatedSDT_r17__list_cond (BWP_DownlinkDedicatedSDT_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BWP_DownlinkDedicatedSDT_r17__helper2 : (forall a : BWP_DownlinkDedicatedSDT_r17__Type, BWP_DownlinkDedicatedSDT_r17__F2 (BWP_DownlinkDedicatedSDT_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BWP_DownlinkDedicatedSDT_r17__helper3 : (forall b : BWP_DownlinkDedicatedSDT_r17__list_type, BWP_DownlinkDedicatedSDT_r17__list_cond b -> BWP_DownlinkDedicatedSDT_r17__cond (BWP_DownlinkDedicatedSDT_r17__F2 b) /\ BWP_DownlinkDedicatedSDT_r17__F1 (BWP_DownlinkDedicatedSDT_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BWP_DownlinkDedicatedSDT_r17__cond, BWP_DownlinkDedicatedSDT_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BWP_DownlinkDedicatedSDT_r17__Format : T_Format BWP_DownlinkDedicatedSDT_r17__Type BWP_DownlinkDedicatedSDT_r17__cond :=
 proj2_format BWP_DownlinkDedicatedSDT_r17__cond BWP_DownlinkDedicatedSDT_r17__list_format  BWP_DownlinkDedicatedSDT_r17__F1 BWP_DownlinkDedicatedSDT_r17__F2 BWP_DownlinkDedicatedSDT_r17__helper1 BWP_DownlinkDedicatedSDT_r17__helper2 BWP_DownlinkDedicatedSDT_r17__helper3.

Opaque BWP_DownlinkDedicatedSDT_r17__cond BWP_DownlinkDedicatedSDT_r17__Format.

