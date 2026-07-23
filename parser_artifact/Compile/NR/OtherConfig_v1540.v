Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.OverheatingAssistanceConfig.
Definition OtherConfig_v1540__overheatingAssistanceConfig__Type := SetupRelease__Type OverheatingAssistanceConfig__Type.
Definition OtherConfig_v1540__overheatingAssistanceConfig__cond := SetupRelease__cond _ OverheatingAssistanceConfig__cond.
Definition OtherConfig_v1540__overheatingAssistanceConfig__Format : T_Format OtherConfig_v1540__overheatingAssistanceConfig__Type OtherConfig_v1540__overheatingAssistanceConfig__cond := SetupRelease__Format _ _ OverheatingAssistanceConfig__Format.
Opaque OtherConfig_v1540__overheatingAssistanceConfig__cond OtherConfig_v1540__overheatingAssistanceConfig__Format.

Record OtherConfig_v1540__Type : Set :=
  make__OtherConfig_v1540__Type {
    OtherConfig_v1540__overheatingAssistanceConfig : option OtherConfig_v1540__overheatingAssistanceConfig__Type ;
}.
Definition OtherConfig_v1540__root_list : list seq_elem := (
 Opt OtherConfig_v1540__overheatingAssistanceConfig__Type OtherConfig_v1540__overheatingAssistanceConfig__cond ::
 nil).
Definition OtherConfig_v1540__ext_list : list typ := (
  nil).
Definition OtherConfig_v1540__cond (z : OtherConfig_v1540__Type) := 
(  opt_cond OtherConfig_v1540__overheatingAssistanceConfig__cond (OtherConfig_v1540__overheatingAssistanceConfig z) /\
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
Opaque OtherConfig_v1540__overheatingAssistanceConfig__cond OtherConfig_v1540__overheatingAssistanceConfig__Format.


Definition OtherConfig_v1540__root_Format_Type := Eval cbn in seq_format_prod OtherConfig_v1540__root_list.
Definition OtherConfig_v1540__root_Format_list : OtherConfig_v1540__root_Format_Type :=
  (OtherConfig_v1540__overheatingAssistanceConfig__Format, unit_format).

Definition OtherConfig_v1540__ext_Format_Type := Eval cbn in get_formats OtherConfig_v1540__ext_list.
Definition OtherConfig_v1540__ext_Format_list : OtherConfig_v1540__ext_Format_Type :=
  unit__Format.

Definition OtherConfig_v1540__list_type : Set := (seq_type OtherConfig_v1540__root_list) * (seq_ext_type OtherConfig_v1540__ext_list).
Definition OtherConfig_v1540__list_cond (z : OtherConfig_v1540__list_type) : Prop :=
        (seq_cond OtherConfig_v1540__root_list (fst z)) /\ (seq_ext_cond OtherConfig_v1540__ext_list (snd z)).
Definition OtherConfig_v1540__list_format : T_Format OtherConfig_v1540__list_type OtherConfig_v1540__list_cond :=
 (* Eval compute in *) seq_ext_format OtherConfig_v1540__root_list OtherConfig_v1540__root_Format_list OtherConfig_v1540__ext_list OtherConfig_v1540__ext_Format_list.

Opaque OtherConfig_v1540__list_format.
Definition OtherConfig_v1540__F1 (z : OtherConfig_v1540__Type) : OtherConfig_v1540__list_type :=
  (((OtherConfig_v1540__overheatingAssistanceConfig z, tt)), (
tt)).
Definition OtherConfig_v1540__F2 (y : OtherConfig_v1540__list_type) : OtherConfig_v1540__Type :=
  match y with
  | ((j0, _), _)=>
    make__OtherConfig_v1540__Type j0
  end.
Definition OtherConfig_v1540__helper1 : (forall a : OtherConfig_v1540__Type, OtherConfig_v1540__cond a -> OtherConfig_v1540__list_cond (OtherConfig_v1540__F1 a)).
                     intros. destruct a. auto. Qed.
Definition OtherConfig_v1540__helper2 : (forall a : OtherConfig_v1540__Type, OtherConfig_v1540__F2 (OtherConfig_v1540__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition OtherConfig_v1540__helper3 : (forall b : OtherConfig_v1540__list_type, OtherConfig_v1540__list_cond b -> OtherConfig_v1540__cond (OtherConfig_v1540__F2 b) /\ OtherConfig_v1540__F1 (OtherConfig_v1540__F2 b) = b).
                     intros. destruct b as [y y1]. unfold OtherConfig_v1540__cond, OtherConfig_v1540__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition OtherConfig_v1540__Format : T_Format OtherConfig_v1540__Type OtherConfig_v1540__cond :=
 proj2_format OtherConfig_v1540__cond OtherConfig_v1540__list_format  OtherConfig_v1540__F1 OtherConfig_v1540__F2 OtherConfig_v1540__helper1 OtherConfig_v1540__helper2 OtherConfig_v1540__helper3.

Opaque OtherConfig_v1540__cond OtherConfig_v1540__Format.

