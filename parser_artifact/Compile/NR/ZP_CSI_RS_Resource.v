Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ZP_CSI_RS_ResourceId.

Opaque ZP_CSI_RS_ResourceId__cond ZP_CSI_RS_ResourceId__Format.

Require Import NR.CSI_RS_ResourceMapping.

Opaque CSI_RS_ResourceMapping__cond CSI_RS_ResourceMapping__Format.

Require Import NR.CSI_ResourcePeriodicityAndOffset.

Opaque CSI_ResourcePeriodicityAndOffset__cond CSI_ResourcePeriodicityAndOffset__Format.

Record ZP_CSI_RS_Resource__Type : Set :=
  make__ZP_CSI_RS_Resource__Type {
    ZP_CSI_RS_Resource__zp_CSI_RS_ResourceId : ZP_CSI_RS_ResourceId__Type ;
    ZP_CSI_RS_Resource__resourceMapping : CSI_RS_ResourceMapping__Type ;
    ZP_CSI_RS_Resource__periodicityAndOffset : option CSI_ResourcePeriodicityAndOffset__Type ;
}.
Definition ZP_CSI_RS_Resource__root_list : list seq_elem := (
 Nor ZP_CSI_RS_ResourceId__Type ZP_CSI_RS_ResourceId__cond ::
 Nor CSI_RS_ResourceMapping__Type CSI_RS_ResourceMapping__cond ::
 Opt CSI_ResourcePeriodicityAndOffset__Type CSI_ResourcePeriodicityAndOffset__cond ::
 nil).
Definition ZP_CSI_RS_Resource__ext_list : list typ := (
  nil).
Definition ZP_CSI_RS_Resource__cond (z : ZP_CSI_RS_Resource__Type) := 
(  ZP_CSI_RS_ResourceId__cond (ZP_CSI_RS_Resource__zp_CSI_RS_ResourceId z) /\
  CSI_RS_ResourceMapping__cond (ZP_CSI_RS_Resource__resourceMapping z) /\
  opt_cond CSI_ResourcePeriodicityAndOffset__cond (ZP_CSI_RS_Resource__periodicityAndOffset z) /\
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

Definition ZP_CSI_RS_Resource__root_Format_Type := Eval cbn in seq_format_prod ZP_CSI_RS_Resource__root_list.
Definition ZP_CSI_RS_Resource__root_Format_list : ZP_CSI_RS_Resource__root_Format_Type :=
  (ZP_CSI_RS_ResourceId__Format, (CSI_RS_ResourceMapping__Format, (CSI_ResourcePeriodicityAndOffset__Format, unit_format))).

Definition ZP_CSI_RS_Resource__ext_Format_Type := Eval cbn in get_formats ZP_CSI_RS_Resource__ext_list.
Definition ZP_CSI_RS_Resource__ext_Format_list : ZP_CSI_RS_Resource__ext_Format_Type :=
  unit__Format.

Definition ZP_CSI_RS_Resource__list_type : Set := (seq_type ZP_CSI_RS_Resource__root_list) * (seq_ext_type ZP_CSI_RS_Resource__ext_list).
Definition ZP_CSI_RS_Resource__list_cond (z : ZP_CSI_RS_Resource__list_type) : Prop :=
        (seq_cond ZP_CSI_RS_Resource__root_list (fst z)) /\ (seq_ext_cond ZP_CSI_RS_Resource__ext_list (snd z)).
Definition ZP_CSI_RS_Resource__list_format : T_Format ZP_CSI_RS_Resource__list_type ZP_CSI_RS_Resource__list_cond :=
 (* Eval compute in *) seq_ext_format ZP_CSI_RS_Resource__root_list ZP_CSI_RS_Resource__root_Format_list ZP_CSI_RS_Resource__ext_list ZP_CSI_RS_Resource__ext_Format_list.

Opaque ZP_CSI_RS_Resource__list_format.
Definition ZP_CSI_RS_Resource__F1 (z : ZP_CSI_RS_Resource__Type) : ZP_CSI_RS_Resource__list_type :=
  (((ZP_CSI_RS_Resource__zp_CSI_RS_ResourceId z, (ZP_CSI_RS_Resource__resourceMapping z, (ZP_CSI_RS_Resource__periodicityAndOffset z, tt)))), (
tt)).
Definition ZP_CSI_RS_Resource__F2 (y : ZP_CSI_RS_Resource__list_type) : ZP_CSI_RS_Resource__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__ZP_CSI_RS_Resource__Type j0 j1 j2
  end.
Definition ZP_CSI_RS_Resource__helper1 : (forall a : ZP_CSI_RS_Resource__Type, ZP_CSI_RS_Resource__cond a -> ZP_CSI_RS_Resource__list_cond (ZP_CSI_RS_Resource__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ZP_CSI_RS_Resource__helper2 : (forall a : ZP_CSI_RS_Resource__Type, ZP_CSI_RS_Resource__F2 (ZP_CSI_RS_Resource__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ZP_CSI_RS_Resource__helper3 : (forall b : ZP_CSI_RS_Resource__list_type, ZP_CSI_RS_Resource__list_cond b -> ZP_CSI_RS_Resource__cond (ZP_CSI_RS_Resource__F2 b) /\ ZP_CSI_RS_Resource__F1 (ZP_CSI_RS_Resource__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ZP_CSI_RS_Resource__cond, ZP_CSI_RS_Resource__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ZP_CSI_RS_Resource__Format : T_Format ZP_CSI_RS_Resource__Type ZP_CSI_RS_Resource__cond :=
 proj2_format ZP_CSI_RS_Resource__cond ZP_CSI_RS_Resource__list_format  ZP_CSI_RS_Resource__F1 ZP_CSI_RS_Resource__F2 ZP_CSI_RS_Resource__helper1 ZP_CSI_RS_Resource__helper2 ZP_CSI_RS_Resource__helper3.

Opaque ZP_CSI_RS_Resource__cond ZP_CSI_RS_Resource__Format.

