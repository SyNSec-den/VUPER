Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_Resource.

Opaque SRS_Resource__cond SRS_Resource__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Record SRS_ResourceConfigCLI_r16__Type : Set :=
  make__SRS_ResourceConfigCLI_r16__Type {
    SRS_ResourceConfigCLI_r16__srs_Resource_r16 : SRS_Resource__Type ;
    SRS_ResourceConfigCLI_r16__srs_SCS_r16 : SubcarrierSpacing__Type ;
    SRS_ResourceConfigCLI_r16__refServCellIndex_r16 : option ServCellIndex__Type ;
    SRS_ResourceConfigCLI_r16__refBWP_r16 : BWP_Id__Type ;
}.
Definition SRS_ResourceConfigCLI_r16__root_list : list seq_elem := (
 Nor SRS_Resource__Type SRS_Resource__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Nor BWP_Id__Type BWP_Id__cond ::
 nil).
Definition SRS_ResourceConfigCLI_r16__ext_list : list typ := (
  nil).
Definition SRS_ResourceConfigCLI_r16__cond (z : SRS_ResourceConfigCLI_r16__Type) := 
(  SRS_Resource__cond (SRS_ResourceConfigCLI_r16__srs_Resource_r16 z) /\
  SubcarrierSpacing__cond (SRS_ResourceConfigCLI_r16__srs_SCS_r16 z) /\
  opt_cond ServCellIndex__cond (SRS_ResourceConfigCLI_r16__refServCellIndex_r16 z) /\
  BWP_Id__cond (SRS_ResourceConfigCLI_r16__refBWP_r16 z) /\
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

Definition SRS_ResourceConfigCLI_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_ResourceConfigCLI_r16__root_list.
Definition SRS_ResourceConfigCLI_r16__root_Format_list : SRS_ResourceConfigCLI_r16__root_Format_Type :=
  (SRS_Resource__Format, (SubcarrierSpacing__Format, (ServCellIndex__Format, (BWP_Id__Format, unit_format)))).

Definition SRS_ResourceConfigCLI_r16__ext_Format_Type := Eval cbn in get_formats SRS_ResourceConfigCLI_r16__ext_list.
Definition SRS_ResourceConfigCLI_r16__ext_Format_list : SRS_ResourceConfigCLI_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_ResourceConfigCLI_r16__list_type : Set := (seq_type SRS_ResourceConfigCLI_r16__root_list) * (seq_ext_type SRS_ResourceConfigCLI_r16__ext_list).
Definition SRS_ResourceConfigCLI_r16__list_cond (z : SRS_ResourceConfigCLI_r16__list_type) : Prop :=
        (seq_cond SRS_ResourceConfigCLI_r16__root_list (fst z)) /\ (seq_ext_cond SRS_ResourceConfigCLI_r16__ext_list (snd z)).
Definition SRS_ResourceConfigCLI_r16__list_format : T_Format SRS_ResourceConfigCLI_r16__list_type SRS_ResourceConfigCLI_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_ResourceConfigCLI_r16__root_list SRS_ResourceConfigCLI_r16__root_Format_list SRS_ResourceConfigCLI_r16__ext_list SRS_ResourceConfigCLI_r16__ext_Format_list.

Opaque SRS_ResourceConfigCLI_r16__list_format.
Definition SRS_ResourceConfigCLI_r16__F1 (z : SRS_ResourceConfigCLI_r16__Type) : SRS_ResourceConfigCLI_r16__list_type :=
  (((SRS_ResourceConfigCLI_r16__srs_Resource_r16 z, (SRS_ResourceConfigCLI_r16__srs_SCS_r16 z, (SRS_ResourceConfigCLI_r16__refServCellIndex_r16 z, (SRS_ResourceConfigCLI_r16__refBWP_r16 z, tt))))), (
tt)).
Definition SRS_ResourceConfigCLI_r16__F2 (y : SRS_ResourceConfigCLI_r16__list_type) : SRS_ResourceConfigCLI_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SRS_ResourceConfigCLI_r16__Type j0 j1 j2 j3
  end.
Definition SRS_ResourceConfigCLI_r16__helper1 : (forall a : SRS_ResourceConfigCLI_r16__Type, SRS_ResourceConfigCLI_r16__cond a -> SRS_ResourceConfigCLI_r16__list_cond (SRS_ResourceConfigCLI_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceConfigCLI_r16__helper2 : (forall a : SRS_ResourceConfigCLI_r16__Type, SRS_ResourceConfigCLI_r16__F2 (SRS_ResourceConfigCLI_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceConfigCLI_r16__helper3 : (forall b : SRS_ResourceConfigCLI_r16__list_type, SRS_ResourceConfigCLI_r16__list_cond b -> SRS_ResourceConfigCLI_r16__cond (SRS_ResourceConfigCLI_r16__F2 b) /\ SRS_ResourceConfigCLI_r16__F1 (SRS_ResourceConfigCLI_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_ResourceConfigCLI_r16__cond, SRS_ResourceConfigCLI_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_ResourceConfigCLI_r16__Format : T_Format SRS_ResourceConfigCLI_r16__Type SRS_ResourceConfigCLI_r16__cond :=
 proj2_format SRS_ResourceConfigCLI_r16__cond SRS_ResourceConfigCLI_r16__list_format  SRS_ResourceConfigCLI_r16__F1 SRS_ResourceConfigCLI_r16__F2 SRS_ResourceConfigCLI_r16__helper1 SRS_ResourceConfigCLI_r16__helper2 SRS_ResourceConfigCLI_r16__helper3.

Opaque SRS_ResourceConfigCLI_r16__cond SRS_ResourceConfigCLI_r16__Format.

