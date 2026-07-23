Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SecurityAlgorithmConfig.

Opaque SecurityAlgorithmConfig__cond SecurityAlgorithmConfig__Format.

Record SecurityConfigSMC__Type : Set :=
  make__SecurityConfigSMC__Type {
    SecurityConfigSMC__securityAlgorithmConfig : SecurityAlgorithmConfig__Type ;
}.
Definition SecurityConfigSMC__root_list : list seq_elem := (
 Nor SecurityAlgorithmConfig__Type SecurityAlgorithmConfig__cond ::
 nil).
Definition SecurityConfigSMC__ext_list : list typ := (
  nil).
Definition SecurityConfigSMC__cond (z : SecurityConfigSMC__Type) := 
(  SecurityAlgorithmConfig__cond (SecurityConfigSMC__securityAlgorithmConfig z) /\
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

Definition SecurityConfigSMC__root_Format_Type := Eval cbn in seq_format_prod SecurityConfigSMC__root_list.
Definition SecurityConfigSMC__root_Format_list : SecurityConfigSMC__root_Format_Type :=
  (SecurityAlgorithmConfig__Format, unit_format).

Definition SecurityConfigSMC__ext_Format_Type := Eval cbn in get_formats SecurityConfigSMC__ext_list.
Definition SecurityConfigSMC__ext_Format_list : SecurityConfigSMC__ext_Format_Type :=
  unit__Format.

Definition SecurityConfigSMC__list_type : Set := (seq_type SecurityConfigSMC__root_list) * (seq_ext_type SecurityConfigSMC__ext_list).
Definition SecurityConfigSMC__list_cond (z : SecurityConfigSMC__list_type) : Prop :=
        (seq_cond SecurityConfigSMC__root_list (fst z)) /\ (seq_ext_cond SecurityConfigSMC__ext_list (snd z)).
Definition SecurityConfigSMC__list_format : T_Format SecurityConfigSMC__list_type SecurityConfigSMC__list_cond :=
 (* Eval compute in *) seq_ext_format SecurityConfigSMC__root_list SecurityConfigSMC__root_Format_list SecurityConfigSMC__ext_list SecurityConfigSMC__ext_Format_list.

Opaque SecurityConfigSMC__list_format.
Definition SecurityConfigSMC__F1 (z : SecurityConfigSMC__Type) : SecurityConfigSMC__list_type :=
  (((SecurityConfigSMC__securityAlgorithmConfig z, tt)), (
tt)).
Definition SecurityConfigSMC__F2 (y : SecurityConfigSMC__list_type) : SecurityConfigSMC__Type :=
  match y with
  | ((j0, _), _)=>
    make__SecurityConfigSMC__Type j0
  end.
Definition SecurityConfigSMC__helper1 : (forall a : SecurityConfigSMC__Type, SecurityConfigSMC__cond a -> SecurityConfigSMC__list_cond (SecurityConfigSMC__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SecurityConfigSMC__helper2 : (forall a : SecurityConfigSMC__Type, SecurityConfigSMC__F2 (SecurityConfigSMC__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SecurityConfigSMC__helper3 : (forall b : SecurityConfigSMC__list_type, SecurityConfigSMC__list_cond b -> SecurityConfigSMC__cond (SecurityConfigSMC__F2 b) /\ SecurityConfigSMC__F1 (SecurityConfigSMC__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SecurityConfigSMC__cond, SecurityConfigSMC__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SecurityConfigSMC__Format : T_Format SecurityConfigSMC__Type SecurityConfigSMC__cond :=
 proj2_format SecurityConfigSMC__cond SecurityConfigSMC__list_format  SecurityConfigSMC__F1 SecurityConfigSMC__F2 SecurityConfigSMC__helper1 SecurityConfigSMC__helper2 SecurityConfigSMC__helper3.

Opaque SecurityConfigSMC__cond SecurityConfigSMC__Format.

