Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CipheringAlgorithm.

Opaque CipheringAlgorithm__cond CipheringAlgorithm__Format.

Require Import NR.IntegrityProtAlgorithm.

Opaque IntegrityProtAlgorithm__cond IntegrityProtAlgorithm__Format.

Record SecurityAlgorithmConfig__Type : Set :=
  make__SecurityAlgorithmConfig__Type {
    SecurityAlgorithmConfig__cipheringAlgorithm : CipheringAlgorithm__Type ;
    SecurityAlgorithmConfig__integrityProtAlgorithm : option IntegrityProtAlgorithm__Type ;
}.
Definition SecurityAlgorithmConfig__root_list : list seq_elem := (
 Nor CipheringAlgorithm__Type CipheringAlgorithm__cond ::
 Opt IntegrityProtAlgorithm__Type IntegrityProtAlgorithm__cond ::
 nil).
Definition SecurityAlgorithmConfig__ext_list : list typ := (
  nil).
Definition SecurityAlgorithmConfig__cond (z : SecurityAlgorithmConfig__Type) := 
(  CipheringAlgorithm__cond (SecurityAlgorithmConfig__cipheringAlgorithm z) /\
  opt_cond IntegrityProtAlgorithm__cond (SecurityAlgorithmConfig__integrityProtAlgorithm z) /\
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

Definition SecurityAlgorithmConfig__root_Format_Type := Eval cbn in seq_format_prod SecurityAlgorithmConfig__root_list.
Definition SecurityAlgorithmConfig__root_Format_list : SecurityAlgorithmConfig__root_Format_Type :=
  (CipheringAlgorithm__Format, (IntegrityProtAlgorithm__Format, unit_format)).

Definition SecurityAlgorithmConfig__ext_Format_Type := Eval cbn in get_formats SecurityAlgorithmConfig__ext_list.
Definition SecurityAlgorithmConfig__ext_Format_list : SecurityAlgorithmConfig__ext_Format_Type :=
  unit__Format.

Definition SecurityAlgorithmConfig__list_type : Set := (seq_type SecurityAlgorithmConfig__root_list) * (seq_ext_type SecurityAlgorithmConfig__ext_list).
Definition SecurityAlgorithmConfig__list_cond (z : SecurityAlgorithmConfig__list_type) : Prop :=
        (seq_cond SecurityAlgorithmConfig__root_list (fst z)) /\ (seq_ext_cond SecurityAlgorithmConfig__ext_list (snd z)).
Definition SecurityAlgorithmConfig__list_format : T_Format SecurityAlgorithmConfig__list_type SecurityAlgorithmConfig__list_cond :=
 (* Eval compute in *) seq_ext_format SecurityAlgorithmConfig__root_list SecurityAlgorithmConfig__root_Format_list SecurityAlgorithmConfig__ext_list SecurityAlgorithmConfig__ext_Format_list.

Opaque SecurityAlgorithmConfig__list_format.
Definition SecurityAlgorithmConfig__F1 (z : SecurityAlgorithmConfig__Type) : SecurityAlgorithmConfig__list_type :=
  (((SecurityAlgorithmConfig__cipheringAlgorithm z, (SecurityAlgorithmConfig__integrityProtAlgorithm z, tt))), (
tt)).
Definition SecurityAlgorithmConfig__F2 (y : SecurityAlgorithmConfig__list_type) : SecurityAlgorithmConfig__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__SecurityAlgorithmConfig__Type j0 j1
  end.
Definition SecurityAlgorithmConfig__helper1 : (forall a : SecurityAlgorithmConfig__Type, SecurityAlgorithmConfig__cond a -> SecurityAlgorithmConfig__list_cond (SecurityAlgorithmConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SecurityAlgorithmConfig__helper2 : (forall a : SecurityAlgorithmConfig__Type, SecurityAlgorithmConfig__F2 (SecurityAlgorithmConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SecurityAlgorithmConfig__helper3 : (forall b : SecurityAlgorithmConfig__list_type, SecurityAlgorithmConfig__list_cond b -> SecurityAlgorithmConfig__cond (SecurityAlgorithmConfig__F2 b) /\ SecurityAlgorithmConfig__F1 (SecurityAlgorithmConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SecurityAlgorithmConfig__cond, SecurityAlgorithmConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SecurityAlgorithmConfig__Format : T_Format SecurityAlgorithmConfig__Type SecurityAlgorithmConfig__cond :=
 proj2_format SecurityAlgorithmConfig__cond SecurityAlgorithmConfig__list_format  SecurityAlgorithmConfig__F1 SecurityAlgorithmConfig__F2 SecurityAlgorithmConfig__helper1 SecurityAlgorithmConfig__helper2 SecurityAlgorithmConfig__helper3.

Opaque SecurityAlgorithmConfig__cond SecurityAlgorithmConfig__Format.

