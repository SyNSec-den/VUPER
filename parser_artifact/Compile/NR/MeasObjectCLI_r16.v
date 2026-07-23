Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CLI_ResourceConfig_r16.

Opaque CLI_ResourceConfig_r16__cond CLI_ResourceConfig_r16__Format.

Record MeasObjectCLI_r16__Type : Set :=
  make__MeasObjectCLI_r16__Type {
    MeasObjectCLI_r16__cli_ResourceConfig_r16 : CLI_ResourceConfig_r16__Type ;
}.
Definition MeasObjectCLI_r16__root_list : list seq_elem := (
 Nor CLI_ResourceConfig_r16__Type CLI_ResourceConfig_r16__cond ::
 nil).
Definition MeasObjectCLI_r16__ext_list : list typ := (
  nil).
Definition MeasObjectCLI_r16__cond (z : MeasObjectCLI_r16__Type) := 
(  CLI_ResourceConfig_r16__cond (MeasObjectCLI_r16__cli_ResourceConfig_r16 z) /\
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

Definition MeasObjectCLI_r16__root_Format_Type := Eval cbn in seq_format_prod MeasObjectCLI_r16__root_list.
Definition MeasObjectCLI_r16__root_Format_list : MeasObjectCLI_r16__root_Format_Type :=
  (CLI_ResourceConfig_r16__Format, unit_format).

Definition MeasObjectCLI_r16__ext_Format_Type := Eval cbn in get_formats MeasObjectCLI_r16__ext_list.
Definition MeasObjectCLI_r16__ext_Format_list : MeasObjectCLI_r16__ext_Format_Type :=
  unit__Format.

Definition MeasObjectCLI_r16__list_type : Set := (seq_type MeasObjectCLI_r16__root_list) * (seq_ext_type MeasObjectCLI_r16__ext_list).
Definition MeasObjectCLI_r16__list_cond (z : MeasObjectCLI_r16__list_type) : Prop :=
        (seq_cond MeasObjectCLI_r16__root_list (fst z)) /\ (seq_ext_cond MeasObjectCLI_r16__ext_list (snd z)).
Definition MeasObjectCLI_r16__list_format : T_Format MeasObjectCLI_r16__list_type MeasObjectCLI_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasObjectCLI_r16__root_list MeasObjectCLI_r16__root_Format_list MeasObjectCLI_r16__ext_list MeasObjectCLI_r16__ext_Format_list.

Opaque MeasObjectCLI_r16__list_format.
Definition MeasObjectCLI_r16__F1 (z : MeasObjectCLI_r16__Type) : MeasObjectCLI_r16__list_type :=
  (((MeasObjectCLI_r16__cli_ResourceConfig_r16 z, tt)), (
tt)).
Definition MeasObjectCLI_r16__F2 (y : MeasObjectCLI_r16__list_type) : MeasObjectCLI_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__MeasObjectCLI_r16__Type j0
  end.
Definition MeasObjectCLI_r16__helper1 : (forall a : MeasObjectCLI_r16__Type, MeasObjectCLI_r16__cond a -> MeasObjectCLI_r16__list_cond (MeasObjectCLI_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasObjectCLI_r16__helper2 : (forall a : MeasObjectCLI_r16__Type, MeasObjectCLI_r16__F2 (MeasObjectCLI_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasObjectCLI_r16__helper3 : (forall b : MeasObjectCLI_r16__list_type, MeasObjectCLI_r16__list_cond b -> MeasObjectCLI_r16__cond (MeasObjectCLI_r16__F2 b) /\ MeasObjectCLI_r16__F1 (MeasObjectCLI_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasObjectCLI_r16__cond, MeasObjectCLI_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasObjectCLI_r16__Format : T_Format MeasObjectCLI_r16__Type MeasObjectCLI_r16__cond :=
 proj2_format MeasObjectCLI_r16__cond MeasObjectCLI_r16__list_format  MeasObjectCLI_r16__F1 MeasObjectCLI_r16__F2 MeasObjectCLI_r16__helper1 MeasObjectCLI_r16__helper2 MeasObjectCLI_r16__helper3.

Opaque MeasObjectCLI_r16__cond MeasObjectCLI_r16__Format.

