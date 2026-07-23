Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition SIB6__messageIdentifier__Type := bit_string_fixed.
Definition SIB6__messageIdentifier__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition SIB6__serialNumber__Type := bit_string_fixed.
Definition SIB6__serialNumber__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition SIB6__warningType__Type := octet_string.
Definition SIB6__warningType__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 2)%Z).
Record SIB6__Type : Set :=
  make__SIB6__Type {
    SIB6__messageIdentifier : SIB6__messageIdentifier__Type ;
    SIB6__serialNumber : SIB6__serialNumber__Type ;
    SIB6__warningType : SIB6__warningType__Type ;
    SIB6__lateNonCriticalExtension : option octet_string ;
}.
Definition SIB6__root_list : list seq_elem := (
 Nor SIB6__messageIdentifier__Type SIB6__messageIdentifier__cond ::
 Nor SIB6__serialNumber__Type SIB6__serialNumber__cond ::
 Nor SIB6__warningType__Type SIB6__warningType__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB6__ext_list : list typ := (
  nil).
Definition SIB6__cond (z : SIB6__Type) := 
(  SIB6__messageIdentifier__cond (SIB6__messageIdentifier z) /\
  SIB6__serialNumber__cond (SIB6__serialNumber z) /\
  SIB6__warningType__cond (SIB6__warningType z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB6__lateNonCriticalExtension z) /\
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
Definition SIB6__messageIdentifier__Format : T_Format SIB6__messageIdentifier__Type SIB6__messageIdentifier__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque SIB6__messageIdentifier__cond SIB6__messageIdentifier__Format.

Definition SIB6__serialNumber__Format : T_Format SIB6__serialNumber__Type SIB6__serialNumber__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque SIB6__serialNumber__cond SIB6__serialNumber__Format.

Definition SIB6__warningType__Format : T_Format SIB6__warningType__Type SIB6__warningType__cond := (* Eval compute in *) octet_string_fixed_format 2.
Opaque SIB6__warningType__cond SIB6__warningType__Format.


Definition SIB6__root_Format_Type := Eval cbn in seq_format_prod SIB6__root_list.
Definition SIB6__root_Format_list : SIB6__root_Format_Type :=
  (SIB6__messageIdentifier__Format, (SIB6__serialNumber__Format, (SIB6__warningType__Format, (octet_string_nc__Format, unit_format)))).

Definition SIB6__ext_Format_Type := Eval cbn in get_formats SIB6__ext_list.
Definition SIB6__ext_Format_list : SIB6__ext_Format_Type :=
  unit__Format.

Definition SIB6__list_type : Set := (seq_type SIB6__root_list) * (seq_ext_type SIB6__ext_list).
Definition SIB6__list_cond (z : SIB6__list_type) : Prop :=
        (seq_cond SIB6__root_list (fst z)) /\ (seq_ext_cond SIB6__ext_list (snd z)).
Definition SIB6__list_format : T_Format SIB6__list_type SIB6__list_cond :=
 (* Eval compute in *) seq_ext_format SIB6__root_list SIB6__root_Format_list SIB6__ext_list SIB6__ext_Format_list.

Opaque SIB6__list_format.
Definition SIB6__F1 (z : SIB6__Type) : SIB6__list_type :=
  (((SIB6__messageIdentifier z, (SIB6__serialNumber z, (SIB6__warningType z, (SIB6__lateNonCriticalExtension z, tt))))), (
tt)).
Definition SIB6__F2 (y : SIB6__list_type) : SIB6__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SIB6__Type j0 j1 j2 j3
  end.
Definition SIB6__helper1 : (forall a : SIB6__Type, SIB6__cond a -> SIB6__list_cond (SIB6__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB6__helper2 : (forall a : SIB6__Type, SIB6__F2 (SIB6__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB6__helper3 : (forall b : SIB6__list_type, SIB6__list_cond b -> SIB6__cond (SIB6__F2 b) /\ SIB6__F1 (SIB6__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB6__cond, SIB6__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB6__Format : T_Format SIB6__Type SIB6__cond :=
 proj2_format SIB6__cond SIB6__list_format  SIB6__F1 SIB6__F2 SIB6__helper1 SIB6__helper2 SIB6__helper3.

Opaque SIB6__cond SIB6__Format.

