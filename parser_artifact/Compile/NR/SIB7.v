Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition SIB7__messageIdentifier__Type := bit_string_fixed.
Definition SIB7__messageIdentifier__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition SIB7__serialNumber__Type := bit_string_fixed.
Definition SIB7__serialNumber__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Inductive SIB7__warningMessageSegmentType__Type : Set :=
 | SIB7__warningMessageSegmentType__notLastSegment
 | SIB7__warningMessageSegmentType__lastSegment
.
Definition SIB7__warningMessageSegmentType__cond := (fun (_ : SIB7__warningMessageSegmentType__Type) => True).
Lemma SIB7__warningMessageSegmentType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB7__warningMessageSegmentType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SIB7__warningMessageSegmentType__nat__helper.

Definition SIB7__warningMessageSegmentType__F1 t :=
  match t with
  | SIB7__warningMessageSegmentType__notLastSegment => 0
  | SIB7__warningMessageSegmentType__lastSegment => 1
  end.
Definition SIB7__warningMessageSegmentType__F2 n :=
  match n with
  | 0 => SIB7__warningMessageSegmentType__notLastSegment
  | 1 => SIB7__warningMessageSegmentType__lastSegment
  | _ => SIB7__warningMessageSegmentType__notLastSegment
  end.
Lemma SIB7__warningMessageSegmentType__F1F2 : forall x : SIB7__warningMessageSegmentType__Type, (SIB7__warningMessageSegmentType__F1 x <= 1) /\ SIB7__warningMessageSegmentType__F2 (SIB7__warningMessageSegmentType__F1 x) = x. imp_solve. Qed.
Lemma SIB7__warningMessageSegmentType__F2F1 : forall (y : nat) (H : y <= 1), SIB7__warningMessageSegmentType__F1 (SIB7__warningMessageSegmentType__F2 y) = y. enum_solve H y. Qed.

Lemma SIB7__warningMessageSegmentNumber__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SIB7__warningMessageSegmentNumber__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB7__warningMessageSegmentNumber__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB7__warningMessageSegmentNumber__Type := Z.
Definition SIB7__warningMessageSegmentNumber__cond := (fun z => (0 <= z <= 63)%Z).
Definition SIB7__dataCodingScheme__Type := octet_string.
Definition SIB7__dataCodingScheme__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 1)%Z).
Record SIB7__Type : Set :=
  make__SIB7__Type {
    SIB7__messageIdentifier : SIB7__messageIdentifier__Type ;
    SIB7__serialNumber : SIB7__serialNumber__Type ;
    SIB7__warningMessageSegmentType : SIB7__warningMessageSegmentType__Type ;
    SIB7__warningMessageSegmentNumber : Z ;
    SIB7__warningMessageSegment : octet_string ;
    SIB7__dataCodingScheme : option SIB7__dataCodingScheme__Type ;
    SIB7__lateNonCriticalExtension : option octet_string ;
}.
Definition SIB7__root_list : list seq_elem := (
 Nor SIB7__messageIdentifier__Type SIB7__messageIdentifier__cond ::
 Nor SIB7__serialNumber__Type SIB7__serialNumber__cond ::
 Nor SIB7__warningMessageSegmentType__Type SIB7__warningMessageSegmentType__cond ::
 Nor Z SIB7__warningMessageSegmentNumber__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SIB7__dataCodingScheme__Type SIB7__dataCodingScheme__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB7__ext_list : list typ := (
  nil).
Definition SIB7__cond (z : SIB7__Type) := 
(  SIB7__messageIdentifier__cond (SIB7__messageIdentifier z) /\
  SIB7__serialNumber__cond (SIB7__serialNumber z) /\
  SIB7__warningMessageSegmentType__cond (SIB7__warningMessageSegmentType z) /\
  SIB7__warningMessageSegmentNumber__cond (SIB7__warningMessageSegmentNumber z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB7__warningMessageSegment z) /\
  opt_cond SIB7__dataCodingScheme__cond (SIB7__dataCodingScheme z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB7__lateNonCriticalExtension z) /\
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
Definition SIB7__messageIdentifier__Format : T_Format SIB7__messageIdentifier__Type SIB7__messageIdentifier__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque SIB7__messageIdentifier__cond SIB7__messageIdentifier__Format.

Definition SIB7__serialNumber__Format : T_Format SIB7__serialNumber__Type SIB7__serialNumber__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque SIB7__serialNumber__cond SIB7__serialNumber__Format.

Definition SIB7__warningMessageSegmentType__Format : T_Format SIB7__warningMessageSegmentType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB7__warningMessageSegmentType__nat__Format SIB7__warningMessageSegmentType__F1 SIB7__warningMessageSegmentType__F2 SIB7__warningMessageSegmentType__F1F2 SIB7__warningMessageSegmentType__F2F1.

Opaque SIB7__warningMessageSegmentType__cond SIB7__warningMessageSegmentType__Format.

Definition SIB7__warningMessageSegmentNumber__Format : T_Format Z SIB7__warningMessageSegmentNumber__cond :=
 ranged_int_format (0) (63) SIB7__warningMessageSegmentNumber__helper1 SIB7__warningMessageSegmentNumber__helper2.

Opaque SIB7__warningMessageSegmentNumber__cond SIB7__warningMessageSegmentNumber__Format.

Definition SIB7__dataCodingScheme__Format : T_Format SIB7__dataCodingScheme__Type SIB7__dataCodingScheme__cond := (* Eval compute in *) octet_string_fixed_format 1.
Opaque SIB7__dataCodingScheme__cond SIB7__dataCodingScheme__Format.


Definition SIB7__root_Format_Type := Eval cbn in seq_format_prod SIB7__root_list.
Definition SIB7__root_Format_list : SIB7__root_Format_Type :=
  (SIB7__messageIdentifier__Format, (SIB7__serialNumber__Format, (SIB7__warningMessageSegmentType__Format, (SIB7__warningMessageSegmentNumber__Format, (octet_string_nc__Format, (SIB7__dataCodingScheme__Format, (octet_string_nc__Format, unit_format))))))).

Definition SIB7__ext_Format_Type := Eval cbn in get_formats SIB7__ext_list.
Definition SIB7__ext_Format_list : SIB7__ext_Format_Type :=
  unit__Format.

Definition SIB7__list_type : Set := (seq_type SIB7__root_list) * (seq_ext_type SIB7__ext_list).
Definition SIB7__list_cond (z : SIB7__list_type) : Prop :=
        (seq_cond SIB7__root_list (fst z)) /\ (seq_ext_cond SIB7__ext_list (snd z)).
Definition SIB7__list_format : T_Format SIB7__list_type SIB7__list_cond :=
 (* Eval compute in *) seq_ext_format SIB7__root_list SIB7__root_Format_list SIB7__ext_list SIB7__ext_Format_list.

Opaque SIB7__list_format.
Definition SIB7__F1 (z : SIB7__Type) : SIB7__list_type :=
  (((SIB7__messageIdentifier z, (SIB7__serialNumber z, (SIB7__warningMessageSegmentType z, (SIB7__warningMessageSegmentNumber z, (SIB7__warningMessageSegment z, (SIB7__dataCodingScheme z, (SIB7__lateNonCriticalExtension z, tt)))))))), (
tt)).
Definition SIB7__F2 (y : SIB7__list_type) : SIB7__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), _)=>
    make__SIB7__Type j0 j1 j2 j3 j4 j5 j6
  end.
Definition SIB7__helper1 : (forall a : SIB7__Type, SIB7__cond a -> SIB7__list_cond (SIB7__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB7__helper2 : (forall a : SIB7__Type, SIB7__F2 (SIB7__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB7__helper3 : (forall b : SIB7__list_type, SIB7__list_cond b -> SIB7__cond (SIB7__F2 b) /\ SIB7__F1 (SIB7__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB7__cond, SIB7__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB7__Format : T_Format SIB7__Type SIB7__cond :=
 proj2_format SIB7__cond SIB7__list_format  SIB7__F1 SIB7__F2 SIB7__helper1 SIB7__helper2 SIB7__helper3.

Opaque SIB7__cond SIB7__Format.

