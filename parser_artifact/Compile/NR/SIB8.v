Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition SIB8__messageIdentifier__Type := bit_string_fixed.
Definition SIB8__messageIdentifier__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition SIB8__serialNumber__Type := bit_string_fixed.
Definition SIB8__serialNumber__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Inductive SIB8__warningMessageSegmentType__Type : Set :=
 | SIB8__warningMessageSegmentType__notLastSegment
 | SIB8__warningMessageSegmentType__lastSegment
.
Definition SIB8__warningMessageSegmentType__cond := (fun (_ : SIB8__warningMessageSegmentType__Type) => True).
Lemma SIB8__warningMessageSegmentType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB8__warningMessageSegmentType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SIB8__warningMessageSegmentType__nat__helper.

Definition SIB8__warningMessageSegmentType__F1 t :=
  match t with
  | SIB8__warningMessageSegmentType__notLastSegment => 0
  | SIB8__warningMessageSegmentType__lastSegment => 1
  end.
Definition SIB8__warningMessageSegmentType__F2 n :=
  match n with
  | 0 => SIB8__warningMessageSegmentType__notLastSegment
  | 1 => SIB8__warningMessageSegmentType__lastSegment
  | _ => SIB8__warningMessageSegmentType__notLastSegment
  end.
Lemma SIB8__warningMessageSegmentType__F1F2 : forall x : SIB8__warningMessageSegmentType__Type, (SIB8__warningMessageSegmentType__F1 x <= 1) /\ SIB8__warningMessageSegmentType__F2 (SIB8__warningMessageSegmentType__F1 x) = x. imp_solve. Qed.
Lemma SIB8__warningMessageSegmentType__F2F1 : forall (y : nat) (H : y <= 1), SIB8__warningMessageSegmentType__F1 (SIB8__warningMessageSegmentType__F2 y) = y. enum_solve H y. Qed.

Lemma SIB8__warningMessageSegmentNumber__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SIB8__warningMessageSegmentNumber__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB8__warningMessageSegmentNumber__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB8__warningMessageSegmentNumber__Type := Z.
Definition SIB8__warningMessageSegmentNumber__cond := (fun z => (0 <= z <= 63)%Z).
Definition SIB8__dataCodingScheme__Type := octet_string.
Definition SIB8__dataCodingScheme__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 1)%Z).
Record SIB8__Type : Set :=
  make__SIB8__Type {
    SIB8__messageIdentifier : SIB8__messageIdentifier__Type ;
    SIB8__serialNumber : SIB8__serialNumber__Type ;
    SIB8__warningMessageSegmentType : SIB8__warningMessageSegmentType__Type ;
    SIB8__warningMessageSegmentNumber : Z ;
    SIB8__warningMessageSegment : octet_string ;
    SIB8__dataCodingScheme : option SIB8__dataCodingScheme__Type ;
    SIB8__warningAreaCoordinatesSegment : option octet_string ;
    SIB8__lateNonCriticalExtension : option octet_string ;
}.
Definition SIB8__root_list : list seq_elem := (
 Nor SIB8__messageIdentifier__Type SIB8__messageIdentifier__cond ::
 Nor SIB8__serialNumber__Type SIB8__serialNumber__cond ::
 Nor SIB8__warningMessageSegmentType__Type SIB8__warningMessageSegmentType__cond ::
 Nor Z SIB8__warningMessageSegmentNumber__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SIB8__dataCodingScheme__Type SIB8__dataCodingScheme__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB8__ext_list : list typ := (
  nil).
Definition SIB8__cond (z : SIB8__Type) := 
(  SIB8__messageIdentifier__cond (SIB8__messageIdentifier z) /\
  SIB8__serialNumber__cond (SIB8__serialNumber z) /\
  SIB8__warningMessageSegmentType__cond (SIB8__warningMessageSegmentType z) /\
  SIB8__warningMessageSegmentNumber__cond (SIB8__warningMessageSegmentNumber z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB8__warningMessageSegment z) /\
  opt_cond SIB8__dataCodingScheme__cond (SIB8__dataCodingScheme z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB8__warningAreaCoordinatesSegment z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB8__lateNonCriticalExtension z) /\
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
Definition SIB8__messageIdentifier__Format : T_Format SIB8__messageIdentifier__Type SIB8__messageIdentifier__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque SIB8__messageIdentifier__cond SIB8__messageIdentifier__Format.

Definition SIB8__serialNumber__Format : T_Format SIB8__serialNumber__Type SIB8__serialNumber__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque SIB8__serialNumber__cond SIB8__serialNumber__Format.

Definition SIB8__warningMessageSegmentType__Format : T_Format SIB8__warningMessageSegmentType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB8__warningMessageSegmentType__nat__Format SIB8__warningMessageSegmentType__F1 SIB8__warningMessageSegmentType__F2 SIB8__warningMessageSegmentType__F1F2 SIB8__warningMessageSegmentType__F2F1.

Opaque SIB8__warningMessageSegmentType__cond SIB8__warningMessageSegmentType__Format.

Definition SIB8__warningMessageSegmentNumber__Format : T_Format Z SIB8__warningMessageSegmentNumber__cond :=
 ranged_int_format (0) (63) SIB8__warningMessageSegmentNumber__helper1 SIB8__warningMessageSegmentNumber__helper2.

Opaque SIB8__warningMessageSegmentNumber__cond SIB8__warningMessageSegmentNumber__Format.

Definition SIB8__dataCodingScheme__Format : T_Format SIB8__dataCodingScheme__Type SIB8__dataCodingScheme__cond := (* Eval compute in *) octet_string_fixed_format 1.
Opaque SIB8__dataCodingScheme__cond SIB8__dataCodingScheme__Format.


Definition SIB8__root_Format_Type := Eval cbn in seq_format_prod SIB8__root_list.
Definition SIB8__root_Format_list : SIB8__root_Format_Type :=
  (SIB8__messageIdentifier__Format, (SIB8__serialNumber__Format, (SIB8__warningMessageSegmentType__Format, (SIB8__warningMessageSegmentNumber__Format, (octet_string_nc__Format, (SIB8__dataCodingScheme__Format, (octet_string_nc__Format, (octet_string_nc__Format, unit_format)))))))).

Definition SIB8__ext_Format_Type := Eval cbn in get_formats SIB8__ext_list.
Definition SIB8__ext_Format_list : SIB8__ext_Format_Type :=
  unit__Format.

Definition SIB8__list_type : Set := (seq_type SIB8__root_list) * (seq_ext_type SIB8__ext_list).
Definition SIB8__list_cond (z : SIB8__list_type) : Prop :=
        (seq_cond SIB8__root_list (fst z)) /\ (seq_ext_cond SIB8__ext_list (snd z)).
Definition SIB8__list_format : T_Format SIB8__list_type SIB8__list_cond :=
 (* Eval compute in *) seq_ext_format SIB8__root_list SIB8__root_Format_list SIB8__ext_list SIB8__ext_Format_list.

Opaque SIB8__list_format.
Definition SIB8__F1 (z : SIB8__Type) : SIB8__list_type :=
  (((SIB8__messageIdentifier z, (SIB8__serialNumber z, (SIB8__warningMessageSegmentType z, (SIB8__warningMessageSegmentNumber z, (SIB8__warningMessageSegment z, (SIB8__dataCodingScheme z, (SIB8__warningAreaCoordinatesSegment z, (SIB8__lateNonCriticalExtension z, tt))))))))), (
tt)).
Definition SIB8__F2 (y : SIB8__list_type) : SIB8__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), _)=>
    make__SIB8__Type j0 j1 j2 j3 j4 j5 j6 j7
  end.
Definition SIB8__helper1 : (forall a : SIB8__Type, SIB8__cond a -> SIB8__list_cond (SIB8__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB8__helper2 : (forall a : SIB8__Type, SIB8__F2 (SIB8__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB8__helper3 : (forall b : SIB8__list_type, SIB8__list_cond b -> SIB8__cond (SIB8__F2 b) /\ SIB8__F1 (SIB8__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB8__cond, SIB8__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB8__Format : T_Format SIB8__Type SIB8__cond :=
 proj2_format SIB8__cond SIB8__list_format  SIB8__F1 SIB8__F2 SIB8__helper1 SIB8__helper2 SIB8__helper3.

Opaque SIB8__cond SIB8__Format.

