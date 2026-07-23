Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SIB_TypeInfo__type__root__Type : Set :=
 | SIB_TypeInfo__type__root__sibType2
 | SIB_TypeInfo__type__root__sibType3
 | SIB_TypeInfo__type__root__sibType4
 | SIB_TypeInfo__type__root__sibType5
 | SIB_TypeInfo__type__root__sibType6
 | SIB_TypeInfo__type__root__sibType7
 | SIB_TypeInfo__type__root__sibType8
 | SIB_TypeInfo__type__root__sibType9
 | SIB_TypeInfo__type__root__sibType10_v1610
 | SIB_TypeInfo__type__root__sibType11_v1610
 | SIB_TypeInfo__type__root__sibType12_v1610
 | SIB_TypeInfo__type__root__sibType13_v1610
 | SIB_TypeInfo__type__root__sibType14_v1610
 | SIB_TypeInfo__type__root__spare3
 | SIB_TypeInfo__type__root__spare2
 | SIB_TypeInfo__type__root__spare1
.
Definition SIB_TypeInfo__type__root__cond := (fun (_ : SIB_TypeInfo__type__root__Type) => True).
Lemma SIB_TypeInfo__type__root__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_TypeInfo__type__root__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB_TypeInfo__type__root__nat__helper.

Definition SIB_TypeInfo__type__root__F1 t :=
  match t with
  | SIB_TypeInfo__type__root__sibType2 => 0
  | SIB_TypeInfo__type__root__sibType3 => 1
  | SIB_TypeInfo__type__root__sibType4 => 2
  | SIB_TypeInfo__type__root__sibType5 => 3
  | SIB_TypeInfo__type__root__sibType6 => 4
  | SIB_TypeInfo__type__root__sibType7 => 5
  | SIB_TypeInfo__type__root__sibType8 => 6
  | SIB_TypeInfo__type__root__sibType9 => 7
  | SIB_TypeInfo__type__root__sibType10_v1610 => 8
  | SIB_TypeInfo__type__root__sibType11_v1610 => 9
  | SIB_TypeInfo__type__root__sibType12_v1610 => 10
  | SIB_TypeInfo__type__root__sibType13_v1610 => 11
  | SIB_TypeInfo__type__root__sibType14_v1610 => 12
  | SIB_TypeInfo__type__root__spare3 => 13
  | SIB_TypeInfo__type__root__spare2 => 14
  | SIB_TypeInfo__type__root__spare1 => 15
  end.
Definition SIB_TypeInfo__type__root__F2 n :=
  match n with
  | 0 => SIB_TypeInfo__type__root__sibType2
  | 1 => SIB_TypeInfo__type__root__sibType3
  | 2 => SIB_TypeInfo__type__root__sibType4
  | 3 => SIB_TypeInfo__type__root__sibType5
  | 4 => SIB_TypeInfo__type__root__sibType6
  | 5 => SIB_TypeInfo__type__root__sibType7
  | 6 => SIB_TypeInfo__type__root__sibType8
  | 7 => SIB_TypeInfo__type__root__sibType9
  | 8 => SIB_TypeInfo__type__root__sibType10_v1610
  | 9 => SIB_TypeInfo__type__root__sibType11_v1610
  | 10 => SIB_TypeInfo__type__root__sibType12_v1610
  | 11 => SIB_TypeInfo__type__root__sibType13_v1610
  | 12 => SIB_TypeInfo__type__root__sibType14_v1610
  | 13 => SIB_TypeInfo__type__root__spare3
  | 14 => SIB_TypeInfo__type__root__spare2
  | 15 => SIB_TypeInfo__type__root__spare1
  | _ => SIB_TypeInfo__type__root__sibType2
  end.
Lemma SIB_TypeInfo__type__root__F1F2 : forall x : SIB_TypeInfo__type__root__Type, (SIB_TypeInfo__type__root__F1 x <= 15) /\ SIB_TypeInfo__type__root__F2 (SIB_TypeInfo__type__root__F1 x) = x. imp_solve. Qed.
Lemma SIB_TypeInfo__type__root__F2F1 : forall (y : nat) (H : y <= 15), SIB_TypeInfo__type__root__F1 (SIB_TypeInfo__type__root__F2 y) = y. enum_solve H y. Qed.

Definition SIB_TypeInfo__type__ext__Type : Set := Empty_set.
Definition SIB_TypeInfo__type__ext__cond := (fun (_ : SIB_TypeInfo__type__ext__Type) => True).
Definition SIB_TypeInfo__type__Type : Set := SIB_TypeInfo__type__root__Type + SIB_TypeInfo__type__ext__Type.
Definition SIB_TypeInfo__type__cond := sum_cond SIB_TypeInfo__type__root__cond SIB_TypeInfo__type__ext__cond.

Lemma SIB_TypeInfo__valueTag__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SIB_TypeInfo__valueTag__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB_TypeInfo__valueTag__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB_TypeInfo__valueTag__Type := Z.
Definition SIB_TypeInfo__valueTag__cond := (fun z => (0 <= z <= 31)%Z).
Inductive SIB_TypeInfo__areaScope__Type : Set :=
 | SIB_TypeInfo__areaScope__true
.
Definition SIB_TypeInfo__areaScope__cond := (fun (_ : SIB_TypeInfo__areaScope__Type) => True).
Lemma SIB_TypeInfo__areaScope__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_TypeInfo__areaScope__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB_TypeInfo__areaScope__nat__helper.

Definition SIB_TypeInfo__areaScope__F1 t :=
  match t with
  | SIB_TypeInfo__areaScope__true => 0
  end.
Definition SIB_TypeInfo__areaScope__F2 n :=
  match n with
  | 0 => SIB_TypeInfo__areaScope__true
  | _ => SIB_TypeInfo__areaScope__true
  end.
Lemma SIB_TypeInfo__areaScope__F1F2 : forall x : SIB_TypeInfo__areaScope__Type, (SIB_TypeInfo__areaScope__F1 x <= 0) /\ SIB_TypeInfo__areaScope__F2 (SIB_TypeInfo__areaScope__F1 x) = x. imp_solve. Qed.
Lemma SIB_TypeInfo__areaScope__F2F1 : forall (y : nat) (H : y <= 0), SIB_TypeInfo__areaScope__F1 (SIB_TypeInfo__areaScope__F2 y) = y. enum_solve H y. Qed.

Record SIB_TypeInfo__Type : Set :=
  make__SIB_TypeInfo__Type {
    SIB_TypeInfo__type : SIB_TypeInfo__type__Type ;
    SIB_TypeInfo__valueTag : option Z ;
    SIB_TypeInfo__areaScope : option SIB_TypeInfo__areaScope__Type ;
}.
Definition SIB_TypeInfo__list := (
 Nor SIB_TypeInfo__type__Type SIB_TypeInfo__type__cond ::
 Opt Z SIB_TypeInfo__valueTag__cond ::
 Opt SIB_TypeInfo__areaScope__Type SIB_TypeInfo__areaScope__cond ::
 nil).
Definition SIB_TypeInfo__cond z := 
  SIB_TypeInfo__type__cond (SIB_TypeInfo__type z) /\
  opt_cond SIB_TypeInfo__valueTag__cond (SIB_TypeInfo__valueTag z) /\
  opt_cond SIB_TypeInfo__areaScope__cond (SIB_TypeInfo__areaScope z) /\
  True.


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
Definition SIB_TypeInfo__type__root__Format : T_Format SIB_TypeInfo__type__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format SIB_TypeInfo__type__root__nat__Format SIB_TypeInfo__type__root__F1 SIB_TypeInfo__type__root__F2 SIB_TypeInfo__type__root__F1F2 SIB_TypeInfo__type__root__F2F1.

Opaque SIB_TypeInfo__type__root__cond SIB_TypeInfo__type__root__Format.

Definition SIB_TypeInfo__type__ext__Format : T_Format SIB_TypeInfo__type__ext__Type SIB_TypeInfo__type__ext__cond := empty_format.

Opaque SIB_TypeInfo__type__ext__cond SIB_TypeInfo__type__ext__Format.

Definition SIB_TypeInfo__type__Format : T_Format SIB_TypeInfo__type__Type SIB_TypeInfo__type__cond := sum_format SIB_TypeInfo__type__root__Format SIB_TypeInfo__type__ext__Format.
Opaque SIB_TypeInfo__type__cond SIB_TypeInfo__type__Format.

Opaque SIB_TypeInfo__type__cond SIB_TypeInfo__type__Format.

Definition SIB_TypeInfo__valueTag__Format : T_Format Z SIB_TypeInfo__valueTag__cond :=
 ranged_int_format (0) (31) SIB_TypeInfo__valueTag__helper1 SIB_TypeInfo__valueTag__helper2.

Opaque SIB_TypeInfo__valueTag__cond SIB_TypeInfo__valueTag__Format.

Definition SIB_TypeInfo__areaScope__Format : T_Format SIB_TypeInfo__areaScope__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB_TypeInfo__areaScope__nat__Format SIB_TypeInfo__areaScope__F1 SIB_TypeInfo__areaScope__F2 SIB_TypeInfo__areaScope__F1F2 SIB_TypeInfo__areaScope__F2F1.

Opaque SIB_TypeInfo__areaScope__cond SIB_TypeInfo__areaScope__Format.


Definition SIB_TypeInfo__Format_Type := Eval cbn in seq_format_prod SIB_TypeInfo__list.
Definition SIB_TypeInfo__Format_list : SIB_TypeInfo__Format_Type :=
  (SIB_TypeInfo__type__Format, (SIB_TypeInfo__valueTag__Format, (SIB_TypeInfo__areaScope__Format, unit_format))).
Definition SIB_TypeInfo__list__Format := (*Eval compute in *) seq_format SIB_TypeInfo__list SIB_TypeInfo__Format_list.
Definition SIB_TypeInfo__F1 z :=
  (SIB_TypeInfo__type z, (SIB_TypeInfo__valueTag z, (SIB_TypeInfo__areaScope z, tt))).
Definition SIB_TypeInfo__F2 (y : seq_type SIB_TypeInfo__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SIB_TypeInfo__Type i0 i1 i2
  end.
Lemma SIB_TypeInfo__F1F2_cond (z : SIB_TypeInfo__Type)
  : SIB_TypeInfo__cond z ->
  (seq_cond SIB_TypeInfo__list (SIB_TypeInfo__F1 z)).
intro H. unfold SIB_TypeInfo__cond in H. simpl. auto. Qed.
Lemma SIB_TypeInfo__F1F2_cond2 (z : SIB_TypeInfo__Type)
 : SIB_TypeInfo__F2 (SIB_TypeInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB_TypeInfo__F2F1_cond (y : seq_type SIB_TypeInfo__list)
  : seq_cond SIB_TypeInfo__list y ->
 (SIB_TypeInfo__cond (SIB_TypeInfo__F2 y)) /\  SIB_TypeInfo__F1 (SIB_TypeInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB_TypeInfo__cond. simpl in *. auto.
 - simpl. unfold SIB_TypeInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB_TypeInfo__Format : T_Format SIB_TypeInfo__Type SIB_TypeInfo__cond :=
        proj2_format  SIB_TypeInfo__cond SIB_TypeInfo__list__Format
    SIB_TypeInfo__F1 SIB_TypeInfo__F2 SIB_TypeInfo__F1F2_cond  SIB_TypeInfo__F1F2_cond2 SIB_TypeInfo__F2F1_cond.
Opaque SIB_TypeInfo__cond SIB_TypeInfo__Format.

