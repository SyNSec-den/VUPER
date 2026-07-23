Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SIB12_r16__segmentNumber_r16__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SIB12_r16__segmentNumber_r16__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB12_r16__segmentNumber_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB12_r16__segmentNumber_r16__Type := Z.
Definition SIB12_r16__segmentNumber_r16__cond := (fun z => (0 <= z <= 63)%Z).
Inductive SIB12_r16__segmentType_r16__Type : Set :=
 | SIB12_r16__segmentType_r16__notLastSegment
 | SIB12_r16__segmentType_r16__lastSegment
.
Definition SIB12_r16__segmentType_r16__cond := (fun (_ : SIB12_r16__segmentType_r16__Type) => True).
Lemma SIB12_r16__segmentType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB12_r16__segmentType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SIB12_r16__segmentType_r16__nat__helper.

Definition SIB12_r16__segmentType_r16__F1 t :=
  match t with
  | SIB12_r16__segmentType_r16__notLastSegment => 0
  | SIB12_r16__segmentType_r16__lastSegment => 1
  end.
Definition SIB12_r16__segmentType_r16__F2 n :=
  match n with
  | 0 => SIB12_r16__segmentType_r16__notLastSegment
  | 1 => SIB12_r16__segmentType_r16__lastSegment
  | _ => SIB12_r16__segmentType_r16__notLastSegment
  end.
Lemma SIB12_r16__segmentType_r16__F1F2 : forall x : SIB12_r16__segmentType_r16__Type, (SIB12_r16__segmentType_r16__F1 x <= 1) /\ SIB12_r16__segmentType_r16__F2 (SIB12_r16__segmentType_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB12_r16__segmentType_r16__F2F1 : forall (y : nat) (H : y <= 1), SIB12_r16__segmentType_r16__F1 (SIB12_r16__segmentType_r16__F2 y) = y. enum_solve H y. Qed.

Record SIB12_r16__Type : Set :=
  make__SIB12_r16__Type {
    SIB12_r16__segmentNumber_r16 : Z ;
    SIB12_r16__segmentType_r16 : SIB12_r16__segmentType_r16__Type ;
    SIB12_r16__segmentContainer_r16 : octet_string ;
}.
Definition SIB12_r16__list := (
 Nor Z SIB12_r16__segmentNumber_r16__cond ::
 Nor SIB12_r16__segmentType_r16__Type SIB12_r16__segmentType_r16__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB12_r16__cond z := 
  SIB12_r16__segmentNumber_r16__cond (SIB12_r16__segmentNumber_r16 z) /\
  SIB12_r16__segmentType_r16__cond (SIB12_r16__segmentType_r16 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB12_r16__segmentContainer_r16 z) /\
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
Definition SIB12_r16__segmentNumber_r16__Format : T_Format Z SIB12_r16__segmentNumber_r16__cond :=
 ranged_int_format (0) (63) SIB12_r16__segmentNumber_r16__helper1 SIB12_r16__segmentNumber_r16__helper2.

Opaque SIB12_r16__segmentNumber_r16__cond SIB12_r16__segmentNumber_r16__Format.

Definition SIB12_r16__segmentType_r16__Format : T_Format SIB12_r16__segmentType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB12_r16__segmentType_r16__nat__Format SIB12_r16__segmentType_r16__F1 SIB12_r16__segmentType_r16__F2 SIB12_r16__segmentType_r16__F1F2 SIB12_r16__segmentType_r16__F2F1.

Opaque SIB12_r16__segmentType_r16__cond SIB12_r16__segmentType_r16__Format.


Definition SIB12_r16__Format_Type := Eval cbn in seq_format_prod SIB12_r16__list.
Definition SIB12_r16__Format_list : SIB12_r16__Format_Type :=
  (SIB12_r16__segmentNumber_r16__Format, (SIB12_r16__segmentType_r16__Format, (octet_string_nc__Format, unit_format))).
Definition SIB12_r16__list__Format := (*Eval compute in *) seq_format SIB12_r16__list SIB12_r16__Format_list.
Definition SIB12_r16__F1 z :=
  (SIB12_r16__segmentNumber_r16 z, (SIB12_r16__segmentType_r16 z, (SIB12_r16__segmentContainer_r16 z, tt))).
Definition SIB12_r16__F2 (y : seq_type SIB12_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SIB12_r16__Type i0 i1 i2
  end.
Lemma SIB12_r16__F1F2_cond (z : SIB12_r16__Type)
  : SIB12_r16__cond z ->
  (seq_cond SIB12_r16__list (SIB12_r16__F1 z)).
intro H. unfold SIB12_r16__cond in H. simpl. auto. Qed.
Lemma SIB12_r16__F1F2_cond2 (z : SIB12_r16__Type)
 : SIB12_r16__F2 (SIB12_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB12_r16__F2F1_cond (y : seq_type SIB12_r16__list)
  : seq_cond SIB12_r16__list y ->
 (SIB12_r16__cond (SIB12_r16__F2 y)) /\  SIB12_r16__F1 (SIB12_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB12_r16__cond. simpl in *. auto.
 - simpl. unfold SIB12_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB12_r16__Format : T_Format SIB12_r16__Type SIB12_r16__cond :=
        proj2_format  SIB12_r16__cond SIB12_r16__list__Format
    SIB12_r16__F1 SIB12_r16__F2 SIB12_r16__F1F2_cond  SIB12_r16__F1F2_cond2 SIB12_r16__F2F1_cond.
Opaque SIB12_r16__cond SIB12_r16__Format.

