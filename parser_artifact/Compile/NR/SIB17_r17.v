Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SIB17_r17__segmentNumber_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SIB17_r17__segmentNumber_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB17_r17__segmentNumber_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB17_r17__segmentNumber_r17__Type := Z.
Definition SIB17_r17__segmentNumber_r17__cond := (fun z => (0 <= z <= 63)%Z).
Inductive SIB17_r17__segmentType_r17__Type : Set :=
 | SIB17_r17__segmentType_r17__notLastSegment
 | SIB17_r17__segmentType_r17__lastSegment
.
Definition SIB17_r17__segmentType_r17__cond := (fun (_ : SIB17_r17__segmentType_r17__Type) => True).
Lemma SIB17_r17__segmentType_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB17_r17__segmentType_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SIB17_r17__segmentType_r17__nat__helper.

Definition SIB17_r17__segmentType_r17__F1 t :=
  match t with
  | SIB17_r17__segmentType_r17__notLastSegment => 0
  | SIB17_r17__segmentType_r17__lastSegment => 1
  end.
Definition SIB17_r17__segmentType_r17__F2 n :=
  match n with
  | 0 => SIB17_r17__segmentType_r17__notLastSegment
  | 1 => SIB17_r17__segmentType_r17__lastSegment
  | _ => SIB17_r17__segmentType_r17__notLastSegment
  end.
Lemma SIB17_r17__segmentType_r17__F1F2 : forall x : SIB17_r17__segmentType_r17__Type, (SIB17_r17__segmentType_r17__F1 x <= 1) /\ SIB17_r17__segmentType_r17__F2 (SIB17_r17__segmentType_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB17_r17__segmentType_r17__F2F1 : forall (y : nat) (H : y <= 1), SIB17_r17__segmentType_r17__F1 (SIB17_r17__segmentType_r17__F2 y) = y. enum_solve H y. Qed.

Record SIB17_r17__Type : Set :=
  make__SIB17_r17__Type {
    SIB17_r17__segmentNumber_r17 : Z ;
    SIB17_r17__segmentType_r17 : SIB17_r17__segmentType_r17__Type ;
    SIB17_r17__segmentContainer_r17 : octet_string ;
}.
Definition SIB17_r17__list := (
 Nor Z SIB17_r17__segmentNumber_r17__cond ::
 Nor SIB17_r17__segmentType_r17__Type SIB17_r17__segmentType_r17__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB17_r17__cond z := 
  SIB17_r17__segmentNumber_r17__cond (SIB17_r17__segmentNumber_r17 z) /\
  SIB17_r17__segmentType_r17__cond (SIB17_r17__segmentType_r17 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB17_r17__segmentContainer_r17 z) /\
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
Definition SIB17_r17__segmentNumber_r17__Format : T_Format Z SIB17_r17__segmentNumber_r17__cond :=
 ranged_int_format (0) (63) SIB17_r17__segmentNumber_r17__helper1 SIB17_r17__segmentNumber_r17__helper2.

Opaque SIB17_r17__segmentNumber_r17__cond SIB17_r17__segmentNumber_r17__Format.

Definition SIB17_r17__segmentType_r17__Format : T_Format SIB17_r17__segmentType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB17_r17__segmentType_r17__nat__Format SIB17_r17__segmentType_r17__F1 SIB17_r17__segmentType_r17__F2 SIB17_r17__segmentType_r17__F1F2 SIB17_r17__segmentType_r17__F2F1.

Opaque SIB17_r17__segmentType_r17__cond SIB17_r17__segmentType_r17__Format.


Definition SIB17_r17__Format_Type := Eval cbn in seq_format_prod SIB17_r17__list.
Definition SIB17_r17__Format_list : SIB17_r17__Format_Type :=
  (SIB17_r17__segmentNumber_r17__Format, (SIB17_r17__segmentType_r17__Format, (octet_string_nc__Format, unit_format))).
Definition SIB17_r17__list__Format := (*Eval compute in *) seq_format SIB17_r17__list SIB17_r17__Format_list.
Definition SIB17_r17__F1 z :=
  (SIB17_r17__segmentNumber_r17 z, (SIB17_r17__segmentType_r17 z, (SIB17_r17__segmentContainer_r17 z, tt))).
Definition SIB17_r17__F2 (y : seq_type SIB17_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SIB17_r17__Type i0 i1 i2
  end.
Lemma SIB17_r17__F1F2_cond (z : SIB17_r17__Type)
  : SIB17_r17__cond z ->
  (seq_cond SIB17_r17__list (SIB17_r17__F1 z)).
intro H. unfold SIB17_r17__cond in H. simpl. auto. Qed.
Lemma SIB17_r17__F1F2_cond2 (z : SIB17_r17__Type)
 : SIB17_r17__F2 (SIB17_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB17_r17__F2F1_cond (y : seq_type SIB17_r17__list)
  : seq_cond SIB17_r17__list y ->
 (SIB17_r17__cond (SIB17_r17__F2 y)) /\  SIB17_r17__F1 (SIB17_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB17_r17__cond. simpl in *. auto.
 - simpl. unfold SIB17_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB17_r17__Format : T_Format SIB17_r17__Type SIB17_r17__cond :=
        proj2_format  SIB17_r17__cond SIB17_r17__list__Format
    SIB17_r17__F1 SIB17_r17__F2 SIB17_r17__F1F2_cond  SIB17_r17__F1F2_cond2 SIB17_r17__F2F1_cond.
Opaque SIB17_r17__cond SIB17_r17__Format.

