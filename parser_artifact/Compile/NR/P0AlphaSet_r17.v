Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma P0AlphaSet_r17__p0_r17__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma P0AlphaSet_r17__p0_r17__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply P0AlphaSet_r17__p0_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition P0AlphaSet_r17__p0_r17__Type := Z.
Definition P0AlphaSet_r17__p0_r17__cond := (fun z => (-16 <= z <= 15)%Z).
Require Import NR.Alpha.

Opaque Alpha__cond Alpha__Format.

Inductive P0AlphaSet_r17__closedLoopIndex_r17__Type : Set :=
 | P0AlphaSet_r17__closedLoopIndex_r17__i0
 | P0AlphaSet_r17__closedLoopIndex_r17__i1
.
Definition P0AlphaSet_r17__closedLoopIndex_r17__cond := (fun (_ : P0AlphaSet_r17__closedLoopIndex_r17__Type) => True).
Lemma P0AlphaSet_r17__closedLoopIndex_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition P0AlphaSet_r17__closedLoopIndex_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 P0AlphaSet_r17__closedLoopIndex_r17__nat__helper.

Definition P0AlphaSet_r17__closedLoopIndex_r17__F1 t :=
  match t with
  | P0AlphaSet_r17__closedLoopIndex_r17__i0 => 0
  | P0AlphaSet_r17__closedLoopIndex_r17__i1 => 1
  end.
Definition P0AlphaSet_r17__closedLoopIndex_r17__F2 n :=
  match n with
  | 0 => P0AlphaSet_r17__closedLoopIndex_r17__i0
  | 1 => P0AlphaSet_r17__closedLoopIndex_r17__i1
  | _ => P0AlphaSet_r17__closedLoopIndex_r17__i0
  end.
Lemma P0AlphaSet_r17__closedLoopIndex_r17__F1F2 : forall x : P0AlphaSet_r17__closedLoopIndex_r17__Type, (P0AlphaSet_r17__closedLoopIndex_r17__F1 x <= 1) /\ P0AlphaSet_r17__closedLoopIndex_r17__F2 (P0AlphaSet_r17__closedLoopIndex_r17__F1 x) = x. imp_solve. Qed.
Lemma P0AlphaSet_r17__closedLoopIndex_r17__F2F1 : forall (y : nat) (H : y <= 1), P0AlphaSet_r17__closedLoopIndex_r17__F1 (P0AlphaSet_r17__closedLoopIndex_r17__F2 y) = y. enum_solve H y. Qed.

Record P0AlphaSet_r17__Type : Set :=
  make__P0AlphaSet_r17__Type {
    P0AlphaSet_r17__p0_r17 : option Z ;
    P0AlphaSet_r17__alpha_r17 : option Alpha__Type ;
    P0AlphaSet_r17__closedLoopIndex_r17 : P0AlphaSet_r17__closedLoopIndex_r17__Type ;
}.
Definition P0AlphaSet_r17__list := (
 Opt Z P0AlphaSet_r17__p0_r17__cond ::
 Opt Alpha__Type Alpha__cond ::
 Nor P0AlphaSet_r17__closedLoopIndex_r17__Type P0AlphaSet_r17__closedLoopIndex_r17__cond ::
 nil).
Definition P0AlphaSet_r17__cond z := 
  opt_cond P0AlphaSet_r17__p0_r17__cond (P0AlphaSet_r17__p0_r17 z) /\
  opt_cond Alpha__cond (P0AlphaSet_r17__alpha_r17 z) /\
  P0AlphaSet_r17__closedLoopIndex_r17__cond (P0AlphaSet_r17__closedLoopIndex_r17 z) /\
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
Definition P0AlphaSet_r17__p0_r17__Format : T_Format Z P0AlphaSet_r17__p0_r17__cond :=
 ranged_int_format (-16) (15) P0AlphaSet_r17__p0_r17__helper1 P0AlphaSet_r17__p0_r17__helper2.

Opaque P0AlphaSet_r17__p0_r17__cond P0AlphaSet_r17__p0_r17__Format.

Definition P0AlphaSet_r17__closedLoopIndex_r17__Format : T_Format P0AlphaSet_r17__closedLoopIndex_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format P0AlphaSet_r17__closedLoopIndex_r17__nat__Format P0AlphaSet_r17__closedLoopIndex_r17__F1 P0AlphaSet_r17__closedLoopIndex_r17__F2 P0AlphaSet_r17__closedLoopIndex_r17__F1F2 P0AlphaSet_r17__closedLoopIndex_r17__F2F1.

Opaque P0AlphaSet_r17__closedLoopIndex_r17__cond P0AlphaSet_r17__closedLoopIndex_r17__Format.


Definition P0AlphaSet_r17__Format_Type := Eval cbn in seq_format_prod P0AlphaSet_r17__list.
Definition P0AlphaSet_r17__Format_list : P0AlphaSet_r17__Format_Type :=
  (P0AlphaSet_r17__p0_r17__Format, (Alpha__Format, (P0AlphaSet_r17__closedLoopIndex_r17__Format, unit_format))).
Definition P0AlphaSet_r17__list__Format := (*Eval compute in *) seq_format P0AlphaSet_r17__list P0AlphaSet_r17__Format_list.
Definition P0AlphaSet_r17__F1 z :=
  (P0AlphaSet_r17__p0_r17 z, (P0AlphaSet_r17__alpha_r17 z, (P0AlphaSet_r17__closedLoopIndex_r17 z, tt))).
Definition P0AlphaSet_r17__F2 (y : seq_type P0AlphaSet_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__P0AlphaSet_r17__Type i0 i1 i2
  end.
Lemma P0AlphaSet_r17__F1F2_cond (z : P0AlphaSet_r17__Type)
  : P0AlphaSet_r17__cond z ->
  (seq_cond P0AlphaSet_r17__list (P0AlphaSet_r17__F1 z)).
intro H. unfold P0AlphaSet_r17__cond in H. simpl. auto. Qed.
Lemma P0AlphaSet_r17__F1F2_cond2 (z : P0AlphaSet_r17__Type)
 : P0AlphaSet_r17__F2 (P0AlphaSet_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma P0AlphaSet_r17__F2F1_cond (y : seq_type P0AlphaSet_r17__list)
  : seq_cond P0AlphaSet_r17__list y ->
 (P0AlphaSet_r17__cond (P0AlphaSet_r17__F2 y)) /\  P0AlphaSet_r17__F1 (P0AlphaSet_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold P0AlphaSet_r17__cond. simpl in *. auto.
 - simpl. unfold P0AlphaSet_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition P0AlphaSet_r17__Format : T_Format P0AlphaSet_r17__Type P0AlphaSet_r17__cond :=
        proj2_format  P0AlphaSet_r17__cond P0AlphaSet_r17__list__Format
    P0AlphaSet_r17__F1 P0AlphaSet_r17__F2 P0AlphaSet_r17__F1F2_cond  P0AlphaSet_r17__F1F2_cond2 P0AlphaSet_r17__F2F1_cond.
Opaque P0AlphaSet_r17__cond P0AlphaSet_r17__Format.

