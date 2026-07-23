Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUCCH_format4__nrofSymbols__helper1 : (4 <= 14)%Z.  lia. Qed.
Lemma PUCCH_format4__nrofSymbols__helper2 : to_bit_sz (Z.to_nat (14 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (14 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_format4__nrofSymbols__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_format4__nrofSymbols__Type := Z.
Definition PUCCH_format4__nrofSymbols__cond := (fun z => (4 <= z <= 14)%Z).
Inductive PUCCH_format4__occ_Length__Type : Set :=
 | PUCCH_format4__occ_Length__n2
 | PUCCH_format4__occ_Length__n4
.
Definition PUCCH_format4__occ_Length__cond := (fun (_ : PUCCH_format4__occ_Length__Type) => True).
Lemma PUCCH_format4__occ_Length__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_format4__occ_Length__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_format4__occ_Length__nat__helper.

Definition PUCCH_format4__occ_Length__F1 t :=
  match t with
  | PUCCH_format4__occ_Length__n2 => 0
  | PUCCH_format4__occ_Length__n4 => 1
  end.
Definition PUCCH_format4__occ_Length__F2 n :=
  match n with
  | 0 => PUCCH_format4__occ_Length__n2
  | 1 => PUCCH_format4__occ_Length__n4
  | _ => PUCCH_format4__occ_Length__n2
  end.
Lemma PUCCH_format4__occ_Length__F1F2 : forall x : PUCCH_format4__occ_Length__Type, (PUCCH_format4__occ_Length__F1 x <= 1) /\ PUCCH_format4__occ_Length__F2 (PUCCH_format4__occ_Length__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_format4__occ_Length__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_format4__occ_Length__F1 (PUCCH_format4__occ_Length__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_format4__occ_Index__Type : Set :=
 | PUCCH_format4__occ_Index__n0
 | PUCCH_format4__occ_Index__n1
 | PUCCH_format4__occ_Index__n2
 | PUCCH_format4__occ_Index__n3
.
Definition PUCCH_format4__occ_Index__cond := (fun (_ : PUCCH_format4__occ_Index__Type) => True).
Lemma PUCCH_format4__occ_Index__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_format4__occ_Index__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PUCCH_format4__occ_Index__nat__helper.

Definition PUCCH_format4__occ_Index__F1 t :=
  match t with
  | PUCCH_format4__occ_Index__n0 => 0
  | PUCCH_format4__occ_Index__n1 => 1
  | PUCCH_format4__occ_Index__n2 => 2
  | PUCCH_format4__occ_Index__n3 => 3
  end.
Definition PUCCH_format4__occ_Index__F2 n :=
  match n with
  | 0 => PUCCH_format4__occ_Index__n0
  | 1 => PUCCH_format4__occ_Index__n1
  | 2 => PUCCH_format4__occ_Index__n2
  | 3 => PUCCH_format4__occ_Index__n3
  | _ => PUCCH_format4__occ_Index__n0
  end.
Lemma PUCCH_format4__occ_Index__F1F2 : forall x : PUCCH_format4__occ_Index__Type, (PUCCH_format4__occ_Index__F1 x <= 3) /\ PUCCH_format4__occ_Index__F2 (PUCCH_format4__occ_Index__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_format4__occ_Index__F2F1 : forall (y : nat) (H : y <= 3), PUCCH_format4__occ_Index__F1 (PUCCH_format4__occ_Index__F2 y) = y. enum_solve H y. Qed.

Lemma PUCCH_format4__startingSymbolIndex__helper1 : (0 <= 10)%Z.  lia. Qed.
Lemma PUCCH_format4__startingSymbolIndex__helper2 : to_bit_sz (Z.to_nat (10 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_format4__startingSymbolIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_format4__startingSymbolIndex__Type := Z.
Definition PUCCH_format4__startingSymbolIndex__cond := (fun z => (0 <= z <= 10)%Z).
Record PUCCH_format4__Type : Set :=
  make__PUCCH_format4__Type {
    PUCCH_format4__nrofSymbols : Z ;
    PUCCH_format4__occ_Length : PUCCH_format4__occ_Length__Type ;
    PUCCH_format4__occ_Index : PUCCH_format4__occ_Index__Type ;
    PUCCH_format4__startingSymbolIndex : Z ;
}.
Definition PUCCH_format4__list := (
 Nor Z PUCCH_format4__nrofSymbols__cond ::
 Nor PUCCH_format4__occ_Length__Type PUCCH_format4__occ_Length__cond ::
 Nor PUCCH_format4__occ_Index__Type PUCCH_format4__occ_Index__cond ::
 Nor Z PUCCH_format4__startingSymbolIndex__cond ::
 nil).
Definition PUCCH_format4__cond z := 
  PUCCH_format4__nrofSymbols__cond (PUCCH_format4__nrofSymbols z) /\
  PUCCH_format4__occ_Length__cond (PUCCH_format4__occ_Length z) /\
  PUCCH_format4__occ_Index__cond (PUCCH_format4__occ_Index z) /\
  PUCCH_format4__startingSymbolIndex__cond (PUCCH_format4__startingSymbolIndex z) /\
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
Definition PUCCH_format4__nrofSymbols__Format : T_Format Z PUCCH_format4__nrofSymbols__cond :=
 ranged_int_format (4) (14) PUCCH_format4__nrofSymbols__helper1 PUCCH_format4__nrofSymbols__helper2.

Opaque PUCCH_format4__nrofSymbols__cond PUCCH_format4__nrofSymbols__Format.

Definition PUCCH_format4__occ_Length__Format : T_Format PUCCH_format4__occ_Length__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_format4__occ_Length__nat__Format PUCCH_format4__occ_Length__F1 PUCCH_format4__occ_Length__F2 PUCCH_format4__occ_Length__F1F2 PUCCH_format4__occ_Length__F2F1.

Opaque PUCCH_format4__occ_Length__cond PUCCH_format4__occ_Length__Format.

Definition PUCCH_format4__occ_Index__Format : T_Format PUCCH_format4__occ_Index__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_format4__occ_Index__nat__Format PUCCH_format4__occ_Index__F1 PUCCH_format4__occ_Index__F2 PUCCH_format4__occ_Index__F1F2 PUCCH_format4__occ_Index__F2F1.

Opaque PUCCH_format4__occ_Index__cond PUCCH_format4__occ_Index__Format.

Definition PUCCH_format4__startingSymbolIndex__Format : T_Format Z PUCCH_format4__startingSymbolIndex__cond :=
 ranged_int_format (0) (10) PUCCH_format4__startingSymbolIndex__helper1 PUCCH_format4__startingSymbolIndex__helper2.

Opaque PUCCH_format4__startingSymbolIndex__cond PUCCH_format4__startingSymbolIndex__Format.


Definition PUCCH_format4__Format_Type := Eval cbn in seq_format_prod PUCCH_format4__list.
Definition PUCCH_format4__Format_list : PUCCH_format4__Format_Type :=
  (PUCCH_format4__nrofSymbols__Format, (PUCCH_format4__occ_Length__Format, (PUCCH_format4__occ_Index__Format, (PUCCH_format4__startingSymbolIndex__Format, unit_format)))).
Definition PUCCH_format4__list__Format := (*Eval compute in *) seq_format PUCCH_format4__list PUCCH_format4__Format_list.
Definition PUCCH_format4__F1 z :=
  (PUCCH_format4__nrofSymbols z, (PUCCH_format4__occ_Length z, (PUCCH_format4__occ_Index z, (PUCCH_format4__startingSymbolIndex z, tt)))).
Definition PUCCH_format4__F2 (y : seq_type PUCCH_format4__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PUCCH_format4__Type i0 i1 i2 i3
  end.
Lemma PUCCH_format4__F1F2_cond (z : PUCCH_format4__Type)
  : PUCCH_format4__cond z ->
  (seq_cond PUCCH_format4__list (PUCCH_format4__F1 z)).
intro H. unfold PUCCH_format4__cond in H. simpl. auto. Qed.
Lemma PUCCH_format4__F1F2_cond2 (z : PUCCH_format4__Type)
 : PUCCH_format4__F2 (PUCCH_format4__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_format4__F2F1_cond (y : seq_type PUCCH_format4__list)
  : seq_cond PUCCH_format4__list y ->
 (PUCCH_format4__cond (PUCCH_format4__F2 y)) /\  PUCCH_format4__F1 (PUCCH_format4__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_format4__cond. simpl in *. auto.
 - simpl. unfold PUCCH_format4__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_format4__Format : T_Format PUCCH_format4__Type PUCCH_format4__cond :=
        proj2_format  PUCCH_format4__cond PUCCH_format4__list__Format
    PUCCH_format4__F1 PUCCH_format4__F2 PUCCH_format4__F1F2_cond  PUCCH_format4__F1F2_cond2 PUCCH_format4__F2F1_cond.
Opaque PUCCH_format4__cond PUCCH_format4__Format.

