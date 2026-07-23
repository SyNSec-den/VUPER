Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RateMatchPatternId.

Opaque RateMatchPatternId__cond RateMatchPatternId__Format.

Definition RateMatchPattern__patternType__bitmaps__resourceBlocks__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__resourceBlocks__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 275 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 14 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 28 /\ bit_string_len_prop (fst z) (snd z)).

Inductive RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type : Set :=
  | RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Type -> RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type
  | RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Type -> RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type
.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list : list typ := (
typ_cons RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Type RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Type RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__cond ::
 nil).
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond (c : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type) := 
  match c with
  | RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot t => RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__cond t 
  | RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots t => RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__cond t 
  end.

Lemma RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__len_helper1 : to_bit_sz (length RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__len_helper2 : 2 <= length2 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list.
 simpl. lia. Qed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 5 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 20 /\ bit_string_len_prop (fst z) (snd z)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Type := bit_string_fixed.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 40 /\ bit_string_len_prop (fst z) (snd z)).

Inductive RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type : Set :=
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40 : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Type -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type
.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list : list typ := (
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__cond ::
typ_cons RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__cond ::
 nil).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond (c : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type) := 
  match c with
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__cond t 
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__cond t 
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__cond t 
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__cond t 
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__cond t 
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__cond t 
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40 t => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__cond t 
  end.

Lemma RateMatchPattern__patternType__bitmaps__periodicityAndPattern__len_helper1 : to_bit_sz (length RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RateMatchPattern__patternType__bitmaps__periodicityAndPattern__len_helper2 : 2 <= length2 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list.
 simpl. lia. Qed.
Record RateMatchPattern__patternType__bitmaps__Type : Set :=
  make__RateMatchPattern__patternType__bitmaps__Type {
    RateMatchPattern__patternType__bitmaps__resourceBlocks : RateMatchPattern__patternType__bitmaps__resourceBlocks__Type ;
    RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type ;
    RateMatchPattern__patternType__bitmaps__periodicityAndPattern : option RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type ;
}.
Definition RateMatchPattern__patternType__bitmaps__root_list : list seq_elem := (
 Nor RateMatchPattern__patternType__bitmaps__resourceBlocks__Type RateMatchPattern__patternType__bitmaps__resourceBlocks__cond ::
 Nor RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond ::
 Opt RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond ::
 nil).
Definition RateMatchPattern__patternType__bitmaps__ext_list : list typ := (
  nil).
Definition RateMatchPattern__patternType__bitmaps__cond (z : RateMatchPattern__patternType__bitmaps__Type) := 
(  RateMatchPattern__patternType__bitmaps__resourceBlocks__cond (RateMatchPattern__patternType__bitmaps__resourceBlocks z) /\
  RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock z) /\
  opt_cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond (RateMatchPattern__patternType__bitmaps__periodicityAndPattern z) /\
  True) /\ 
(  True).

Require Import NR.ControlResourceSetId.

Opaque ControlResourceSetId__cond ControlResourceSetId__Format.


Inductive RateMatchPattern__patternType__Type : Set :=
  | RateMatchPattern__patternType__bitmaps : RateMatchPattern__patternType__bitmaps__Type -> RateMatchPattern__patternType__Type
  | RateMatchPattern__patternType__controlResourceSet : ControlResourceSetId__Type -> RateMatchPattern__patternType__Type
.
Definition RateMatchPattern__patternType__list : list typ := (
typ_cons RateMatchPattern__patternType__bitmaps__Type RateMatchPattern__patternType__bitmaps__cond ::
typ_cons ControlResourceSetId__Type ControlResourceSetId__cond ::
 nil).
Definition RateMatchPattern__patternType__cond (c : RateMatchPattern__patternType__Type) := 
  match c with
  | RateMatchPattern__patternType__bitmaps t => RateMatchPattern__patternType__bitmaps__cond t 
  | RateMatchPattern__patternType__controlResourceSet t => ControlResourceSetId__cond t 
  end.

Lemma RateMatchPattern__patternType__len_helper1 : to_bit_sz (length RateMatchPattern__patternType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RateMatchPattern__patternType__len_helper2 : 2 <= length2 RateMatchPattern__patternType__list.
 simpl. lia. Qed.
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Inductive RateMatchPattern__dummy__Type : Set :=
 | RateMatchPattern__dummy__dynamic
 | RateMatchPattern__dummy__semiStatic
.
Definition RateMatchPattern__dummy__cond := (fun (_ : RateMatchPattern__dummy__Type) => True).
Lemma RateMatchPattern__dummy__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RateMatchPattern__dummy__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RateMatchPattern__dummy__nat__helper.

Definition RateMatchPattern__dummy__F1 t :=
  match t with
  | RateMatchPattern__dummy__dynamic => 0
  | RateMatchPattern__dummy__semiStatic => 1
  end.
Definition RateMatchPattern__dummy__F2 n :=
  match n with
  | 0 => RateMatchPattern__dummy__dynamic
  | 1 => RateMatchPattern__dummy__semiStatic
  | _ => RateMatchPattern__dummy__dynamic
  end.
Lemma RateMatchPattern__dummy__F1F2 : forall x : RateMatchPattern__dummy__Type, (RateMatchPattern__dummy__F1 x <= 1) /\ RateMatchPattern__dummy__F2 (RateMatchPattern__dummy__F1 x) = x. imp_solve. Qed.
Lemma RateMatchPattern__dummy__F2F1 : forall (y : nat) (H : y <= 1), RateMatchPattern__dummy__F1 (RateMatchPattern__dummy__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ControlResourceSetId_r16.

Opaque ControlResourceSetId_r16__cond ControlResourceSetId_r16__Format.

Record RateMatchPattern__ext0O__Type : Set :=
  make__RateMatchPattern__ext0O__Type {
    RateMatchPattern__ext0O__controlResourceSet_r16 : option ControlResourceSetId_r16__Type ;
}.
Definition RateMatchPattern__ext0O__list := (
 Opt ControlResourceSetId_r16__Type ControlResourceSetId_r16__cond ::
 nil).
Definition RateMatchPattern__ext0O__cond z := 
  opt_cond ControlResourceSetId_r16__cond (RateMatchPattern__ext0O__controlResourceSet_r16 z) /\
  True.

Definition RateMatchPattern__ext0__Type := RateMatchPattern__ext0O__Type.
Definition RateMatchPattern__ext0__cond := RateMatchPattern__ext0O__cond.

Record RateMatchPattern__Type : Set :=
  make__RateMatchPattern__Type {
    RateMatchPattern__rateMatchPatternId : RateMatchPatternId__Type ;
    RateMatchPattern__patternType : RateMatchPattern__patternType__Type ;
    RateMatchPattern__subcarrierSpacing : option SubcarrierSpacing__Type ;
    RateMatchPattern__dummy : RateMatchPattern__dummy__Type ;
    RateMatchPattern__ext0 : option RateMatchPattern__ext0__Type ;
}.
Definition RateMatchPattern__root_list : list seq_elem := (
 Nor RateMatchPatternId__Type RateMatchPatternId__cond ::
 Nor RateMatchPattern__patternType__Type RateMatchPattern__patternType__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor RateMatchPattern__dummy__Type RateMatchPattern__dummy__cond ::
 nil).
Definition RateMatchPattern__ext_list : list typ := (
  typ_cons RateMatchPattern__ext0__Type RateMatchPattern__ext0__cond ::
  nil).
Definition RateMatchPattern__cond (z : RateMatchPattern__Type) := 
(  RateMatchPatternId__cond (RateMatchPattern__rateMatchPatternId z) /\
  RateMatchPattern__patternType__cond (RateMatchPattern__patternType z) /\
  opt_cond SubcarrierSpacing__cond (RateMatchPattern__subcarrierSpacing z) /\
  RateMatchPattern__dummy__cond (RateMatchPattern__dummy z) /\
  True) /\ 
(  opt_cond RateMatchPattern__ext0__cond (RateMatchPattern__ext0 z) /\
  True).


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
Definition RateMatchPattern__patternType__bitmaps__resourceBlocks__Format : T_Format RateMatchPattern__patternType__bitmaps__resourceBlocks__Type RateMatchPattern__patternType__bitmaps__resourceBlocks__cond := (* Eval compute in *) bit_string_fixed_format 275.
Opaque RateMatchPattern__patternType__bitmaps__resourceBlocks__cond RateMatchPattern__patternType__bitmaps__resourceBlocks__Format.

Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Format : T_Format RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Type RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__cond := (* Eval compute in *) bit_string_fixed_format 14.
Opaque RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__cond RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Format.

Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Format : T_Format RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Type RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__cond := (* Eval compute in *) bit_string_fixed_format 28.
Opaque RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__cond RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Format.


Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format_Type := Eval cbn in get_formats RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format_list : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format_Type :=
  (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Format, (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Format, unit__Format)).
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list__Format := Eval compute in choice_format RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__len_helper1 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__len_helper2  RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format_list.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F1 (z : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type) : (choice RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list) :=
  match z with
   | RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot t => existT _ 0 t
  | RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots t => existT _ 1 t
  end.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__g := (fun n => typ_set (get_nth_typ RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list n)).
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F2 (y : choice RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list) : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__g n -> RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type) with
    | 0 => fun (t : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot__Type) => RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__oneSlot t 
    | 1 => fun (t : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots__Type) => RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__twoSlots t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type with end) n0
           end t0).

Lemma RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__helper2 :  forall (y : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type), RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond y -> choice_cond RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__helper3 :  forall (y : RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type), RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F2 (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__helper4 : (forall b : choice RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list, choice_cond RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list b -> RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F2 b) /\ RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F1 (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F1 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F2.
Definition RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format : T_Format RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Type RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond :=
  (* Eval compute in *) proj2_format RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__list__Format RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F1 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__F2 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__helper2 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__helper3 RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__helper4.
Opaque RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__cond RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__cond := (* Eval compute in *) bit_string_fixed_format 5.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__cond := (* Eval compute in *) bit_string_fixed_format 20.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Format.

Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__cond := (* Eval compute in *) bit_string_fixed_format 40.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Format.


Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format_Type := Eval cbn in get_formats RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format_list : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format_Type :=
  (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Format, unit__Format))))))).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list__Format := Eval compute in choice_format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list RateMatchPattern__patternType__bitmaps__periodicityAndPattern__len_helper1 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__len_helper2  RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format_list.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F1 (z : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type) : (choice RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list) :=
  match z with
   | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2 t => existT _ 0 t
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4 t => existT _ 1 t
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5 t => existT _ 2 t
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8 t => existT _ 3 t
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10 t => existT _ 4 t
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20 t => existT _ 5 t
  | RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40 t => existT _ 6 t
  end.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__g := (fun n => typ_set (get_nth_typ RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list n)).
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F2 (y : choice RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list) : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__g n -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type) with
    | 0 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n2 t 
    | 1 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n4 t 
    | 2 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n5 t 
    | 3 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n8 t 
    | 4 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n10 t 
    | 5 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n20 t 
    | 6 => fun (t : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40__Type) => RateMatchPattern__patternType__bitmaps__periodicityAndPattern__n40 t 
 | (S (S (S (S (S (S (S n0))))))) => (fun (x' : nat) (t'' : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__g (S (S (S (S (S (S (S x')))))))) =>let t' :=
           eq_rect (get_nth_typ RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list (S (S (S (S (S (S (S x'))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list (S (S (S (S (S (S (S x')))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))) in match t' return RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type with end) n0
           end t0).

Lemma RateMatchPattern__patternType__bitmaps__periodicityAndPattern__helper2 :  forall (y : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type), RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond y -> choice_cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RateMatchPattern__patternType__bitmaps__periodicityAndPattern__helper3 :  forall (y : RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type), RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F2 (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RateMatchPattern__patternType__bitmaps__periodicityAndPattern__helper4 : (forall b : choice RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list, choice_cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list b -> RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F2 b) /\ RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F1 (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F1 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F2.
Definition RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format : T_Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Type RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond :=
  (* Eval compute in *) proj2_format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__list__Format RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F1 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__F2 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__helper2 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__helper3 RateMatchPattern__patternType__bitmaps__periodicityAndPattern__helper4.
Opaque RateMatchPattern__patternType__bitmaps__periodicityAndPattern__cond RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format.


Definition RateMatchPattern__patternType__bitmaps__root_Format_Type := Eval cbn in seq_format_prod RateMatchPattern__patternType__bitmaps__root_list.
Definition RateMatchPattern__patternType__bitmaps__root_Format_list : RateMatchPattern__patternType__bitmaps__root_Format_Type :=
  (RateMatchPattern__patternType__bitmaps__resourceBlocks__Format, (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock__Format, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern__Format, unit_format))).

Definition RateMatchPattern__patternType__bitmaps__ext_Format_Type := Eval cbn in get_formats RateMatchPattern__patternType__bitmaps__ext_list.
Definition RateMatchPattern__patternType__bitmaps__ext_Format_list : RateMatchPattern__patternType__bitmaps__ext_Format_Type :=
  unit__Format.

Definition RateMatchPattern__patternType__bitmaps__list_type : Set := (seq_type RateMatchPattern__patternType__bitmaps__root_list) * (seq_ext_type RateMatchPattern__patternType__bitmaps__ext_list).
Definition RateMatchPattern__patternType__bitmaps__list_cond (z : RateMatchPattern__patternType__bitmaps__list_type) : Prop :=
        (seq_cond RateMatchPattern__patternType__bitmaps__root_list (fst z)) /\ (seq_ext_cond RateMatchPattern__patternType__bitmaps__ext_list (snd z)).
Definition RateMatchPattern__patternType__bitmaps__list_format : T_Format RateMatchPattern__patternType__bitmaps__list_type RateMatchPattern__patternType__bitmaps__list_cond :=
 (* Eval compute in *) seq_ext_format RateMatchPattern__patternType__bitmaps__root_list RateMatchPattern__patternType__bitmaps__root_Format_list RateMatchPattern__patternType__bitmaps__ext_list RateMatchPattern__patternType__bitmaps__ext_Format_list.

Opaque RateMatchPattern__patternType__bitmaps__list_format.
Definition RateMatchPattern__patternType__bitmaps__F1 (z : RateMatchPattern__patternType__bitmaps__Type) : RateMatchPattern__patternType__bitmaps__list_type :=
  (((RateMatchPattern__patternType__bitmaps__resourceBlocks z, (RateMatchPattern__patternType__bitmaps__symbolsInResourceBlock z, (RateMatchPattern__patternType__bitmaps__periodicityAndPattern z, tt)))), (
tt)).
Definition RateMatchPattern__patternType__bitmaps__F2 (y : RateMatchPattern__patternType__bitmaps__list_type) : RateMatchPattern__patternType__bitmaps__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__RateMatchPattern__patternType__bitmaps__Type j0 j1 j2
  end.
Definition RateMatchPattern__patternType__bitmaps__helper1 : (forall a : RateMatchPattern__patternType__bitmaps__Type, RateMatchPattern__patternType__bitmaps__cond a -> RateMatchPattern__patternType__bitmaps__list_cond (RateMatchPattern__patternType__bitmaps__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RateMatchPattern__patternType__bitmaps__helper2 : (forall a : RateMatchPattern__patternType__bitmaps__Type, RateMatchPattern__patternType__bitmaps__F2 (RateMatchPattern__patternType__bitmaps__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RateMatchPattern__patternType__bitmaps__helper3 : (forall b : RateMatchPattern__patternType__bitmaps__list_type, RateMatchPattern__patternType__bitmaps__list_cond b -> RateMatchPattern__patternType__bitmaps__cond (RateMatchPattern__patternType__bitmaps__F2 b) /\ RateMatchPattern__patternType__bitmaps__F1 (RateMatchPattern__patternType__bitmaps__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RateMatchPattern__patternType__bitmaps__cond, RateMatchPattern__patternType__bitmaps__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RateMatchPattern__patternType__bitmaps__Format : T_Format RateMatchPattern__patternType__bitmaps__Type RateMatchPattern__patternType__bitmaps__cond :=
 proj2_format RateMatchPattern__patternType__bitmaps__cond RateMatchPattern__patternType__bitmaps__list_format  RateMatchPattern__patternType__bitmaps__F1 RateMatchPattern__patternType__bitmaps__F2 RateMatchPattern__patternType__bitmaps__helper1 RateMatchPattern__patternType__bitmaps__helper2 RateMatchPattern__patternType__bitmaps__helper3.

Opaque RateMatchPattern__patternType__bitmaps__cond RateMatchPattern__patternType__bitmaps__Format.


Definition RateMatchPattern__patternType__Format_Type := Eval cbn in get_formats RateMatchPattern__patternType__list.
Definition RateMatchPattern__patternType__Format_list : RateMatchPattern__patternType__Format_Type :=
  (RateMatchPattern__patternType__bitmaps__Format, (ControlResourceSetId__Format, unit__Format)).
Definition RateMatchPattern__patternType__list__Format := Eval compute in choice_format RateMatchPattern__patternType__list RateMatchPattern__patternType__len_helper1 RateMatchPattern__patternType__len_helper2  RateMatchPattern__patternType__Format_list.
Definition RateMatchPattern__patternType__F1 (z : RateMatchPattern__patternType__Type) : (choice RateMatchPattern__patternType__list) :=
  match z with
   | RateMatchPattern__patternType__bitmaps t => existT _ 0 t
  | RateMatchPattern__patternType__controlResourceSet t => existT _ 1 t
  end.
Definition RateMatchPattern__patternType__g := (fun n => typ_set (get_nth_typ RateMatchPattern__patternType__list n)).
Definition RateMatchPattern__patternType__F2 (y : choice RateMatchPattern__patternType__list) : RateMatchPattern__patternType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RateMatchPattern__patternType__g n -> RateMatchPattern__patternType__Type) with
    | 0 => fun (t : RateMatchPattern__patternType__bitmaps__Type) => RateMatchPattern__patternType__bitmaps t 
    | 1 => fun (t : ControlResourceSetId__Type) => RateMatchPattern__patternType__controlResourceSet t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RateMatchPattern__patternType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RateMatchPattern__patternType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RateMatchPattern__patternType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RateMatchPattern__patternType__Type with end) n0
           end t0).

Lemma RateMatchPattern__patternType__helper2 :  forall (y : RateMatchPattern__patternType__Type), RateMatchPattern__patternType__cond y -> choice_cond RateMatchPattern__patternType__list (RateMatchPattern__patternType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RateMatchPattern__patternType__helper3 :  forall (y : RateMatchPattern__patternType__Type), RateMatchPattern__patternType__F2 (RateMatchPattern__patternType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RateMatchPattern__patternType__helper4 : (forall b : choice RateMatchPattern__patternType__list, choice_cond RateMatchPattern__patternType__list b -> RateMatchPattern__patternType__cond (RateMatchPattern__patternType__F2 b) /\ RateMatchPattern__patternType__F1 (RateMatchPattern__patternType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RateMatchPattern__patternType__F1 RateMatchPattern__patternType__F2.
Definition RateMatchPattern__patternType__Format : T_Format RateMatchPattern__patternType__Type RateMatchPattern__patternType__cond :=
  (* Eval compute in *) proj2_format RateMatchPattern__patternType__cond RateMatchPattern__patternType__list__Format RateMatchPattern__patternType__F1 RateMatchPattern__patternType__F2 RateMatchPattern__patternType__helper2 RateMatchPattern__patternType__helper3 RateMatchPattern__patternType__helper4.
Opaque RateMatchPattern__patternType__cond RateMatchPattern__patternType__Format.

Definition RateMatchPattern__dummy__Format : T_Format RateMatchPattern__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RateMatchPattern__dummy__nat__Format RateMatchPattern__dummy__F1 RateMatchPattern__dummy__F2 RateMatchPattern__dummy__F1F2 RateMatchPattern__dummy__F2F1.

Opaque RateMatchPattern__dummy__cond RateMatchPattern__dummy__Format.


Definition RateMatchPattern__ext0O__Format_Type := Eval cbn in seq_format_prod RateMatchPattern__ext0O__list.
Definition RateMatchPattern__ext0O__Format_list : RateMatchPattern__ext0O__Format_Type :=
  (ControlResourceSetId_r16__Format, unit_format).
Definition RateMatchPattern__ext0O__list__Format := (*Eval compute in *) seq_format RateMatchPattern__ext0O__list RateMatchPattern__ext0O__Format_list.
Definition RateMatchPattern__ext0O__F1 z :=
  (RateMatchPattern__ext0O__controlResourceSet_r16 z, tt).
Definition RateMatchPattern__ext0O__F2 (y : seq_type RateMatchPattern__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RateMatchPattern__ext0O__Type i0
  end.
Lemma RateMatchPattern__ext0O__F1F2_cond (z : RateMatchPattern__ext0O__Type)
  : RateMatchPattern__ext0O__cond z ->
  (seq_cond RateMatchPattern__ext0O__list (RateMatchPattern__ext0O__F1 z)).
intro H. unfold RateMatchPattern__ext0O__cond in H. simpl. auto. Qed.
Lemma RateMatchPattern__ext0O__F1F2_cond2 (z : RateMatchPattern__ext0O__Type)
 : RateMatchPattern__ext0O__F2 (RateMatchPattern__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RateMatchPattern__ext0O__F2F1_cond (y : seq_type RateMatchPattern__ext0O__list)
  : seq_cond RateMatchPattern__ext0O__list y ->
 (RateMatchPattern__ext0O__cond (RateMatchPattern__ext0O__F2 y)) /\  RateMatchPattern__ext0O__F1 (RateMatchPattern__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RateMatchPattern__ext0O__cond. simpl in *. auto.
 - simpl. unfold RateMatchPattern__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RateMatchPattern__ext0O__Format : T_Format RateMatchPattern__ext0O__Type RateMatchPattern__ext0O__cond :=
        proj2_format  RateMatchPattern__ext0O__cond RateMatchPattern__ext0O__list__Format
    RateMatchPattern__ext0O__F1 RateMatchPattern__ext0O__F2 RateMatchPattern__ext0O__F1F2_cond  RateMatchPattern__ext0O__F1F2_cond2 RateMatchPattern__ext0O__F2F1_cond.
Opaque RateMatchPattern__ext0O__cond RateMatchPattern__ext0O__Format.

Definition RateMatchPattern__ext0__check_all_none (b : RateMatchPattern__ext0O__Type) : bool :=
match b with 
  | make__RateMatchPattern__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RateMatchPattern__ext0__Format : T_Format RateMatchPattern__ext0__Type RateMatchPattern__ext0__cond :=
  restrict_add_format RateMatchPattern__ext0__check_all_none RateMatchPattern__ext0O__Format.

Opaque RateMatchPattern__ext0__cond RateMatchPattern__ext0__Format.


Definition RateMatchPattern__root_Format_Type := Eval cbn in seq_format_prod RateMatchPattern__root_list.
Definition RateMatchPattern__root_Format_list : RateMatchPattern__root_Format_Type :=
  (RateMatchPatternId__Format, (RateMatchPattern__patternType__Format, (SubcarrierSpacing__Format, (RateMatchPattern__dummy__Format, unit_format)))).

Definition RateMatchPattern__ext_Format_Type := Eval cbn in get_formats RateMatchPattern__ext_list.
Definition RateMatchPattern__ext_Format_list : RateMatchPattern__ext_Format_Type :=
  (RateMatchPattern__ext0__Format, unit__Format).

Definition RateMatchPattern__list_type : Set := (seq_type RateMatchPattern__root_list) * (seq_ext_type RateMatchPattern__ext_list).
Definition RateMatchPattern__list_cond (z : RateMatchPattern__list_type) : Prop :=
        (seq_cond RateMatchPattern__root_list (fst z)) /\ (seq_ext_cond RateMatchPattern__ext_list (snd z)).
Definition RateMatchPattern__list_format : T_Format RateMatchPattern__list_type RateMatchPattern__list_cond :=
 (* Eval compute in *) seq_ext_format RateMatchPattern__root_list RateMatchPattern__root_Format_list RateMatchPattern__ext_list RateMatchPattern__ext_Format_list.

Opaque RateMatchPattern__list_format.
Definition RateMatchPattern__F1 (z : RateMatchPattern__Type) : RateMatchPattern__list_type :=
  (((RateMatchPattern__rateMatchPatternId z, (RateMatchPattern__patternType z, (RateMatchPattern__subcarrierSpacing z, (RateMatchPattern__dummy z, tt))))), (
(RateMatchPattern__ext0 z, tt))).
Definition RateMatchPattern__F2 (y : RateMatchPattern__list_type) : RateMatchPattern__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__RateMatchPattern__Type j0 j1 j2 j3 i0
  end.
Definition RateMatchPattern__helper1 : (forall a : RateMatchPattern__Type, RateMatchPattern__cond a -> RateMatchPattern__list_cond (RateMatchPattern__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RateMatchPattern__helper2 : (forall a : RateMatchPattern__Type, RateMatchPattern__F2 (RateMatchPattern__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RateMatchPattern__helper3 : (forall b : RateMatchPattern__list_type, RateMatchPattern__list_cond b -> RateMatchPattern__cond (RateMatchPattern__F2 b) /\ RateMatchPattern__F1 (RateMatchPattern__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RateMatchPattern__cond, RateMatchPattern__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RateMatchPattern__Format : T_Format RateMatchPattern__Type RateMatchPattern__cond :=
 proj2_format RateMatchPattern__cond RateMatchPattern__list_format  RateMatchPattern__F1 RateMatchPattern__F2 RateMatchPattern__helper1 RateMatchPattern__helper2 RateMatchPattern__helper3.

Opaque RateMatchPattern__cond RateMatchPattern__Format.

