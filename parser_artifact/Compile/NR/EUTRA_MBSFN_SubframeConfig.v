Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Type : Set :=
 | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n1
 | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n2
 | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n4
 | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n8
 | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n16
 | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n32
.
Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__cond := (fun (_ : EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Type) => True).
Lemma EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__nat__helper.

Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1 t :=
  match t with
  | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n1 => 0
  | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n2 => 1
  | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n4 => 2
  | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n8 => 3
  | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n16 => 4
  | EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n32 => 5
  end.
Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F2 n :=
  match n with
  | 0 => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n1
  | 1 => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n2
  | 2 => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n4
  | 3 => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n8
  | 4 => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n16
  | 5 => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n32
  | _ => EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__n1
  end.
Lemma EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1F2 : forall x : EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Type, (EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1 x <= 5) /\ EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F2 (EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F2F1 : forall (y : nat) (H : y <= 5), EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1 (EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F2 y) = y. enum_solve H y. Qed.

Lemma EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__Type := Z.
Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__cond := (fun z => (0 <= z <= 7)%Z).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Type := bit_string_fixed.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 6 /\ bit_string_len_prop (fst z) (snd z)).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Type := bit_string_fixed.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 24 /\ bit_string_len_prop (fst z) (snd z)).

Inductive EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type : Set :=
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Type -> EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Type -> EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type
.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list : list typ := (
typ_cons EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__cond ::
typ_cons EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__cond ::
 nil).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond (c : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type) := 
  match c with
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame t => EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__cond t 
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames t => EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__cond t 
  end.

Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation1__len_helper1 : to_bit_sz (length EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation1__len_helper2 : 2 <= length2 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list.
 simpl. lia. Qed.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Type := bit_string_fixed.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Type := bit_string_fixed.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).

Inductive EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type : Set :=
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Type -> EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Type -> EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type
.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list : list typ := (
typ_cons EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__cond ::
typ_cons EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__cond ::
 nil).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond (c : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type) := 
  match c with
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame t => EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__cond t 
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames t => EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__cond t 
  end.

Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation2__len_helper1 : to_bit_sz (length EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation2__len_helper2 : 2 <= length2 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list.
 simpl. lia. Qed.
Record EUTRA_MBSFN_SubframeConfig__Type : Set :=
  make__EUTRA_MBSFN_SubframeConfig__Type {
    EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod : EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Type ;
    EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset : Z ;
    EUTRA_MBSFN_SubframeConfig__subframeAllocation1 : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type ;
    EUTRA_MBSFN_SubframeConfig__subframeAllocation2 : option EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type ;
}.
Definition EUTRA_MBSFN_SubframeConfig__root_list : list seq_elem := (
 Nor EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Type EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__cond ::
 Nor Z EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__cond ::
 Nor EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond ::
 Opt EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond ::
 nil).
Definition EUTRA_MBSFN_SubframeConfig__ext_list : list typ := (
  nil).
Definition EUTRA_MBSFN_SubframeConfig__cond (z : EUTRA_MBSFN_SubframeConfig__Type) := 
(  EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__cond (EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod z) /\
  EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__cond (EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset z) /\
  EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond (EUTRA_MBSFN_SubframeConfig__subframeAllocation1 z) /\
  opt_cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond (EUTRA_MBSFN_SubframeConfig__subframeAllocation2 z) /\
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
Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Format : T_Format EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__nat__Format EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1 EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F2 EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F1F2 EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__F2F1.

Opaque EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__cond EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Format.

Definition EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__Format : T_Format Z EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__cond :=
 ranged_int_format (0) (7) EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__helper1 EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__helper2.

Opaque EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__cond EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__Format.

Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Format : T_Format EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__cond := (* Eval compute in *) bit_string_fixed_format 6.
Opaque EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Format.

Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Format : T_Format EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__cond := (* Eval compute in *) bit_string_fixed_format 24.
Opaque EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Format.


Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format_Type := Eval cbn in get_formats EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format_list : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format_Type :=
  (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Format, (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Format, unit__Format)).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list__Format := Eval compute in choice_format EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list EUTRA_MBSFN_SubframeConfig__subframeAllocation1__len_helper1 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__len_helper2  EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format_list.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F1 (z : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type) : (choice EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list) :=
  match z with
   | EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame t => existT _ 0 t
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames t => existT _ 1 t
  end.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__g := (fun n => typ_set (get_nth_typ EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list n)).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F2 (y : choice EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list) : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__g n -> EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type) with
    | 0 => fun (t : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame__Type) => EUTRA_MBSFN_SubframeConfig__subframeAllocation1__oneFrame t 
    | 1 => fun (t : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames__Type) => EUTRA_MBSFN_SubframeConfig__subframeAllocation1__fourFrames t 
 | (S (S n0)) => (fun (x' : nat) (t'' : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type with end) n0
           end t0).

Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation1__helper2 :  forall (y : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type), EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond y -> choice_cond EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation1__helper3 :  forall (y : EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type), EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F2 (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation1__helper4 : (forall b : choice EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list, choice_cond EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list b -> EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F2 b) /\ EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F1 (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F1 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F2.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format : T_Format EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond :=
  (* Eval compute in *) proj2_format EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation1__list__Format EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F1 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__F2 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__helper2 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__helper3 EUTRA_MBSFN_SubframeConfig__subframeAllocation1__helper4.
Opaque EUTRA_MBSFN_SubframeConfig__subframeAllocation1__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format.

Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Format : T_Format EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Format.

Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Format : T_Format EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Format.


Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format_Type := Eval cbn in get_formats EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format_list : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format_Type :=
  (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Format, (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Format, unit__Format)).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list__Format := Eval compute in choice_format EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list EUTRA_MBSFN_SubframeConfig__subframeAllocation2__len_helper1 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__len_helper2  EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format_list.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F1 (z : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type) : (choice EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list) :=
  match z with
   | EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame t => existT _ 0 t
  | EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames t => existT _ 1 t
  end.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__g := (fun n => typ_set (get_nth_typ EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list n)).
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F2 (y : choice EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list) : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__g n -> EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type) with
    | 0 => fun (t : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame__Type) => EUTRA_MBSFN_SubframeConfig__subframeAllocation2__oneFrame t 
    | 1 => fun (t : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames__Type) => EUTRA_MBSFN_SubframeConfig__subframeAllocation2__fourFrames t 
 | (S (S n0)) => (fun (x' : nat) (t'' : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type with end) n0
           end t0).

Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation2__helper2 :  forall (y : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type), EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond y -> choice_cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation2__helper3 :  forall (y : EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type), EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F2 (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EUTRA_MBSFN_SubframeConfig__subframeAllocation2__helper4 : (forall b : choice EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list, choice_cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list b -> EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F2 b) /\ EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F1 (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F1 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F2.
Definition EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format : T_Format EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Type EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond :=
  (* Eval compute in *) proj2_format EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__list__Format EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F1 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__F2 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__helper2 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__helper3 EUTRA_MBSFN_SubframeConfig__subframeAllocation2__helper4.
Opaque EUTRA_MBSFN_SubframeConfig__subframeAllocation2__cond EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format.


Definition EUTRA_MBSFN_SubframeConfig__root_Format_Type := Eval cbn in seq_format_prod EUTRA_MBSFN_SubframeConfig__root_list.
Definition EUTRA_MBSFN_SubframeConfig__root_Format_list : EUTRA_MBSFN_SubframeConfig__root_Format_Type :=
  (EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod__Format, (EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset__Format, (EUTRA_MBSFN_SubframeConfig__subframeAllocation1__Format, (EUTRA_MBSFN_SubframeConfig__subframeAllocation2__Format, unit_format)))).

Definition EUTRA_MBSFN_SubframeConfig__ext_Format_Type := Eval cbn in get_formats EUTRA_MBSFN_SubframeConfig__ext_list.
Definition EUTRA_MBSFN_SubframeConfig__ext_Format_list : EUTRA_MBSFN_SubframeConfig__ext_Format_Type :=
  unit__Format.

Definition EUTRA_MBSFN_SubframeConfig__list_type : Set := (seq_type EUTRA_MBSFN_SubframeConfig__root_list) * (seq_ext_type EUTRA_MBSFN_SubframeConfig__ext_list).
Definition EUTRA_MBSFN_SubframeConfig__list_cond (z : EUTRA_MBSFN_SubframeConfig__list_type) : Prop :=
        (seq_cond EUTRA_MBSFN_SubframeConfig__root_list (fst z)) /\ (seq_ext_cond EUTRA_MBSFN_SubframeConfig__ext_list (snd z)).
Definition EUTRA_MBSFN_SubframeConfig__list_format : T_Format EUTRA_MBSFN_SubframeConfig__list_type EUTRA_MBSFN_SubframeConfig__list_cond :=
 (* Eval compute in *) seq_ext_format EUTRA_MBSFN_SubframeConfig__root_list EUTRA_MBSFN_SubframeConfig__root_Format_list EUTRA_MBSFN_SubframeConfig__ext_list EUTRA_MBSFN_SubframeConfig__ext_Format_list.

Opaque EUTRA_MBSFN_SubframeConfig__list_format.
Definition EUTRA_MBSFN_SubframeConfig__F1 (z : EUTRA_MBSFN_SubframeConfig__Type) : EUTRA_MBSFN_SubframeConfig__list_type :=
  (((EUTRA_MBSFN_SubframeConfig__radioframeAllocationPeriod z, (EUTRA_MBSFN_SubframeConfig__radioframeAllocationOffset z, (EUTRA_MBSFN_SubframeConfig__subframeAllocation1 z, (EUTRA_MBSFN_SubframeConfig__subframeAllocation2 z, tt))))), (
tt)).
Definition EUTRA_MBSFN_SubframeConfig__F2 (y : EUTRA_MBSFN_SubframeConfig__list_type) : EUTRA_MBSFN_SubframeConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__EUTRA_MBSFN_SubframeConfig__Type j0 j1 j2 j3
  end.
Definition EUTRA_MBSFN_SubframeConfig__helper1 : (forall a : EUTRA_MBSFN_SubframeConfig__Type, EUTRA_MBSFN_SubframeConfig__cond a -> EUTRA_MBSFN_SubframeConfig__list_cond (EUTRA_MBSFN_SubframeConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EUTRA_MBSFN_SubframeConfig__helper2 : (forall a : EUTRA_MBSFN_SubframeConfig__Type, EUTRA_MBSFN_SubframeConfig__F2 (EUTRA_MBSFN_SubframeConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EUTRA_MBSFN_SubframeConfig__helper3 : (forall b : EUTRA_MBSFN_SubframeConfig__list_type, EUTRA_MBSFN_SubframeConfig__list_cond b -> EUTRA_MBSFN_SubframeConfig__cond (EUTRA_MBSFN_SubframeConfig__F2 b) /\ EUTRA_MBSFN_SubframeConfig__F1 (EUTRA_MBSFN_SubframeConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EUTRA_MBSFN_SubframeConfig__cond, EUTRA_MBSFN_SubframeConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EUTRA_MBSFN_SubframeConfig__Format : T_Format EUTRA_MBSFN_SubframeConfig__Type EUTRA_MBSFN_SubframeConfig__cond :=
 proj2_format EUTRA_MBSFN_SubframeConfig__cond EUTRA_MBSFN_SubframeConfig__list_format  EUTRA_MBSFN_SubframeConfig__F1 EUTRA_MBSFN_SubframeConfig__F2 EUTRA_MBSFN_SubframeConfig__helper1 EUTRA_MBSFN_SubframeConfig__helper2 EUTRA_MBSFN_SubframeConfig__helper3.

Opaque EUTRA_MBSFN_SubframeConfig__cond EUTRA_MBSFN_SubframeConfig__Format.

