Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PDSCH_HARQ_ACK_EnhType3Index_r17.

Opaque PDSCH_HARQ_ACK_EnhType3Index_r17__cond PDSCH_HARQ_ACK_EnhType3Index_r17__Format.

Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__Type := Z.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__cond := (fun z => (0 <= z <= 1)%Z).
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Type := list Z.

Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__cond (z : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__cond z) .

Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__Type := bit_string_fixed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Type := list PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__Type.

Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__cond (z : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__cond z) .


Inductive PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type : Set :=
  | PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Type -> PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type
  | PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Type -> PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type
.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list : list typ := (
typ_cons PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__cond ::
typ_cons PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__cond ::
 nil).
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond (c : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type) := 
  match c with
  | PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC t => PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__cond t 
  | PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ t => PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__cond t 
  end.

Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__len_helper1 : to_bit_sz (length PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__len_helper2 : 2 <= length2 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list.
 simpl. lia. Qed.
Inductive PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Type : Set :=
 | PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__true
.
Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__cond := (fun (_ : PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Type) => True).
Lemma PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__nat__helper.

Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1 t :=
  match t with
  | PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__true => 0
  end.
Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F2 n :=
  match n with
  | 0 => PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__true
  | _ => PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__true
  end.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1F2 : forall x : PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Type, (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1 x <= 0) /\ PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F2 (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1 (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Type : Set :=
 | PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__true
.
Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__cond := (fun (_ : PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Type) => True).
Lemma PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__nat__helper.

Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1 t :=
  match t with
  | PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__true => 0
  end.
Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F2 n :=
  match n with
  | 0 => PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__true
  | _ => PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__true
  end.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1F2 : forall x : PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Type, (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1 x <= 0) /\ PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F2 (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1 (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_HARQ_ACK_EnhType3_r17__Type : Set :=
  make__PDSCH_HARQ_ACK_EnhType3_r17__Type {
    PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3Index_r17 : PDSCH_HARQ_ACK_EnhType3Index_r17__Type ;
    PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17 : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type ;
    PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17 : option PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Type ;
    PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17 : option PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Type ;
}.
Definition PDSCH_HARQ_ACK_EnhType3_r17__root_list : list seq_elem := (
 Nor PDSCH_HARQ_ACK_EnhType3Index_r17__Type PDSCH_HARQ_ACK_EnhType3Index_r17__cond ::
 Nor PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond ::
 Opt PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Type PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__cond ::
 Opt PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Type PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__cond ::
 nil).
Definition PDSCH_HARQ_ACK_EnhType3_r17__ext_list : list typ := (
  nil).
Definition PDSCH_HARQ_ACK_EnhType3_r17__cond (z : PDSCH_HARQ_ACK_EnhType3_r17__Type) := 
(  PDSCH_HARQ_ACK_EnhType3Index_r17__cond (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3Index_r17 z) /\
  PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17 z) /\
  opt_cond PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__cond (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17 z) /\
  opt_cond PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__cond (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17 z) /\
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
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__Format : T_Format Z PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__cond :=
 ranged_int_format (0) (1) PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__helper1 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__helper2.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__Format.

Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__cond := seq_of_format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__seq_of__Format 1 maxNrofServingCells PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__helper1 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__helper2.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Format.

Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__Format.

Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__cond := seq_of_format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__seq_of__Format 1 maxNrofServingCells PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__helper1 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__helper2.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Format.


Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format_Type := Eval cbn in get_formats PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format_list : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format_Type :=
  (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Format, (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Format, unit__Format)).
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list__Format := Eval compute in choice_format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__len_helper1 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__len_helper2  PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format_list.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F1 (z : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type) : (choice PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list) :=
  match z with
   | PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC t => existT _ 0 t
  | PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ t => existT _ 1 t
  end.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__g := (fun n => typ_set (get_nth_typ PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list n)).
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F2 (y : choice PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list) : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__g n -> PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type) with
    | 0 => fun (t : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC__Type) => PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perCC t 
    | 1 => fun (t : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ__Type) => PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__perHARQ t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type with end) n0
           end t0).

Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__helper2 :  forall (y : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type), PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond y -> choice_cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__helper3 :  forall (y : PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type), PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F2 (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__helper4 : (forall b : choice PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list, choice_cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list b -> PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F2 b) /\ PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F1 (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F1 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F2.
Definition PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Type PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond :=
  (* Eval compute in *) proj2_format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__list__Format PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F1 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__F2 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__helper2 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__helper3 PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__helper4.
Opaque PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format.

Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__nat__Format PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F2 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F1F2 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__F2F1.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Format.

Definition PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__nat__Format PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F2 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F1F2 PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__F2F1.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Format.


Definition PDSCH_HARQ_ACK_EnhType3_r17__root_Format_Type := Eval cbn in seq_format_prod PDSCH_HARQ_ACK_EnhType3_r17__root_list.
Definition PDSCH_HARQ_ACK_EnhType3_r17__root_Format_list : PDSCH_HARQ_ACK_EnhType3_r17__root_Format_Type :=
  (PDSCH_HARQ_ACK_EnhType3Index_r17__Format, (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17__Format, (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17__Format, (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17__Format, unit_format)))).

Definition PDSCH_HARQ_ACK_EnhType3_r17__ext_Format_Type := Eval cbn in get_formats PDSCH_HARQ_ACK_EnhType3_r17__ext_list.
Definition PDSCH_HARQ_ACK_EnhType3_r17__ext_Format_list : PDSCH_HARQ_ACK_EnhType3_r17__ext_Format_Type :=
  unit__Format.

Definition PDSCH_HARQ_ACK_EnhType3_r17__list_type : Set := (seq_type PDSCH_HARQ_ACK_EnhType3_r17__root_list) * (seq_ext_type PDSCH_HARQ_ACK_EnhType3_r17__ext_list).
Definition PDSCH_HARQ_ACK_EnhType3_r17__list_cond (z : PDSCH_HARQ_ACK_EnhType3_r17__list_type) : Prop :=
        (seq_cond PDSCH_HARQ_ACK_EnhType3_r17__root_list (fst z)) /\ (seq_ext_cond PDSCH_HARQ_ACK_EnhType3_r17__ext_list (snd z)).
Definition PDSCH_HARQ_ACK_EnhType3_r17__list_format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__list_type PDSCH_HARQ_ACK_EnhType3_r17__list_cond :=
 (* Eval compute in *) seq_ext_format PDSCH_HARQ_ACK_EnhType3_r17__root_list PDSCH_HARQ_ACK_EnhType3_r17__root_Format_list PDSCH_HARQ_ACK_EnhType3_r17__ext_list PDSCH_HARQ_ACK_EnhType3_r17__ext_Format_list.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__list_format.
Definition PDSCH_HARQ_ACK_EnhType3_r17__F1 (z : PDSCH_HARQ_ACK_EnhType3_r17__Type) : PDSCH_HARQ_ACK_EnhType3_r17__list_type :=
  (((PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3Index_r17 z, (PDSCH_HARQ_ACK_EnhType3_r17__applicable_r17 z, (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3NDI_r17 z, (PDSCH_HARQ_ACK_EnhType3_r17__pdsch_HARQ_ACK_EnhType3CBG_r17 z, tt))))), (
tt)).
Definition PDSCH_HARQ_ACK_EnhType3_r17__F2 (y : PDSCH_HARQ_ACK_EnhType3_r17__list_type) : PDSCH_HARQ_ACK_EnhType3_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__PDSCH_HARQ_ACK_EnhType3_r17__Type j0 j1 j2 j3
  end.
Definition PDSCH_HARQ_ACK_EnhType3_r17__helper1 : (forall a : PDSCH_HARQ_ACK_EnhType3_r17__Type, PDSCH_HARQ_ACK_EnhType3_r17__cond a -> PDSCH_HARQ_ACK_EnhType3_r17__list_cond (PDSCH_HARQ_ACK_EnhType3_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__helper2 : (forall a : PDSCH_HARQ_ACK_EnhType3_r17__Type, PDSCH_HARQ_ACK_EnhType3_r17__F2 (PDSCH_HARQ_ACK_EnhType3_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__helper3 : (forall b : PDSCH_HARQ_ACK_EnhType3_r17__list_type, PDSCH_HARQ_ACK_EnhType3_r17__list_cond b -> PDSCH_HARQ_ACK_EnhType3_r17__cond (PDSCH_HARQ_ACK_EnhType3_r17__F2 b) /\ PDSCH_HARQ_ACK_EnhType3_r17__F1 (PDSCH_HARQ_ACK_EnhType3_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDSCH_HARQ_ACK_EnhType3_r17__cond, PDSCH_HARQ_ACK_EnhType3_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDSCH_HARQ_ACK_EnhType3_r17__Format : T_Format PDSCH_HARQ_ACK_EnhType3_r17__Type PDSCH_HARQ_ACK_EnhType3_r17__cond :=
 proj2_format PDSCH_HARQ_ACK_EnhType3_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__list_format  PDSCH_HARQ_ACK_EnhType3_r17__F1 PDSCH_HARQ_ACK_EnhType3_r17__F2 PDSCH_HARQ_ACK_EnhType3_r17__helper1 PDSCH_HARQ_ACK_EnhType3_r17__helper2 PDSCH_HARQ_ACK_EnhType3_r17__helper3.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__Format.

