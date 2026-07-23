Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__helper1 : (1 <= 319)%Z.  lia. Qed.
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__helper2 : to_bit_sz (Z.to_nat (319 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__Type := Z.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__cond := (fun z => (1 <= z <= 319)%Z).
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__helper1 : (1 <= 319)%Z.  lia. Qed.
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__helper2 : to_bit_sz (Z.to_nat (319 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__Type := Z.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__cond := (fun z => (1 <= z <= 319)%Z).
Record CG_COT_Sharing_r17__cot_Sharing_r17__Type : Set :=
  make__CG_COT_Sharing_r17__cot_Sharing_r17__Type {
    CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17 : Z ;
    CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17 : Z ;
}.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__list := (
 Nor Z CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__cond ::
 Nor Z CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__cond ::
 nil).
Definition CG_COT_Sharing_r17__cot_Sharing_r17__cond z := 
  CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__cond (CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17 z) /\
  CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__cond (CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17 z) /\
  True.


Inductive CG_COT_Sharing_r17__Type : Set :=
  | CG_COT_Sharing_r17__noCOT_Sharing_r17 : unit -> CG_COT_Sharing_r17__Type
  | CG_COT_Sharing_r17__cot_Sharing_r17 : CG_COT_Sharing_r17__cot_Sharing_r17__Type -> CG_COT_Sharing_r17__Type
.
Definition CG_COT_Sharing_r17__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons CG_COT_Sharing_r17__cot_Sharing_r17__Type CG_COT_Sharing_r17__cot_Sharing_r17__cond ::
 nil).
Definition CG_COT_Sharing_r17__cond (c : CG_COT_Sharing_r17__Type) := 
  match c with
  | CG_COT_Sharing_r17__noCOT_Sharing_r17 t => (fun _ => True) t 
  | CG_COT_Sharing_r17__cot_Sharing_r17 t => CG_COT_Sharing_r17__cot_Sharing_r17__cond t 
  end.

Lemma CG_COT_Sharing_r17__len_helper1 : to_bit_sz (length CG_COT_Sharing_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CG_COT_Sharing_r17__len_helper2 : 2 <= length2 CG_COT_Sharing_r17__list.
 simpl. lia. Qed.

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
Definition CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__Format : T_Format Z CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__cond :=
 ranged_int_format (1) (319) CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__helper1 CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__helper2.

Opaque CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__cond CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__Format.

Definition CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__Format : T_Format Z CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__cond :=
 ranged_int_format (1) (319) CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__helper1 CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__helper2.

Opaque CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__cond CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__Format.


Definition CG_COT_Sharing_r17__cot_Sharing_r17__Format_Type := Eval cbn in seq_format_prod CG_COT_Sharing_r17__cot_Sharing_r17__list.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__Format_list : CG_COT_Sharing_r17__cot_Sharing_r17__Format_Type :=
  (CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17__Format, (CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17__Format, unit_format)).
Definition CG_COT_Sharing_r17__cot_Sharing_r17__list__Format := (*Eval compute in *) seq_format CG_COT_Sharing_r17__cot_Sharing_r17__list CG_COT_Sharing_r17__cot_Sharing_r17__Format_list.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__F1 z :=
  (CG_COT_Sharing_r17__cot_Sharing_r17__duration_r17 z, (CG_COT_Sharing_r17__cot_Sharing_r17__offset_r17 z, tt)).
Definition CG_COT_Sharing_r17__cot_Sharing_r17__F2 (y : seq_type CG_COT_Sharing_r17__cot_Sharing_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_COT_Sharing_r17__cot_Sharing_r17__Type i0 i1
  end.
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__F1F2_cond (z : CG_COT_Sharing_r17__cot_Sharing_r17__Type)
  : CG_COT_Sharing_r17__cot_Sharing_r17__cond z ->
  (seq_cond CG_COT_Sharing_r17__cot_Sharing_r17__list (CG_COT_Sharing_r17__cot_Sharing_r17__F1 z)).
intro H. unfold CG_COT_Sharing_r17__cot_Sharing_r17__cond in H. simpl. auto. Qed.
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__F1F2_cond2 (z : CG_COT_Sharing_r17__cot_Sharing_r17__Type)
 : CG_COT_Sharing_r17__cot_Sharing_r17__F2 (CG_COT_Sharing_r17__cot_Sharing_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_COT_Sharing_r17__cot_Sharing_r17__F2F1_cond (y : seq_type CG_COT_Sharing_r17__cot_Sharing_r17__list)
  : seq_cond CG_COT_Sharing_r17__cot_Sharing_r17__list y ->
 (CG_COT_Sharing_r17__cot_Sharing_r17__cond (CG_COT_Sharing_r17__cot_Sharing_r17__F2 y)) /\  CG_COT_Sharing_r17__cot_Sharing_r17__F1 (CG_COT_Sharing_r17__cot_Sharing_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_COT_Sharing_r17__cot_Sharing_r17__cond. simpl in *. auto.
 - simpl. unfold CG_COT_Sharing_r17__cot_Sharing_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_COT_Sharing_r17__cot_Sharing_r17__Format : T_Format CG_COT_Sharing_r17__cot_Sharing_r17__Type CG_COT_Sharing_r17__cot_Sharing_r17__cond :=
        proj2_format  CG_COT_Sharing_r17__cot_Sharing_r17__cond CG_COT_Sharing_r17__cot_Sharing_r17__list__Format
    CG_COT_Sharing_r17__cot_Sharing_r17__F1 CG_COT_Sharing_r17__cot_Sharing_r17__F2 CG_COT_Sharing_r17__cot_Sharing_r17__F1F2_cond  CG_COT_Sharing_r17__cot_Sharing_r17__F1F2_cond2 CG_COT_Sharing_r17__cot_Sharing_r17__F2F1_cond.
Opaque CG_COT_Sharing_r17__cot_Sharing_r17__cond CG_COT_Sharing_r17__cot_Sharing_r17__Format.


Definition CG_COT_Sharing_r17__Format_Type := Eval cbn in get_formats CG_COT_Sharing_r17__list.
Definition CG_COT_Sharing_r17__Format_list : CG_COT_Sharing_r17__Format_Type :=
  (unit__Format, (CG_COT_Sharing_r17__cot_Sharing_r17__Format, unit__Format)).
Definition CG_COT_Sharing_r17__list__Format := Eval compute in choice_format CG_COT_Sharing_r17__list CG_COT_Sharing_r17__len_helper1 CG_COT_Sharing_r17__len_helper2  CG_COT_Sharing_r17__Format_list.
Definition CG_COT_Sharing_r17__F1 (z : CG_COT_Sharing_r17__Type) : (choice CG_COT_Sharing_r17__list) :=
  match z with
   | CG_COT_Sharing_r17__noCOT_Sharing_r17 t => existT _ 0 t
  | CG_COT_Sharing_r17__cot_Sharing_r17 t => existT _ 1 t
  end.
Definition CG_COT_Sharing_r17__g := (fun n => typ_set (get_nth_typ CG_COT_Sharing_r17__list n)).
Definition CG_COT_Sharing_r17__F2 (y : choice CG_COT_Sharing_r17__list) : CG_COT_Sharing_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CG_COT_Sharing_r17__g n -> CG_COT_Sharing_r17__Type) with
    | 0 => fun (t : unit) => CG_COT_Sharing_r17__noCOT_Sharing_r17 t 
    | 1 => fun (t : CG_COT_Sharing_r17__cot_Sharing_r17__Type) => CG_COT_Sharing_r17__cot_Sharing_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CG_COT_Sharing_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CG_COT_Sharing_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CG_COT_Sharing_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CG_COT_Sharing_r17__Type with end) n0
           end t0).

Lemma CG_COT_Sharing_r17__helper2 :  forall (y : CG_COT_Sharing_r17__Type), CG_COT_Sharing_r17__cond y -> choice_cond CG_COT_Sharing_r17__list (CG_COT_Sharing_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CG_COT_Sharing_r17__helper3 :  forall (y : CG_COT_Sharing_r17__Type), CG_COT_Sharing_r17__F2 (CG_COT_Sharing_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CG_COT_Sharing_r17__helper4 : (forall b : choice CG_COT_Sharing_r17__list, choice_cond CG_COT_Sharing_r17__list b -> CG_COT_Sharing_r17__cond (CG_COT_Sharing_r17__F2 b) /\ CG_COT_Sharing_r17__F1 (CG_COT_Sharing_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CG_COT_Sharing_r17__F1 CG_COT_Sharing_r17__F2.
Definition CG_COT_Sharing_r17__Format : T_Format CG_COT_Sharing_r17__Type CG_COT_Sharing_r17__cond :=
  (* Eval compute in *) proj2_format CG_COT_Sharing_r17__cond CG_COT_Sharing_r17__list__Format CG_COT_Sharing_r17__F1 CG_COT_Sharing_r17__F2 CG_COT_Sharing_r17__helper2 CG_COT_Sharing_r17__helper3 CG_COT_Sharing_r17__helper4.
Opaque CG_COT_Sharing_r17__cond CG_COT_Sharing_r17__Format.

