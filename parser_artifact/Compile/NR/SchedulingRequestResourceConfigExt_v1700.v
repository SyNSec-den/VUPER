Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__Type := Z.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__Type := Z.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__Type := Z.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__cond := (fun z => (0 <= z <= 5119)%Z).

Inductive SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type : Set :=
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280 : Z -> SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560 : Z -> SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120 : Z -> SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type
.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list : list typ := (
typ_cons Z SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__cond ::
typ_cons Z SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__cond ::
typ_cons Z SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__cond ::
 nil).
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond (c : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type) := 
  match c with
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280 t => SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__cond t 
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560 t => SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__cond t 
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120 t => SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__cond t 
  end.

Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__len_helper1 : to_bit_sz (length SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__len_helper2 : 2 <= length2 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list.
 simpl. lia. Qed.
Record SchedulingRequestResourceConfigExt_v1700__Type : Set :=
  make__SchedulingRequestResourceConfigExt_v1700__Type {
    SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17 : option SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type ;
}.
Definition SchedulingRequestResourceConfigExt_v1700__list := (
 Opt SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond ::
 nil).
Definition SchedulingRequestResourceConfigExt_v1700__cond z := 
  opt_cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17 z) /\
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
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__Format : T_Format Z SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__cond :=
 ranged_int_format (0) (1279) SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__helper1 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__helper2.

Opaque SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__Format.

Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__Format : T_Format Z SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__cond :=
 ranged_int_format (0) (2559) SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__helper1 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__helper2.

Opaque SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__Format.

Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__Format : T_Format Z SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__cond :=
 ranged_int_format (0) (5119) SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__helper1 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__helper2.

Opaque SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__Format.


Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format_Type := Eval cbn in get_formats SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format_list : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format_Type :=
  (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280__Format, (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560__Format, (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120__Format, unit__Format))).
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list__Format := Eval compute in choice_format SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__len_helper1 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__len_helper2  SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format_list.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F1 (z : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type) : (choice SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list) :=
  match z with
   | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280 t => existT _ 0 t
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560 t => existT _ 1 t
  | SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120 t => existT _ 2 t
  end.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__g := (fun n => typ_set (get_nth_typ SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list n)).
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F2 (y : choice SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list) : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__g n -> SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type) with
    | 0 => fun (t : Z) => SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl1280 t 
    | 1 => fun (t : Z) => SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl2560 t 
    | 2 => fun (t : Z) => SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__sl5120 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type with end) n0
           end t0).

Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__helper2 :  forall (y : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type), SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond y -> choice_cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__helper3 :  forall (y : SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type), SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F2 (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__helper4 : (forall b : choice SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list, choice_cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list b -> SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F2 b) /\ SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F1 (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F1 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F2.
Definition SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format : T_Format SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Type SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond :=
  (* Eval compute in *) proj2_format SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__list__Format SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F1 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__F2 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__helper2 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__helper3 SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__helper4.
Opaque SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__cond SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format.


Definition SchedulingRequestResourceConfigExt_v1700__Format_Type := Eval cbn in seq_format_prod SchedulingRequestResourceConfigExt_v1700__list.
Definition SchedulingRequestResourceConfigExt_v1700__Format_list : SchedulingRequestResourceConfigExt_v1700__Format_Type :=
  (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17__Format, unit_format).
Definition SchedulingRequestResourceConfigExt_v1700__list__Format := (*Eval compute in *) seq_format SchedulingRequestResourceConfigExt_v1700__list SchedulingRequestResourceConfigExt_v1700__Format_list.
Definition SchedulingRequestResourceConfigExt_v1700__F1 z :=
  (SchedulingRequestResourceConfigExt_v1700__periodicityAndOffset_r17 z, tt).
Definition SchedulingRequestResourceConfigExt_v1700__F2 (y : seq_type SchedulingRequestResourceConfigExt_v1700__list) :=
  match y with
  | (i0, _)=>
    make__SchedulingRequestResourceConfigExt_v1700__Type i0
  end.
Lemma SchedulingRequestResourceConfigExt_v1700__F1F2_cond (z : SchedulingRequestResourceConfigExt_v1700__Type)
  : SchedulingRequestResourceConfigExt_v1700__cond z ->
  (seq_cond SchedulingRequestResourceConfigExt_v1700__list (SchedulingRequestResourceConfigExt_v1700__F1 z)).
intro H. unfold SchedulingRequestResourceConfigExt_v1700__cond in H. simpl. auto. Qed.
Lemma SchedulingRequestResourceConfigExt_v1700__F1F2_cond2 (z : SchedulingRequestResourceConfigExt_v1700__Type)
 : SchedulingRequestResourceConfigExt_v1700__F2 (SchedulingRequestResourceConfigExt_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingRequestResourceConfigExt_v1700__F2F1_cond (y : seq_type SchedulingRequestResourceConfigExt_v1700__list)
  : seq_cond SchedulingRequestResourceConfigExt_v1700__list y ->
 (SchedulingRequestResourceConfigExt_v1700__cond (SchedulingRequestResourceConfigExt_v1700__F2 y)) /\  SchedulingRequestResourceConfigExt_v1700__F1 (SchedulingRequestResourceConfigExt_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingRequestResourceConfigExt_v1700__cond. simpl in *. auto.
 - simpl. unfold SchedulingRequestResourceConfigExt_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingRequestResourceConfigExt_v1700__Format : T_Format SchedulingRequestResourceConfigExt_v1700__Type SchedulingRequestResourceConfigExt_v1700__cond :=
        proj2_format  SchedulingRequestResourceConfigExt_v1700__cond SchedulingRequestResourceConfigExt_v1700__list__Format
    SchedulingRequestResourceConfigExt_v1700__F1 SchedulingRequestResourceConfigExt_v1700__F2 SchedulingRequestResourceConfigExt_v1700__F1F2_cond  SchedulingRequestResourceConfigExt_v1700__F1F2_cond2 SchedulingRequestResourceConfigExt_v1700__F2F1_cond.
Opaque SchedulingRequestResourceConfigExt_v1700__cond SchedulingRequestResourceConfigExt_v1700__Format.

