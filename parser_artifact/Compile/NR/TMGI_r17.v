Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma TMGI_r17__plmn_Id_r17__plmn_Index__helper1 : (1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma TMGI_r17__plmn_Id_r17__plmn_Index__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TMGI_r17__plmn_Id_r17__plmn_Index__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TMGI_r17__plmn_Id_r17__plmn_Index__Type := Z.
Definition TMGI_r17__plmn_Id_r17__plmn_Index__cond := (fun z => (1 <= z <= maxPLMN)%Z).
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.


Inductive TMGI_r17__plmn_Id_r17__Type : Set :=
  | TMGI_r17__plmn_Id_r17__plmn_Index : Z -> TMGI_r17__plmn_Id_r17__Type
  | TMGI_r17__plmn_Id_r17__explicitValue : PLMN_Identity__Type -> TMGI_r17__plmn_Id_r17__Type
.
Definition TMGI_r17__plmn_Id_r17__list : list typ := (
typ_cons Z TMGI_r17__plmn_Id_r17__plmn_Index__cond ::
typ_cons PLMN_Identity__Type PLMN_Identity__cond ::
 nil).
Definition TMGI_r17__plmn_Id_r17__cond (c : TMGI_r17__plmn_Id_r17__Type) := 
  match c with
  | TMGI_r17__plmn_Id_r17__plmn_Index t => TMGI_r17__plmn_Id_r17__plmn_Index__cond t 
  | TMGI_r17__plmn_Id_r17__explicitValue t => PLMN_Identity__cond t 
  end.

Lemma TMGI_r17__plmn_Id_r17__len_helper1 : to_bit_sz (length TMGI_r17__plmn_Id_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma TMGI_r17__plmn_Id_r17__len_helper2 : 2 <= length2 TMGI_r17__plmn_Id_r17__list.
 simpl. lia. Qed.
Definition TMGI_r17__serviceId_r17__Type := octet_string.
Definition TMGI_r17__serviceId_r17__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 3)%Z).
Record TMGI_r17__Type : Set :=
  make__TMGI_r17__Type {
    TMGI_r17__plmn_Id_r17 : TMGI_r17__plmn_Id_r17__Type ;
    TMGI_r17__serviceId_r17 : TMGI_r17__serviceId_r17__Type ;
}.
Definition TMGI_r17__list := (
 Nor TMGI_r17__plmn_Id_r17__Type TMGI_r17__plmn_Id_r17__cond ::
 Nor TMGI_r17__serviceId_r17__Type TMGI_r17__serviceId_r17__cond ::
 nil).
Definition TMGI_r17__cond z := 
  TMGI_r17__plmn_Id_r17__cond (TMGI_r17__plmn_Id_r17 z) /\
  TMGI_r17__serviceId_r17__cond (TMGI_r17__serviceId_r17 z) /\
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
Definition TMGI_r17__plmn_Id_r17__plmn_Index__Format : T_Format Z TMGI_r17__plmn_Id_r17__plmn_Index__cond :=
 ranged_int_format (1) (maxPLMN) TMGI_r17__plmn_Id_r17__plmn_Index__helper1 TMGI_r17__plmn_Id_r17__plmn_Index__helper2.

Opaque TMGI_r17__plmn_Id_r17__plmn_Index__cond TMGI_r17__plmn_Id_r17__plmn_Index__Format.


Definition TMGI_r17__plmn_Id_r17__Format_Type := Eval cbn in get_formats TMGI_r17__plmn_Id_r17__list.
Definition TMGI_r17__plmn_Id_r17__Format_list : TMGI_r17__plmn_Id_r17__Format_Type :=
  (TMGI_r17__plmn_Id_r17__plmn_Index__Format, (PLMN_Identity__Format, unit__Format)).
Definition TMGI_r17__plmn_Id_r17__list__Format := Eval compute in choice_format TMGI_r17__plmn_Id_r17__list TMGI_r17__plmn_Id_r17__len_helper1 TMGI_r17__plmn_Id_r17__len_helper2  TMGI_r17__plmn_Id_r17__Format_list.
Definition TMGI_r17__plmn_Id_r17__F1 (z : TMGI_r17__plmn_Id_r17__Type) : (choice TMGI_r17__plmn_Id_r17__list) :=
  match z with
   | TMGI_r17__plmn_Id_r17__plmn_Index t => existT _ 0 t
  | TMGI_r17__plmn_Id_r17__explicitValue t => existT _ 1 t
  end.
Definition TMGI_r17__plmn_Id_r17__g := (fun n => typ_set (get_nth_typ TMGI_r17__plmn_Id_r17__list n)).
Definition TMGI_r17__plmn_Id_r17__F2 (y : choice TMGI_r17__plmn_Id_r17__list) : TMGI_r17__plmn_Id_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (TMGI_r17__plmn_Id_r17__g n -> TMGI_r17__plmn_Id_r17__Type) with
    | 0 => fun (t : Z) => TMGI_r17__plmn_Id_r17__plmn_Index t 
    | 1 => fun (t : PLMN_Identity__Type) => TMGI_r17__plmn_Id_r17__explicitValue t 
 | (S (S n0)) => (fun (x' : nat) (t'' : TMGI_r17__plmn_Id_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ TMGI_r17__plmn_Id_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len TMGI_r17__plmn_Id_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return TMGI_r17__plmn_Id_r17__Type with end) n0
           end t0).

Lemma TMGI_r17__plmn_Id_r17__helper2 :  forall (y : TMGI_r17__plmn_Id_r17__Type), TMGI_r17__plmn_Id_r17__cond y -> choice_cond TMGI_r17__plmn_Id_r17__list (TMGI_r17__plmn_Id_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma TMGI_r17__plmn_Id_r17__helper3 :  forall (y : TMGI_r17__plmn_Id_r17__Type), TMGI_r17__plmn_Id_r17__F2 (TMGI_r17__plmn_Id_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma TMGI_r17__plmn_Id_r17__helper4 : (forall b : choice TMGI_r17__plmn_Id_r17__list, choice_cond TMGI_r17__plmn_Id_r17__list b -> TMGI_r17__plmn_Id_r17__cond (TMGI_r17__plmn_Id_r17__F2 b) /\ TMGI_r17__plmn_Id_r17__F1 (TMGI_r17__plmn_Id_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length TMGI_r17__plmn_Id_r17__F1 TMGI_r17__plmn_Id_r17__F2.
Definition TMGI_r17__plmn_Id_r17__Format : T_Format TMGI_r17__plmn_Id_r17__Type TMGI_r17__plmn_Id_r17__cond :=
  (* Eval compute in *) proj2_format TMGI_r17__plmn_Id_r17__cond TMGI_r17__plmn_Id_r17__list__Format TMGI_r17__plmn_Id_r17__F1 TMGI_r17__plmn_Id_r17__F2 TMGI_r17__plmn_Id_r17__helper2 TMGI_r17__plmn_Id_r17__helper3 TMGI_r17__plmn_Id_r17__helper4.
Opaque TMGI_r17__plmn_Id_r17__cond TMGI_r17__plmn_Id_r17__Format.

Definition TMGI_r17__serviceId_r17__Format : T_Format TMGI_r17__serviceId_r17__Type TMGI_r17__serviceId_r17__cond := (* Eval compute in *) octet_string_fixed_format 3.
Opaque TMGI_r17__serviceId_r17__cond TMGI_r17__serviceId_r17__Format.


Definition TMGI_r17__Format_Type := Eval cbn in seq_format_prod TMGI_r17__list.
Definition TMGI_r17__Format_list : TMGI_r17__Format_Type :=
  (TMGI_r17__plmn_Id_r17__Format, (TMGI_r17__serviceId_r17__Format, unit_format)).
Definition TMGI_r17__list__Format := (*Eval compute in *) seq_format TMGI_r17__list TMGI_r17__Format_list.
Definition TMGI_r17__F1 z :=
  (TMGI_r17__plmn_Id_r17 z, (TMGI_r17__serviceId_r17 z, tt)).
Definition TMGI_r17__F2 (y : seq_type TMGI_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TMGI_r17__Type i0 i1
  end.
Lemma TMGI_r17__F1F2_cond (z : TMGI_r17__Type)
  : TMGI_r17__cond z ->
  (seq_cond TMGI_r17__list (TMGI_r17__F1 z)).
intro H. unfold TMGI_r17__cond in H. simpl. auto. Qed.
Lemma TMGI_r17__F1F2_cond2 (z : TMGI_r17__Type)
 : TMGI_r17__F2 (TMGI_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TMGI_r17__F2F1_cond (y : seq_type TMGI_r17__list)
  : seq_cond TMGI_r17__list y ->
 (TMGI_r17__cond (TMGI_r17__F2 y)) /\  TMGI_r17__F1 (TMGI_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TMGI_r17__cond. simpl in *. auto.
 - simpl. unfold TMGI_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TMGI_r17__Format : T_Format TMGI_r17__Type TMGI_r17__cond :=
        proj2_format  TMGI_r17__cond TMGI_r17__list__Format
    TMGI_r17__F1 TMGI_r17__F2 TMGI_r17__F1F2_cond  TMGI_r17__F1F2_cond2 TMGI_r17__F2F1_cond.
Opaque TMGI_r17__cond TMGI_r17__Format.

