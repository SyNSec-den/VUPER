Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CSI_ReportPeriodicityAndOffset__slots4__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots4__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots4__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots4__cond := (fun z => (0 <= z <= 3)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots5__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots5__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots5__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots5__cond := (fun z => (0 <= z <= 4)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots8__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots8__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots8__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots8__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots8__cond := (fun z => (0 <= z <= 7)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots10__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots16__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots20__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots40__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots80__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots160__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma CSI_ReportPeriodicityAndOffset__slots320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__slots320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportPeriodicityAndOffset__slots320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportPeriodicityAndOffset__slots320__Type := Z.
Definition CSI_ReportPeriodicityAndOffset__slots320__cond := (fun z => (0 <= z <= 319)%Z).

Inductive CSI_ReportPeriodicityAndOffset__Type : Set :=
  | CSI_ReportPeriodicityAndOffset__slots4 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots5 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots8 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots10 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots16 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots20 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots40 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots80 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots160 : Z -> CSI_ReportPeriodicityAndOffset__Type
  | CSI_ReportPeriodicityAndOffset__slots320 : Z -> CSI_ReportPeriodicityAndOffset__Type
.
Definition CSI_ReportPeriodicityAndOffset__list : list typ := (
typ_cons Z CSI_ReportPeriodicityAndOffset__slots4__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots5__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots8__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots10__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots16__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots20__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots40__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots80__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots160__cond ::
typ_cons Z CSI_ReportPeriodicityAndOffset__slots320__cond ::
 nil).
Definition CSI_ReportPeriodicityAndOffset__cond (c : CSI_ReportPeriodicityAndOffset__Type) := 
  match c with
  | CSI_ReportPeriodicityAndOffset__slots4 t => CSI_ReportPeriodicityAndOffset__slots4__cond t 
  | CSI_ReportPeriodicityAndOffset__slots5 t => CSI_ReportPeriodicityAndOffset__slots5__cond t 
  | CSI_ReportPeriodicityAndOffset__slots8 t => CSI_ReportPeriodicityAndOffset__slots8__cond t 
  | CSI_ReportPeriodicityAndOffset__slots10 t => CSI_ReportPeriodicityAndOffset__slots10__cond t 
  | CSI_ReportPeriodicityAndOffset__slots16 t => CSI_ReportPeriodicityAndOffset__slots16__cond t 
  | CSI_ReportPeriodicityAndOffset__slots20 t => CSI_ReportPeriodicityAndOffset__slots20__cond t 
  | CSI_ReportPeriodicityAndOffset__slots40 t => CSI_ReportPeriodicityAndOffset__slots40__cond t 
  | CSI_ReportPeriodicityAndOffset__slots80 t => CSI_ReportPeriodicityAndOffset__slots80__cond t 
  | CSI_ReportPeriodicityAndOffset__slots160 t => CSI_ReportPeriodicityAndOffset__slots160__cond t 
  | CSI_ReportPeriodicityAndOffset__slots320 t => CSI_ReportPeriodicityAndOffset__slots320__cond t 
  end.

Lemma CSI_ReportPeriodicityAndOffset__len_helper1 : to_bit_sz (length CSI_ReportPeriodicityAndOffset__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportPeriodicityAndOffset__len_helper2 : 2 <= length2 CSI_ReportPeriodicityAndOffset__list.
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
Definition CSI_ReportPeriodicityAndOffset__slots4__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots4__cond :=
 ranged_int_format (0) (3) CSI_ReportPeriodicityAndOffset__slots4__helper1 CSI_ReportPeriodicityAndOffset__slots4__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots4__cond CSI_ReportPeriodicityAndOffset__slots4__Format.

Definition CSI_ReportPeriodicityAndOffset__slots5__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots5__cond :=
 ranged_int_format (0) (4) CSI_ReportPeriodicityAndOffset__slots5__helper1 CSI_ReportPeriodicityAndOffset__slots5__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots5__cond CSI_ReportPeriodicityAndOffset__slots5__Format.

Definition CSI_ReportPeriodicityAndOffset__slots8__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots8__cond :=
 ranged_int_format (0) (7) CSI_ReportPeriodicityAndOffset__slots8__helper1 CSI_ReportPeriodicityAndOffset__slots8__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots8__cond CSI_ReportPeriodicityAndOffset__slots8__Format.

Definition CSI_ReportPeriodicityAndOffset__slots10__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots10__cond :=
 ranged_int_format (0) (9) CSI_ReportPeriodicityAndOffset__slots10__helper1 CSI_ReportPeriodicityAndOffset__slots10__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots10__cond CSI_ReportPeriodicityAndOffset__slots10__Format.

Definition CSI_ReportPeriodicityAndOffset__slots16__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots16__cond :=
 ranged_int_format (0) (15) CSI_ReportPeriodicityAndOffset__slots16__helper1 CSI_ReportPeriodicityAndOffset__slots16__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots16__cond CSI_ReportPeriodicityAndOffset__slots16__Format.

Definition CSI_ReportPeriodicityAndOffset__slots20__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots20__cond :=
 ranged_int_format (0) (19) CSI_ReportPeriodicityAndOffset__slots20__helper1 CSI_ReportPeriodicityAndOffset__slots20__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots20__cond CSI_ReportPeriodicityAndOffset__slots20__Format.

Definition CSI_ReportPeriodicityAndOffset__slots40__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots40__cond :=
 ranged_int_format (0) (39) CSI_ReportPeriodicityAndOffset__slots40__helper1 CSI_ReportPeriodicityAndOffset__slots40__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots40__cond CSI_ReportPeriodicityAndOffset__slots40__Format.

Definition CSI_ReportPeriodicityAndOffset__slots80__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots80__cond :=
 ranged_int_format (0) (79) CSI_ReportPeriodicityAndOffset__slots80__helper1 CSI_ReportPeriodicityAndOffset__slots80__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots80__cond CSI_ReportPeriodicityAndOffset__slots80__Format.

Definition CSI_ReportPeriodicityAndOffset__slots160__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots160__cond :=
 ranged_int_format (0) (159) CSI_ReportPeriodicityAndOffset__slots160__helper1 CSI_ReportPeriodicityAndOffset__slots160__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots160__cond CSI_ReportPeriodicityAndOffset__slots160__Format.

Definition CSI_ReportPeriodicityAndOffset__slots320__Format : T_Format Z CSI_ReportPeriodicityAndOffset__slots320__cond :=
 ranged_int_format (0) (319) CSI_ReportPeriodicityAndOffset__slots320__helper1 CSI_ReportPeriodicityAndOffset__slots320__helper2.

Opaque CSI_ReportPeriodicityAndOffset__slots320__cond CSI_ReportPeriodicityAndOffset__slots320__Format.


Definition CSI_ReportPeriodicityAndOffset__Format_Type := Eval cbn in get_formats CSI_ReportPeriodicityAndOffset__list.
Definition CSI_ReportPeriodicityAndOffset__Format_list : CSI_ReportPeriodicityAndOffset__Format_Type :=
  (CSI_ReportPeriodicityAndOffset__slots4__Format, (CSI_ReportPeriodicityAndOffset__slots5__Format, (CSI_ReportPeriodicityAndOffset__slots8__Format, (CSI_ReportPeriodicityAndOffset__slots10__Format, (CSI_ReportPeriodicityAndOffset__slots16__Format, (CSI_ReportPeriodicityAndOffset__slots20__Format, (CSI_ReportPeriodicityAndOffset__slots40__Format, (CSI_ReportPeriodicityAndOffset__slots80__Format, (CSI_ReportPeriodicityAndOffset__slots160__Format, (CSI_ReportPeriodicityAndOffset__slots320__Format, unit__Format)))))))))).
Definition CSI_ReportPeriodicityAndOffset__list__Format := Eval compute in choice_format CSI_ReportPeriodicityAndOffset__list CSI_ReportPeriodicityAndOffset__len_helper1 CSI_ReportPeriodicityAndOffset__len_helper2  CSI_ReportPeriodicityAndOffset__Format_list.
Definition CSI_ReportPeriodicityAndOffset__F1 (z : CSI_ReportPeriodicityAndOffset__Type) : (choice CSI_ReportPeriodicityAndOffset__list) :=
  match z with
   | CSI_ReportPeriodicityAndOffset__slots4 t => existT _ 0 t
  | CSI_ReportPeriodicityAndOffset__slots5 t => existT _ 1 t
  | CSI_ReportPeriodicityAndOffset__slots8 t => existT _ 2 t
  | CSI_ReportPeriodicityAndOffset__slots10 t => existT _ 3 t
  | CSI_ReportPeriodicityAndOffset__slots16 t => existT _ 4 t
  | CSI_ReportPeriodicityAndOffset__slots20 t => existT _ 5 t
  | CSI_ReportPeriodicityAndOffset__slots40 t => existT _ 6 t
  | CSI_ReportPeriodicityAndOffset__slots80 t => existT _ 7 t
  | CSI_ReportPeriodicityAndOffset__slots160 t => existT _ 8 t
  | CSI_ReportPeriodicityAndOffset__slots320 t => existT _ 9 t
  end.
Definition CSI_ReportPeriodicityAndOffset__g := (fun n => typ_set (get_nth_typ CSI_ReportPeriodicityAndOffset__list n)).
Definition CSI_ReportPeriodicityAndOffset__F2 (y : choice CSI_ReportPeriodicityAndOffset__list) : CSI_ReportPeriodicityAndOffset__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportPeriodicityAndOffset__g n -> CSI_ReportPeriodicityAndOffset__Type) with
    | 0 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots4 t 
    | 1 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots5 t 
    | 2 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots8 t 
    | 3 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots10 t 
    | 4 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots16 t 
    | 5 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots20 t 
    | 6 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots40 t 
    | 7 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots80 t 
    | 8 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots160 t 
    | 9 => fun (t : Z) => CSI_ReportPeriodicityAndOffset__slots320 t 
 | (S (S (S (S (S (S (S (S (S (S n0)))))))))) => (fun (x' : nat) (t'' : CSI_ReportPeriodicityAndOffset__g (S (S (S (S (S (S (S (S (S (S x'))))))))))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportPeriodicityAndOffset__list (S (S (S (S (S (S (S (S (S (S x')))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportPeriodicityAndOffset__list (S (S (S (S (S (S (S (S (S (S x'))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))) in match t' return CSI_ReportPeriodicityAndOffset__Type with end) n0
           end t0).

Lemma CSI_ReportPeriodicityAndOffset__helper2 :  forall (y : CSI_ReportPeriodicityAndOffset__Type), CSI_ReportPeriodicityAndOffset__cond y -> choice_cond CSI_ReportPeriodicityAndOffset__list (CSI_ReportPeriodicityAndOffset__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportPeriodicityAndOffset__helper3 :  forall (y : CSI_ReportPeriodicityAndOffset__Type), CSI_ReportPeriodicityAndOffset__F2 (CSI_ReportPeriodicityAndOffset__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportPeriodicityAndOffset__helper4 : (forall b : choice CSI_ReportPeriodicityAndOffset__list, choice_cond CSI_ReportPeriodicityAndOffset__list b -> CSI_ReportPeriodicityAndOffset__cond (CSI_ReportPeriodicityAndOffset__F2 b) /\ CSI_ReportPeriodicityAndOffset__F1 (CSI_ReportPeriodicityAndOffset__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportPeriodicityAndOffset__F1 CSI_ReportPeriodicityAndOffset__F2.
Definition CSI_ReportPeriodicityAndOffset__Format : T_Format CSI_ReportPeriodicityAndOffset__Type CSI_ReportPeriodicityAndOffset__cond :=
  (* Eval compute in *) proj2_format CSI_ReportPeriodicityAndOffset__cond CSI_ReportPeriodicityAndOffset__list__Format CSI_ReportPeriodicityAndOffset__F1 CSI_ReportPeriodicityAndOffset__F2 CSI_ReportPeriodicityAndOffset__helper2 CSI_ReportPeriodicityAndOffset__helper3 CSI_ReportPeriodicityAndOffset__helper4.
Opaque CSI_ReportPeriodicityAndOffset__cond CSI_ReportPeriodicityAndOffset__Format.

