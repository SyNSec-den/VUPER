Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma NR_TimeStamp_r17__nr_SFN_r17__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma NR_TimeStamp_r17__nr_SFN_r17__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_TimeStamp_r17__nr_SFN_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_TimeStamp_r17__nr_SFN_r17__Type := Z.
Definition NR_TimeStamp_r17__nr_SFN_r17__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__Type := Z.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__cond := (fun z => (0 <= z <= 9)%Z).
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__Type := Z.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__cond := (fun z => (0 <= z <= 19)%Z).
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__Type := Z.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__cond := (fun z => (0 <= z <= 39)%Z).
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__Type := Z.
Definition NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__cond := (fun z => (0 <= z <= 79)%Z).

Inductive NR_TimeStamp_r17__nr_Slot_r17__Type : Set :=
  | NR_TimeStamp_r17__nr_Slot_r17__scs15_r17 : Z -> NR_TimeStamp_r17__nr_Slot_r17__Type
  | NR_TimeStamp_r17__nr_Slot_r17__scs30_r17 : Z -> NR_TimeStamp_r17__nr_Slot_r17__Type
  | NR_TimeStamp_r17__nr_Slot_r17__scs60_r17 : Z -> NR_TimeStamp_r17__nr_Slot_r17__Type
  | NR_TimeStamp_r17__nr_Slot_r17__scs120_r17 : Z -> NR_TimeStamp_r17__nr_Slot_r17__Type
.
Definition NR_TimeStamp_r17__nr_Slot_r17__list : list typ := (
typ_cons Z NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__cond ::
typ_cons Z NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__cond ::
typ_cons Z NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__cond ::
typ_cons Z NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__cond ::
 nil).
Definition NR_TimeStamp_r17__nr_Slot_r17__cond (c : NR_TimeStamp_r17__nr_Slot_r17__Type) := 
  match c with
  | NR_TimeStamp_r17__nr_Slot_r17__scs15_r17 t => NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__cond t 
  | NR_TimeStamp_r17__nr_Slot_r17__scs30_r17 t => NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__cond t 
  | NR_TimeStamp_r17__nr_Slot_r17__scs60_r17 t => NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__cond t 
  | NR_TimeStamp_r17__nr_Slot_r17__scs120_r17 t => NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__cond t 
  end.

Lemma NR_TimeStamp_r17__nr_Slot_r17__len_helper1 : to_bit_sz (length NR_TimeStamp_r17__nr_Slot_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_TimeStamp_r17__nr_Slot_r17__len_helper2 : 2 <= length2 NR_TimeStamp_r17__nr_Slot_r17__list.
 simpl. lia. Qed.
Record NR_TimeStamp_r17__Type : Set :=
  make__NR_TimeStamp_r17__Type {
    NR_TimeStamp_r17__nr_SFN_r17 : Z ;
    NR_TimeStamp_r17__nr_Slot_r17 : NR_TimeStamp_r17__nr_Slot_r17__Type ;
}.
Definition NR_TimeStamp_r17__root_list : list seq_elem := (
 Nor Z NR_TimeStamp_r17__nr_SFN_r17__cond ::
 Nor NR_TimeStamp_r17__nr_Slot_r17__Type NR_TimeStamp_r17__nr_Slot_r17__cond ::
 nil).
Definition NR_TimeStamp_r17__ext_list : list typ := (
  nil).
Definition NR_TimeStamp_r17__cond (z : NR_TimeStamp_r17__Type) := 
(  NR_TimeStamp_r17__nr_SFN_r17__cond (NR_TimeStamp_r17__nr_SFN_r17 z) /\
  NR_TimeStamp_r17__nr_Slot_r17__cond (NR_TimeStamp_r17__nr_Slot_r17 z) /\
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
Definition NR_TimeStamp_r17__nr_SFN_r17__Format : T_Format Z NR_TimeStamp_r17__nr_SFN_r17__cond :=
 ranged_int_format (0) (1023) NR_TimeStamp_r17__nr_SFN_r17__helper1 NR_TimeStamp_r17__nr_SFN_r17__helper2.

Opaque NR_TimeStamp_r17__nr_SFN_r17__cond NR_TimeStamp_r17__nr_SFN_r17__Format.

Definition NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__Format : T_Format Z NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__cond :=
 ranged_int_format (0) (9) NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__helper1 NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__helper2.

Opaque NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__cond NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__Format.

Definition NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__Format : T_Format Z NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__cond :=
 ranged_int_format (0) (19) NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__helper1 NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__helper2.

Opaque NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__cond NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__Format.

Definition NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__Format : T_Format Z NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__cond :=
 ranged_int_format (0) (39) NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__helper1 NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__helper2.

Opaque NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__cond NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__Format.

Definition NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__Format : T_Format Z NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__cond :=
 ranged_int_format (0) (79) NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__helper1 NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__helper2.

Opaque NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__cond NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__Format.


Definition NR_TimeStamp_r17__nr_Slot_r17__Format_Type := Eval cbn in get_formats NR_TimeStamp_r17__nr_Slot_r17__list.
Definition NR_TimeStamp_r17__nr_Slot_r17__Format_list : NR_TimeStamp_r17__nr_Slot_r17__Format_Type :=
  (NR_TimeStamp_r17__nr_Slot_r17__scs15_r17__Format, (NR_TimeStamp_r17__nr_Slot_r17__scs30_r17__Format, (NR_TimeStamp_r17__nr_Slot_r17__scs60_r17__Format, (NR_TimeStamp_r17__nr_Slot_r17__scs120_r17__Format, unit__Format)))).
Definition NR_TimeStamp_r17__nr_Slot_r17__list__Format := Eval compute in choice_format NR_TimeStamp_r17__nr_Slot_r17__list NR_TimeStamp_r17__nr_Slot_r17__len_helper1 NR_TimeStamp_r17__nr_Slot_r17__len_helper2  NR_TimeStamp_r17__nr_Slot_r17__Format_list.
Definition NR_TimeStamp_r17__nr_Slot_r17__F1 (z : NR_TimeStamp_r17__nr_Slot_r17__Type) : (choice NR_TimeStamp_r17__nr_Slot_r17__list) :=
  match z with
   | NR_TimeStamp_r17__nr_Slot_r17__scs15_r17 t => existT _ 0 t
  | NR_TimeStamp_r17__nr_Slot_r17__scs30_r17 t => existT _ 1 t
  | NR_TimeStamp_r17__nr_Slot_r17__scs60_r17 t => existT _ 2 t
  | NR_TimeStamp_r17__nr_Slot_r17__scs120_r17 t => existT _ 3 t
  end.
Definition NR_TimeStamp_r17__nr_Slot_r17__g := (fun n => typ_set (get_nth_typ NR_TimeStamp_r17__nr_Slot_r17__list n)).
Definition NR_TimeStamp_r17__nr_Slot_r17__F2 (y : choice NR_TimeStamp_r17__nr_Slot_r17__list) : NR_TimeStamp_r17__nr_Slot_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_TimeStamp_r17__nr_Slot_r17__g n -> NR_TimeStamp_r17__nr_Slot_r17__Type) with
    | 0 => fun (t : Z) => NR_TimeStamp_r17__nr_Slot_r17__scs15_r17 t 
    | 1 => fun (t : Z) => NR_TimeStamp_r17__nr_Slot_r17__scs30_r17 t 
    | 2 => fun (t : Z) => NR_TimeStamp_r17__nr_Slot_r17__scs60_r17 t 
    | 3 => fun (t : Z) => NR_TimeStamp_r17__nr_Slot_r17__scs120_r17 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : NR_TimeStamp_r17__nr_Slot_r17__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ NR_TimeStamp_r17__nr_Slot_r17__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_TimeStamp_r17__nr_Slot_r17__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return NR_TimeStamp_r17__nr_Slot_r17__Type with end) n0
           end t0).

Lemma NR_TimeStamp_r17__nr_Slot_r17__helper2 :  forall (y : NR_TimeStamp_r17__nr_Slot_r17__Type), NR_TimeStamp_r17__nr_Slot_r17__cond y -> choice_cond NR_TimeStamp_r17__nr_Slot_r17__list (NR_TimeStamp_r17__nr_Slot_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_TimeStamp_r17__nr_Slot_r17__helper3 :  forall (y : NR_TimeStamp_r17__nr_Slot_r17__Type), NR_TimeStamp_r17__nr_Slot_r17__F2 (NR_TimeStamp_r17__nr_Slot_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_TimeStamp_r17__nr_Slot_r17__helper4 : (forall b : choice NR_TimeStamp_r17__nr_Slot_r17__list, choice_cond NR_TimeStamp_r17__nr_Slot_r17__list b -> NR_TimeStamp_r17__nr_Slot_r17__cond (NR_TimeStamp_r17__nr_Slot_r17__F2 b) /\ NR_TimeStamp_r17__nr_Slot_r17__F1 (NR_TimeStamp_r17__nr_Slot_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_TimeStamp_r17__nr_Slot_r17__F1 NR_TimeStamp_r17__nr_Slot_r17__F2.
Definition NR_TimeStamp_r17__nr_Slot_r17__Format : T_Format NR_TimeStamp_r17__nr_Slot_r17__Type NR_TimeStamp_r17__nr_Slot_r17__cond :=
  (* Eval compute in *) proj2_format NR_TimeStamp_r17__nr_Slot_r17__cond NR_TimeStamp_r17__nr_Slot_r17__list__Format NR_TimeStamp_r17__nr_Slot_r17__F1 NR_TimeStamp_r17__nr_Slot_r17__F2 NR_TimeStamp_r17__nr_Slot_r17__helper2 NR_TimeStamp_r17__nr_Slot_r17__helper3 NR_TimeStamp_r17__nr_Slot_r17__helper4.
Opaque NR_TimeStamp_r17__nr_Slot_r17__cond NR_TimeStamp_r17__nr_Slot_r17__Format.


Definition NR_TimeStamp_r17__root_Format_Type := Eval cbn in seq_format_prod NR_TimeStamp_r17__root_list.
Definition NR_TimeStamp_r17__root_Format_list : NR_TimeStamp_r17__root_Format_Type :=
  (NR_TimeStamp_r17__nr_SFN_r17__Format, (NR_TimeStamp_r17__nr_Slot_r17__Format, unit_format)).

Definition NR_TimeStamp_r17__ext_Format_Type := Eval cbn in get_formats NR_TimeStamp_r17__ext_list.
Definition NR_TimeStamp_r17__ext_Format_list : NR_TimeStamp_r17__ext_Format_Type :=
  unit__Format.

Definition NR_TimeStamp_r17__list_type : Set := (seq_type NR_TimeStamp_r17__root_list) * (seq_ext_type NR_TimeStamp_r17__ext_list).
Definition NR_TimeStamp_r17__list_cond (z : NR_TimeStamp_r17__list_type) : Prop :=
        (seq_cond NR_TimeStamp_r17__root_list (fst z)) /\ (seq_ext_cond NR_TimeStamp_r17__ext_list (snd z)).
Definition NR_TimeStamp_r17__list_format : T_Format NR_TimeStamp_r17__list_type NR_TimeStamp_r17__list_cond :=
 (* Eval compute in *) seq_ext_format NR_TimeStamp_r17__root_list NR_TimeStamp_r17__root_Format_list NR_TimeStamp_r17__ext_list NR_TimeStamp_r17__ext_Format_list.

Opaque NR_TimeStamp_r17__list_format.
Definition NR_TimeStamp_r17__F1 (z : NR_TimeStamp_r17__Type) : NR_TimeStamp_r17__list_type :=
  (((NR_TimeStamp_r17__nr_SFN_r17 z, (NR_TimeStamp_r17__nr_Slot_r17 z, tt))), (
tt)).
Definition NR_TimeStamp_r17__F2 (y : NR_TimeStamp_r17__list_type) : NR_TimeStamp_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__NR_TimeStamp_r17__Type j0 j1
  end.
Definition NR_TimeStamp_r17__helper1 : (forall a : NR_TimeStamp_r17__Type, NR_TimeStamp_r17__cond a -> NR_TimeStamp_r17__list_cond (NR_TimeStamp_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NR_TimeStamp_r17__helper2 : (forall a : NR_TimeStamp_r17__Type, NR_TimeStamp_r17__F2 (NR_TimeStamp_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NR_TimeStamp_r17__helper3 : (forall b : NR_TimeStamp_r17__list_type, NR_TimeStamp_r17__list_cond b -> NR_TimeStamp_r17__cond (NR_TimeStamp_r17__F2 b) /\ NR_TimeStamp_r17__F1 (NR_TimeStamp_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NR_TimeStamp_r17__cond, NR_TimeStamp_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NR_TimeStamp_r17__Format : T_Format NR_TimeStamp_r17__Type NR_TimeStamp_r17__cond :=
 proj2_format NR_TimeStamp_r17__cond NR_TimeStamp_r17__list_format  NR_TimeStamp_r17__F1 NR_TimeStamp_r17__F2 NR_TimeStamp_r17__helper1 NR_TimeStamp_r17__helper2 NR_TimeStamp_r17__helper3.

Opaque NR_TimeStamp_r17__cond NR_TimeStamp_r17__Format.

