Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__Type := Z.
Definition SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__cond := (fun z => (0 <= z <= 3)%Z).
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.


Inductive SL_RemoteUE_RB_Identity_r17__root__Type : Set :=
  | SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17 : Z -> SL_RemoteUE_RB_Identity_r17__root__Type
  | SL_RemoteUE_RB_Identity_r17__root__drb_Identity_r17 : DRB_Identity__Type -> SL_RemoteUE_RB_Identity_r17__root__Type
.
Definition SL_RemoteUE_RB_Identity_r17__root__list : list typ := (
typ_cons Z SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__cond ::
typ_cons DRB_Identity__Type DRB_Identity__cond ::
 nil).
Definition SL_RemoteUE_RB_Identity_r17__root__cond (c : SL_RemoteUE_RB_Identity_r17__root__Type) := 
  match c with
  | SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17 t => SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__cond t 
  | SL_RemoteUE_RB_Identity_r17__root__drb_Identity_r17 t => DRB_Identity__cond t 
  end.

Lemma SL_RemoteUE_RB_Identity_r17__root__len_helper1 : to_bit_sz (length SL_RemoteUE_RB_Identity_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_RemoteUE_RB_Identity_r17__root__len_helper2 : 2 <= length2 SL_RemoteUE_RB_Identity_r17__root__list.
 simpl. lia. Qed.

Definition SL_RemoteUE_RB_Identity_r17__ext__Type : Set := Empty_set.
Definition SL_RemoteUE_RB_Identity_r17__ext__cond (c : SL_RemoteUE_RB_Identity_r17__ext__Type) := True.
Definition SL_RemoteUE_RB_Identity_r17__Type : Set := SL_RemoteUE_RB_Identity_r17__root__Type + SL_RemoteUE_RB_Identity_r17__ext__Type.
Definition SL_RemoteUE_RB_Identity_r17__cond :=
  sum_cond SL_RemoteUE_RB_Identity_r17__root__cond SL_RemoteUE_RB_Identity_r17__ext__cond.

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
Definition SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__Format : T_Format Z SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__cond :=
 ranged_int_format (0) (3) SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__helper1 SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__helper2.

Opaque SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__cond SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__Format.


Definition SL_RemoteUE_RB_Identity_r17__root__Format_Type := Eval cbn in get_formats SL_RemoteUE_RB_Identity_r17__root__list.
Definition SL_RemoteUE_RB_Identity_r17__root__Format_list : SL_RemoteUE_RB_Identity_r17__root__Format_Type :=
  (SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17__Format, (DRB_Identity__Format, unit__Format)).
Definition SL_RemoteUE_RB_Identity_r17__root__list__Format := Eval compute in choice_format SL_RemoteUE_RB_Identity_r17__root__list SL_RemoteUE_RB_Identity_r17__root__len_helper1 SL_RemoteUE_RB_Identity_r17__root__len_helper2  SL_RemoteUE_RB_Identity_r17__root__Format_list.
Definition SL_RemoteUE_RB_Identity_r17__root__F1 (z : SL_RemoteUE_RB_Identity_r17__root__Type) : (choice SL_RemoteUE_RB_Identity_r17__root__list) :=
  match z with
   | SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17 t => existT _ 0 t
  | SL_RemoteUE_RB_Identity_r17__root__drb_Identity_r17 t => existT _ 1 t
  end.
Definition SL_RemoteUE_RB_Identity_r17__root__g := (fun n => typ_set (get_nth_typ SL_RemoteUE_RB_Identity_r17__root__list n)).
Definition SL_RemoteUE_RB_Identity_r17__root__F2 (y : choice SL_RemoteUE_RB_Identity_r17__root__list) : SL_RemoteUE_RB_Identity_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_RemoteUE_RB_Identity_r17__root__g n -> SL_RemoteUE_RB_Identity_r17__root__Type) with
    | 0 => fun (t : Z) => SL_RemoteUE_RB_Identity_r17__root__srb_Identity_r17 t 
    | 1 => fun (t : DRB_Identity__Type) => SL_RemoteUE_RB_Identity_r17__root__drb_Identity_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_RemoteUE_RB_Identity_r17__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_RemoteUE_RB_Identity_r17__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_RemoteUE_RB_Identity_r17__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_RemoteUE_RB_Identity_r17__root__Type with end) n0
           end t0).

Lemma SL_RemoteUE_RB_Identity_r17__root__helper2 :  forall (y : SL_RemoteUE_RB_Identity_r17__root__Type), SL_RemoteUE_RB_Identity_r17__root__cond y -> choice_cond SL_RemoteUE_RB_Identity_r17__root__list (SL_RemoteUE_RB_Identity_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_RemoteUE_RB_Identity_r17__root__helper3 :  forall (y : SL_RemoteUE_RB_Identity_r17__root__Type), SL_RemoteUE_RB_Identity_r17__root__F2 (SL_RemoteUE_RB_Identity_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_RemoteUE_RB_Identity_r17__root__helper4 : (forall b : choice SL_RemoteUE_RB_Identity_r17__root__list, choice_cond SL_RemoteUE_RB_Identity_r17__root__list b -> SL_RemoteUE_RB_Identity_r17__root__cond (SL_RemoteUE_RB_Identity_r17__root__F2 b) /\ SL_RemoteUE_RB_Identity_r17__root__F1 (SL_RemoteUE_RB_Identity_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_RemoteUE_RB_Identity_r17__root__F1 SL_RemoteUE_RB_Identity_r17__root__F2.
Definition SL_RemoteUE_RB_Identity_r17__root__Format : T_Format SL_RemoteUE_RB_Identity_r17__root__Type SL_RemoteUE_RB_Identity_r17__root__cond :=
  (* Eval compute in *) proj2_format SL_RemoteUE_RB_Identity_r17__root__cond SL_RemoteUE_RB_Identity_r17__root__list__Format SL_RemoteUE_RB_Identity_r17__root__F1 SL_RemoteUE_RB_Identity_r17__root__F2 SL_RemoteUE_RB_Identity_r17__root__helper2 SL_RemoteUE_RB_Identity_r17__root__helper3 SL_RemoteUE_RB_Identity_r17__root__helper4.
Opaque SL_RemoteUE_RB_Identity_r17__root__cond SL_RemoteUE_RB_Identity_r17__root__Format.

Definition SL_RemoteUE_RB_Identity_r17__ext__Format : T_Format SL_RemoteUE_RB_Identity_r17__ext__Type SL_RemoteUE_RB_Identity_r17__ext__cond := empty_format.
Opaque SL_RemoteUE_RB_Identity_r17__ext__cond SL_RemoteUE_RB_Identity_r17__ext__Format.

Definition SL_RemoteUE_RB_Identity_r17__Format : T_Format SL_RemoteUE_RB_Identity_r17__Type SL_RemoteUE_RB_Identity_r17__cond := sum_format SL_RemoteUE_RB_Identity_r17__root__Format SL_RemoteUE_RB_Identity_r17__ext__Format.
Opaque SL_RemoteUE_RB_Identity_r17__cond SL_RemoteUE_RB_Identity_r17__Format.

