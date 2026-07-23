Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SRS_PeriodicityAndOffsetExt_r16__sl128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffsetExt_r16__sl128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffsetExt_r16__sl128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffsetExt_r16__sl128__Type := Z.
Definition SRS_PeriodicityAndOffsetExt_r16__sl128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma SRS_PeriodicityAndOffsetExt_r16__sl256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffsetExt_r16__sl256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffsetExt_r16__sl256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffsetExt_r16__sl256__Type := Z.
Definition SRS_PeriodicityAndOffsetExt_r16__sl256__cond := (fun z => (0 <= z <= 255)%Z).
Lemma SRS_PeriodicityAndOffsetExt_r16__sl512__helper1 : (0 <= 511)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffsetExt_r16__sl512__helper2 : to_bit_sz (Z.to_nat (511 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (511 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffsetExt_r16__sl512__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffsetExt_r16__sl512__Type := Z.
Definition SRS_PeriodicityAndOffsetExt_r16__sl512__cond := (fun z => (0 <= z <= 511)%Z).
Lemma SRS_PeriodicityAndOffsetExt_r16__sl20480__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffsetExt_r16__sl20480__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffsetExt_r16__sl20480__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffsetExt_r16__sl20480__Type := Z.
Definition SRS_PeriodicityAndOffsetExt_r16__sl20480__cond := (fun z => (0 <= z <= 20479)%Z).

Inductive SRS_PeriodicityAndOffsetExt_r16__Type : Set :=
  | SRS_PeriodicityAndOffsetExt_r16__sl128 : Z -> SRS_PeriodicityAndOffsetExt_r16__Type
  | SRS_PeriodicityAndOffsetExt_r16__sl256 : Z -> SRS_PeriodicityAndOffsetExt_r16__Type
  | SRS_PeriodicityAndOffsetExt_r16__sl512 : Z -> SRS_PeriodicityAndOffsetExt_r16__Type
  | SRS_PeriodicityAndOffsetExt_r16__sl20480 : Z -> SRS_PeriodicityAndOffsetExt_r16__Type
.
Definition SRS_PeriodicityAndOffsetExt_r16__list : list typ := (
typ_cons Z SRS_PeriodicityAndOffsetExt_r16__sl128__cond ::
typ_cons Z SRS_PeriodicityAndOffsetExt_r16__sl256__cond ::
typ_cons Z SRS_PeriodicityAndOffsetExt_r16__sl512__cond ::
typ_cons Z SRS_PeriodicityAndOffsetExt_r16__sl20480__cond ::
 nil).
Definition SRS_PeriodicityAndOffsetExt_r16__cond (c : SRS_PeriodicityAndOffsetExt_r16__Type) := 
  match c with
  | SRS_PeriodicityAndOffsetExt_r16__sl128 t => SRS_PeriodicityAndOffsetExt_r16__sl128__cond t 
  | SRS_PeriodicityAndOffsetExt_r16__sl256 t => SRS_PeriodicityAndOffsetExt_r16__sl256__cond t 
  | SRS_PeriodicityAndOffsetExt_r16__sl512 t => SRS_PeriodicityAndOffsetExt_r16__sl512__cond t 
  | SRS_PeriodicityAndOffsetExt_r16__sl20480 t => SRS_PeriodicityAndOffsetExt_r16__sl20480__cond t 
  end.

Lemma SRS_PeriodicityAndOffsetExt_r16__len_helper1 : to_bit_sz (length SRS_PeriodicityAndOffsetExt_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_PeriodicityAndOffsetExt_r16__len_helper2 : 2 <= length2 SRS_PeriodicityAndOffsetExt_r16__list.
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
Definition SRS_PeriodicityAndOffsetExt_r16__sl128__Format : T_Format Z SRS_PeriodicityAndOffsetExt_r16__sl128__cond :=
 ranged_int_format (0) (127) SRS_PeriodicityAndOffsetExt_r16__sl128__helper1 SRS_PeriodicityAndOffsetExt_r16__sl128__helper2.

Opaque SRS_PeriodicityAndOffsetExt_r16__sl128__cond SRS_PeriodicityAndOffsetExt_r16__sl128__Format.

Definition SRS_PeriodicityAndOffsetExt_r16__sl256__Format : T_Format Z SRS_PeriodicityAndOffsetExt_r16__sl256__cond :=
 ranged_int_format (0) (255) SRS_PeriodicityAndOffsetExt_r16__sl256__helper1 SRS_PeriodicityAndOffsetExt_r16__sl256__helper2.

Opaque SRS_PeriodicityAndOffsetExt_r16__sl256__cond SRS_PeriodicityAndOffsetExt_r16__sl256__Format.

Definition SRS_PeriodicityAndOffsetExt_r16__sl512__Format : T_Format Z SRS_PeriodicityAndOffsetExt_r16__sl512__cond :=
 ranged_int_format (0) (511) SRS_PeriodicityAndOffsetExt_r16__sl512__helper1 SRS_PeriodicityAndOffsetExt_r16__sl512__helper2.

Opaque SRS_PeriodicityAndOffsetExt_r16__sl512__cond SRS_PeriodicityAndOffsetExt_r16__sl512__Format.

Definition SRS_PeriodicityAndOffsetExt_r16__sl20480__Format : T_Format Z SRS_PeriodicityAndOffsetExt_r16__sl20480__cond :=
 ranged_int_format (0) (20479) SRS_PeriodicityAndOffsetExt_r16__sl20480__helper1 SRS_PeriodicityAndOffsetExt_r16__sl20480__helper2.

Opaque SRS_PeriodicityAndOffsetExt_r16__sl20480__cond SRS_PeriodicityAndOffsetExt_r16__sl20480__Format.


Definition SRS_PeriodicityAndOffsetExt_r16__Format_Type := Eval cbn in get_formats SRS_PeriodicityAndOffsetExt_r16__list.
Definition SRS_PeriodicityAndOffsetExt_r16__Format_list : SRS_PeriodicityAndOffsetExt_r16__Format_Type :=
  (SRS_PeriodicityAndOffsetExt_r16__sl128__Format, (SRS_PeriodicityAndOffsetExt_r16__sl256__Format, (SRS_PeriodicityAndOffsetExt_r16__sl512__Format, (SRS_PeriodicityAndOffsetExt_r16__sl20480__Format, unit__Format)))).
Definition SRS_PeriodicityAndOffsetExt_r16__list__Format := Eval compute in choice_format SRS_PeriodicityAndOffsetExt_r16__list SRS_PeriodicityAndOffsetExt_r16__len_helper1 SRS_PeriodicityAndOffsetExt_r16__len_helper2  SRS_PeriodicityAndOffsetExt_r16__Format_list.
Definition SRS_PeriodicityAndOffsetExt_r16__F1 (z : SRS_PeriodicityAndOffsetExt_r16__Type) : (choice SRS_PeriodicityAndOffsetExt_r16__list) :=
  match z with
   | SRS_PeriodicityAndOffsetExt_r16__sl128 t => existT _ 0 t
  | SRS_PeriodicityAndOffsetExt_r16__sl256 t => existT _ 1 t
  | SRS_PeriodicityAndOffsetExt_r16__sl512 t => existT _ 2 t
  | SRS_PeriodicityAndOffsetExt_r16__sl20480 t => existT _ 3 t
  end.
Definition SRS_PeriodicityAndOffsetExt_r16__g := (fun n => typ_set (get_nth_typ SRS_PeriodicityAndOffsetExt_r16__list n)).
Definition SRS_PeriodicityAndOffsetExt_r16__F2 (y : choice SRS_PeriodicityAndOffsetExt_r16__list) : SRS_PeriodicityAndOffsetExt_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_PeriodicityAndOffsetExt_r16__g n -> SRS_PeriodicityAndOffsetExt_r16__Type) with
    | 0 => fun (t : Z) => SRS_PeriodicityAndOffsetExt_r16__sl128 t 
    | 1 => fun (t : Z) => SRS_PeriodicityAndOffsetExt_r16__sl256 t 
    | 2 => fun (t : Z) => SRS_PeriodicityAndOffsetExt_r16__sl512 t 
    | 3 => fun (t : Z) => SRS_PeriodicityAndOffsetExt_r16__sl20480 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : SRS_PeriodicityAndOffsetExt_r16__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ SRS_PeriodicityAndOffsetExt_r16__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_PeriodicityAndOffsetExt_r16__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return SRS_PeriodicityAndOffsetExt_r16__Type with end) n0
           end t0).

Lemma SRS_PeriodicityAndOffsetExt_r16__helper2 :  forall (y : SRS_PeriodicityAndOffsetExt_r16__Type), SRS_PeriodicityAndOffsetExt_r16__cond y -> choice_cond SRS_PeriodicityAndOffsetExt_r16__list (SRS_PeriodicityAndOffsetExt_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_PeriodicityAndOffsetExt_r16__helper3 :  forall (y : SRS_PeriodicityAndOffsetExt_r16__Type), SRS_PeriodicityAndOffsetExt_r16__F2 (SRS_PeriodicityAndOffsetExt_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_PeriodicityAndOffsetExt_r16__helper4 : (forall b : choice SRS_PeriodicityAndOffsetExt_r16__list, choice_cond SRS_PeriodicityAndOffsetExt_r16__list b -> SRS_PeriodicityAndOffsetExt_r16__cond (SRS_PeriodicityAndOffsetExt_r16__F2 b) /\ SRS_PeriodicityAndOffsetExt_r16__F1 (SRS_PeriodicityAndOffsetExt_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_PeriodicityAndOffsetExt_r16__F1 SRS_PeriodicityAndOffsetExt_r16__F2.
Definition SRS_PeriodicityAndOffsetExt_r16__Format : T_Format SRS_PeriodicityAndOffsetExt_r16__Type SRS_PeriodicityAndOffsetExt_r16__cond :=
  (* Eval compute in *) proj2_format SRS_PeriodicityAndOffsetExt_r16__cond SRS_PeriodicityAndOffsetExt_r16__list__Format SRS_PeriodicityAndOffsetExt_r16__F1 SRS_PeriodicityAndOffsetExt_r16__F2 SRS_PeriodicityAndOffsetExt_r16__helper2 SRS_PeriodicityAndOffsetExt_r16__helper3 SRS_PeriodicityAndOffsetExt_r16__helper4.
Opaque SRS_PeriodicityAndOffsetExt_r16__cond SRS_PeriodicityAndOffsetExt_r16__Format.

