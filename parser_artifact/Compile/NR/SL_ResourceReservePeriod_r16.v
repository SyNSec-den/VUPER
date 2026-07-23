Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type : Set :=
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms0
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms100
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms200
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms300
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms400
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms500
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms600
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms700
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms800
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms900
 | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms1000
.
Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__cond := (fun (_ : SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type) => True).
Lemma SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__nat__helper.

Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1 t :=
  match t with
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms0 => 0
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms100 => 1
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms200 => 2
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms300 => 3
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms400 => 4
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms500 => 5
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms600 => 6
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms700 => 7
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms800 => 8
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms900 => 9
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms1000 => 10
  end.
Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F2 n :=
  match n with
  | 0 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms0
  | 1 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms100
  | 2 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms200
  | 3 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms300
  | 4 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms400
  | 5 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms500
  | 6 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms600
  | 7 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms700
  | 8 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms800
  | 9 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms900
  | 10 => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms1000
  | _ => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__ms0
  end.
Lemma SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1F2 : forall x : SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type, (SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1 x <= 10) /\ SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F2 (SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F2F1 : forall (y : nat) (H : y <= 10), SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1 (SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__helper1 : (1 <= 99)%Z.  lia. Qed.
Lemma SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__helper2 : to_bit_sz (Z.to_nat (99 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (99 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__Type := Z.
Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__cond := (fun z => (1 <= z <= 99)%Z).

Inductive SL_ResourceReservePeriod_r16__Type : Set :=
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16 : SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type -> SL_ResourceReservePeriod_r16__Type
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16 : Z -> SL_ResourceReservePeriod_r16__Type
.
Definition SL_ResourceReservePeriod_r16__list : list typ := (
typ_cons SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__cond ::
typ_cons Z SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__cond ::
 nil).
Definition SL_ResourceReservePeriod_r16__cond (c : SL_ResourceReservePeriod_r16__Type) := 
  match c with
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16 t => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__cond t 
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16 t => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__cond t 
  end.

Lemma SL_ResourceReservePeriod_r16__len_helper1 : to_bit_sz (length SL_ResourceReservePeriod_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_ResourceReservePeriod_r16__len_helper2 : 2 <= length2 SL_ResourceReservePeriod_r16__list.
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
Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Format : T_Format SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__nat__Format SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1 SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F2 SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F1F2 SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__F2F1.

Opaque SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__cond SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Format.

Definition SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__Format : T_Format Z SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__cond :=
 ranged_int_format (1) (99) SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__helper1 SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__helper2.

Opaque SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__cond SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__Format.


Definition SL_ResourceReservePeriod_r16__Format_Type := Eval cbn in get_formats SL_ResourceReservePeriod_r16__list.
Definition SL_ResourceReservePeriod_r16__Format_list : SL_ResourceReservePeriod_r16__Format_Type :=
  (SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Format, (SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16__Format, unit__Format)).
Definition SL_ResourceReservePeriod_r16__list__Format := Eval compute in choice_format SL_ResourceReservePeriod_r16__list SL_ResourceReservePeriod_r16__len_helper1 SL_ResourceReservePeriod_r16__len_helper2  SL_ResourceReservePeriod_r16__Format_list.
Definition SL_ResourceReservePeriod_r16__F1 (z : SL_ResourceReservePeriod_r16__Type) : (choice SL_ResourceReservePeriod_r16__list) :=
  match z with
   | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16 t => existT _ 0 t
  | SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16 t => existT _ 1 t
  end.
Definition SL_ResourceReservePeriod_r16__g := (fun n => typ_set (get_nth_typ SL_ResourceReservePeriod_r16__list n)).
Definition SL_ResourceReservePeriod_r16__F2 (y : choice SL_ResourceReservePeriod_r16__list) : SL_ResourceReservePeriod_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_ResourceReservePeriod_r16__g n -> SL_ResourceReservePeriod_r16__Type) with
    | 0 => fun (t : SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16__Type) => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod1_r16 t 
    | 1 => fun (t : Z) => SL_ResourceReservePeriod_r16__sl_ResourceReservePeriod2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_ResourceReservePeriod_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_ResourceReservePeriod_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_ResourceReservePeriod_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_ResourceReservePeriod_r16__Type with end) n0
           end t0).

Lemma SL_ResourceReservePeriod_r16__helper2 :  forall (y : SL_ResourceReservePeriod_r16__Type), SL_ResourceReservePeriod_r16__cond y -> choice_cond SL_ResourceReservePeriod_r16__list (SL_ResourceReservePeriod_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_ResourceReservePeriod_r16__helper3 :  forall (y : SL_ResourceReservePeriod_r16__Type), SL_ResourceReservePeriod_r16__F2 (SL_ResourceReservePeriod_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_ResourceReservePeriod_r16__helper4 : (forall b : choice SL_ResourceReservePeriod_r16__list, choice_cond SL_ResourceReservePeriod_r16__list b -> SL_ResourceReservePeriod_r16__cond (SL_ResourceReservePeriod_r16__F2 b) /\ SL_ResourceReservePeriod_r16__F1 (SL_ResourceReservePeriod_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_ResourceReservePeriod_r16__F1 SL_ResourceReservePeriod_r16__F2.
Definition SL_ResourceReservePeriod_r16__Format : T_Format SL_ResourceReservePeriod_r16__Type SL_ResourceReservePeriod_r16__cond :=
  (* Eval compute in *) proj2_format SL_ResourceReservePeriod_r16__cond SL_ResourceReservePeriod_r16__list__Format SL_ResourceReservePeriod_r16__F1 SL_ResourceReservePeriod_r16__F2 SL_ResourceReservePeriod_r16__helper2 SL_ResourceReservePeriod_r16__helper3 SL_ResourceReservePeriod_r16__helper4.
Opaque SL_ResourceReservePeriod_r16__cond SL_ResourceReservePeriod_r16__Format.

