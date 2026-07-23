Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_PeriodCG_r16__sl_PeriodCG1_r16__Type : Set :=
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms100
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms200
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms300
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms400
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms500
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms600
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms700
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms800
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms900
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms1000
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare6
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare5
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare4
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare3
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare2
 | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare1
.
Definition SL_PeriodCG_r16__sl_PeriodCG1_r16__cond := (fun (_ : SL_PeriodCG_r16__sl_PeriodCG1_r16__Type) => True).
Lemma SL_PeriodCG_r16__sl_PeriodCG1_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PeriodCG_r16__sl_PeriodCG1_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SL_PeriodCG_r16__sl_PeriodCG1_r16__nat__helper.

Definition SL_PeriodCG_r16__sl_PeriodCG1_r16__F1 t :=
  match t with
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms100 => 0
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms200 => 1
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms300 => 2
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms400 => 3
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms500 => 4
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms600 => 5
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms700 => 6
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms800 => 7
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms900 => 8
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__ms1000 => 9
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare6 => 10
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare5 => 11
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare4 => 12
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare3 => 13
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare2 => 14
  | SL_PeriodCG_r16__sl_PeriodCG1_r16__spare1 => 15
  end.
Definition SL_PeriodCG_r16__sl_PeriodCG1_r16__F2 n :=
  match n with
  | 0 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms100
  | 1 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms200
  | 2 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms300
  | 3 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms400
  | 4 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms500
  | 5 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms600
  | 6 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms700
  | 7 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms800
  | 8 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms900
  | 9 => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms1000
  | 10 => SL_PeriodCG_r16__sl_PeriodCG1_r16__spare6
  | 11 => SL_PeriodCG_r16__sl_PeriodCG1_r16__spare5
  | 12 => SL_PeriodCG_r16__sl_PeriodCG1_r16__spare4
  | 13 => SL_PeriodCG_r16__sl_PeriodCG1_r16__spare3
  | 14 => SL_PeriodCG_r16__sl_PeriodCG1_r16__spare2
  | 15 => SL_PeriodCG_r16__sl_PeriodCG1_r16__spare1
  | _ => SL_PeriodCG_r16__sl_PeriodCG1_r16__ms100
  end.
Lemma SL_PeriodCG_r16__sl_PeriodCG1_r16__F1F2 : forall x : SL_PeriodCG_r16__sl_PeriodCG1_r16__Type, (SL_PeriodCG_r16__sl_PeriodCG1_r16__F1 x <= 15) /\ SL_PeriodCG_r16__sl_PeriodCG1_r16__F2 (SL_PeriodCG_r16__sl_PeriodCG1_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PeriodCG_r16__sl_PeriodCG1_r16__F2F1 : forall (y : nat) (H : y <= 15), SL_PeriodCG_r16__sl_PeriodCG1_r16__F1 (SL_PeriodCG_r16__sl_PeriodCG1_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_PeriodCG_r16__sl_PeriodCG2_r16__helper1 : (1 <= 99)%Z.  lia. Qed.
Lemma SL_PeriodCG_r16__sl_PeriodCG2_r16__helper2 : to_bit_sz (Z.to_nat (99 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (99 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PeriodCG_r16__sl_PeriodCG2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PeriodCG_r16__sl_PeriodCG2_r16__Type := Z.
Definition SL_PeriodCG_r16__sl_PeriodCG2_r16__cond := (fun z => (1 <= z <= 99)%Z).

Inductive SL_PeriodCG_r16__Type : Set :=
  | SL_PeriodCG_r16__sl_PeriodCG1_r16 : SL_PeriodCG_r16__sl_PeriodCG1_r16__Type -> SL_PeriodCG_r16__Type
  | SL_PeriodCG_r16__sl_PeriodCG2_r16 : Z -> SL_PeriodCG_r16__Type
.
Definition SL_PeriodCG_r16__list : list typ := (
typ_cons SL_PeriodCG_r16__sl_PeriodCG1_r16__Type SL_PeriodCG_r16__sl_PeriodCG1_r16__cond ::
typ_cons Z SL_PeriodCG_r16__sl_PeriodCG2_r16__cond ::
 nil).
Definition SL_PeriodCG_r16__cond (c : SL_PeriodCG_r16__Type) := 
  match c with
  | SL_PeriodCG_r16__sl_PeriodCG1_r16 t => SL_PeriodCG_r16__sl_PeriodCG1_r16__cond t 
  | SL_PeriodCG_r16__sl_PeriodCG2_r16 t => SL_PeriodCG_r16__sl_PeriodCG2_r16__cond t 
  end.

Lemma SL_PeriodCG_r16__len_helper1 : to_bit_sz (length SL_PeriodCG_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_PeriodCG_r16__len_helper2 : 2 <= length2 SL_PeriodCG_r16__list.
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
Definition SL_PeriodCG_r16__sl_PeriodCG1_r16__Format : T_Format SL_PeriodCG_r16__sl_PeriodCG1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PeriodCG_r16__sl_PeriodCG1_r16__nat__Format SL_PeriodCG_r16__sl_PeriodCG1_r16__F1 SL_PeriodCG_r16__sl_PeriodCG1_r16__F2 SL_PeriodCG_r16__sl_PeriodCG1_r16__F1F2 SL_PeriodCG_r16__sl_PeriodCG1_r16__F2F1.

Opaque SL_PeriodCG_r16__sl_PeriodCG1_r16__cond SL_PeriodCG_r16__sl_PeriodCG1_r16__Format.

Definition SL_PeriodCG_r16__sl_PeriodCG2_r16__Format : T_Format Z SL_PeriodCG_r16__sl_PeriodCG2_r16__cond :=
 ranged_int_format (1) (99) SL_PeriodCG_r16__sl_PeriodCG2_r16__helper1 SL_PeriodCG_r16__sl_PeriodCG2_r16__helper2.

Opaque SL_PeriodCG_r16__sl_PeriodCG2_r16__cond SL_PeriodCG_r16__sl_PeriodCG2_r16__Format.


Definition SL_PeriodCG_r16__Format_Type := Eval cbn in get_formats SL_PeriodCG_r16__list.
Definition SL_PeriodCG_r16__Format_list : SL_PeriodCG_r16__Format_Type :=
  (SL_PeriodCG_r16__sl_PeriodCG1_r16__Format, (SL_PeriodCG_r16__sl_PeriodCG2_r16__Format, unit__Format)).
Definition SL_PeriodCG_r16__list__Format := Eval compute in choice_format SL_PeriodCG_r16__list SL_PeriodCG_r16__len_helper1 SL_PeriodCG_r16__len_helper2  SL_PeriodCG_r16__Format_list.
Definition SL_PeriodCG_r16__F1 (z : SL_PeriodCG_r16__Type) : (choice SL_PeriodCG_r16__list) :=
  match z with
   | SL_PeriodCG_r16__sl_PeriodCG1_r16 t => existT _ 0 t
  | SL_PeriodCG_r16__sl_PeriodCG2_r16 t => existT _ 1 t
  end.
Definition SL_PeriodCG_r16__g := (fun n => typ_set (get_nth_typ SL_PeriodCG_r16__list n)).
Definition SL_PeriodCG_r16__F2 (y : choice SL_PeriodCG_r16__list) : SL_PeriodCG_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_PeriodCG_r16__g n -> SL_PeriodCG_r16__Type) with
    | 0 => fun (t : SL_PeriodCG_r16__sl_PeriodCG1_r16__Type) => SL_PeriodCG_r16__sl_PeriodCG1_r16 t 
    | 1 => fun (t : Z) => SL_PeriodCG_r16__sl_PeriodCG2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_PeriodCG_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_PeriodCG_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_PeriodCG_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_PeriodCG_r16__Type with end) n0
           end t0).

Lemma SL_PeriodCG_r16__helper2 :  forall (y : SL_PeriodCG_r16__Type), SL_PeriodCG_r16__cond y -> choice_cond SL_PeriodCG_r16__list (SL_PeriodCG_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_PeriodCG_r16__helper3 :  forall (y : SL_PeriodCG_r16__Type), SL_PeriodCG_r16__F2 (SL_PeriodCG_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_PeriodCG_r16__helper4 : (forall b : choice SL_PeriodCG_r16__list, choice_cond SL_PeriodCG_r16__list b -> SL_PeriodCG_r16__cond (SL_PeriodCG_r16__F2 b) /\ SL_PeriodCG_r16__F1 (SL_PeriodCG_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_PeriodCG_r16__F1 SL_PeriodCG_r16__F2.
Definition SL_PeriodCG_r16__Format : T_Format SL_PeriodCG_r16__Type SL_PeriodCG_r16__cond :=
  (* Eval compute in *) proj2_format SL_PeriodCG_r16__cond SL_PeriodCG_r16__list__Format SL_PeriodCG_r16__F1 SL_PeriodCG_r16__F2 SL_PeriodCG_r16__helper2 SL_PeriodCG_r16__helper3 SL_PeriodCG_r16__helper4.
Opaque SL_PeriodCG_r16__cond SL_PeriodCG_r16__Format.

