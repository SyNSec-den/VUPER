Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SupportedBandwidth_v1700__fr1_r17__Type : Set :=
 | SupportedBandwidth_v1700__fr1_r17__mhz5
 | SupportedBandwidth_v1700__fr1_r17__mhz10
 | SupportedBandwidth_v1700__fr1_r17__mhz15
 | SupportedBandwidth_v1700__fr1_r17__mhz20
 | SupportedBandwidth_v1700__fr1_r17__mhz25
 | SupportedBandwidth_v1700__fr1_r17__mhz30
 | SupportedBandwidth_v1700__fr1_r17__mhz35
 | SupportedBandwidth_v1700__fr1_r17__mhz40
 | SupportedBandwidth_v1700__fr1_r17__mhz45
 | SupportedBandwidth_v1700__fr1_r17__mhz50
 | SupportedBandwidth_v1700__fr1_r17__mhz60
 | SupportedBandwidth_v1700__fr1_r17__mhz70
 | SupportedBandwidth_v1700__fr1_r17__mhz80
 | SupportedBandwidth_v1700__fr1_r17__mhz90
 | SupportedBandwidth_v1700__fr1_r17__mhz100
.
Definition SupportedBandwidth_v1700__fr1_r17__cond := (fun (_ : SupportedBandwidth_v1700__fr1_r17__Type) => True).
Lemma SupportedBandwidth_v1700__fr1_r17__nat__helper : to_bit_sz 14 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SupportedBandwidth_v1700__fr1_r17__nat__Format : T_Format nat (fun z => (z <= 14)) :=
  nat_enum_format 14 SupportedBandwidth_v1700__fr1_r17__nat__helper.

Definition SupportedBandwidth_v1700__fr1_r17__F1 t :=
  match t with
  | SupportedBandwidth_v1700__fr1_r17__mhz5 => 0
  | SupportedBandwidth_v1700__fr1_r17__mhz10 => 1
  | SupportedBandwidth_v1700__fr1_r17__mhz15 => 2
  | SupportedBandwidth_v1700__fr1_r17__mhz20 => 3
  | SupportedBandwidth_v1700__fr1_r17__mhz25 => 4
  | SupportedBandwidth_v1700__fr1_r17__mhz30 => 5
  | SupportedBandwidth_v1700__fr1_r17__mhz35 => 6
  | SupportedBandwidth_v1700__fr1_r17__mhz40 => 7
  | SupportedBandwidth_v1700__fr1_r17__mhz45 => 8
  | SupportedBandwidth_v1700__fr1_r17__mhz50 => 9
  | SupportedBandwidth_v1700__fr1_r17__mhz60 => 10
  | SupportedBandwidth_v1700__fr1_r17__mhz70 => 11
  | SupportedBandwidth_v1700__fr1_r17__mhz80 => 12
  | SupportedBandwidth_v1700__fr1_r17__mhz90 => 13
  | SupportedBandwidth_v1700__fr1_r17__mhz100 => 14
  end.
Definition SupportedBandwidth_v1700__fr1_r17__F2 n :=
  match n with
  | 0 => SupportedBandwidth_v1700__fr1_r17__mhz5
  | 1 => SupportedBandwidth_v1700__fr1_r17__mhz10
  | 2 => SupportedBandwidth_v1700__fr1_r17__mhz15
  | 3 => SupportedBandwidth_v1700__fr1_r17__mhz20
  | 4 => SupportedBandwidth_v1700__fr1_r17__mhz25
  | 5 => SupportedBandwidth_v1700__fr1_r17__mhz30
  | 6 => SupportedBandwidth_v1700__fr1_r17__mhz35
  | 7 => SupportedBandwidth_v1700__fr1_r17__mhz40
  | 8 => SupportedBandwidth_v1700__fr1_r17__mhz45
  | 9 => SupportedBandwidth_v1700__fr1_r17__mhz50
  | 10 => SupportedBandwidth_v1700__fr1_r17__mhz60
  | 11 => SupportedBandwidth_v1700__fr1_r17__mhz70
  | 12 => SupportedBandwidth_v1700__fr1_r17__mhz80
  | 13 => SupportedBandwidth_v1700__fr1_r17__mhz90
  | 14 => SupportedBandwidth_v1700__fr1_r17__mhz100
  | _ => SupportedBandwidth_v1700__fr1_r17__mhz5
  end.
Lemma SupportedBandwidth_v1700__fr1_r17__F1F2 : forall x : SupportedBandwidth_v1700__fr1_r17__Type, (SupportedBandwidth_v1700__fr1_r17__F1 x <= 14) /\ SupportedBandwidth_v1700__fr1_r17__F2 (SupportedBandwidth_v1700__fr1_r17__F1 x) = x. imp_solve. Qed.
Lemma SupportedBandwidth_v1700__fr1_r17__F2F1 : forall (y : nat) (H : y <= 14), SupportedBandwidth_v1700__fr1_r17__F1 (SupportedBandwidth_v1700__fr1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SupportedBandwidth_v1700__fr2_r17__Type : Set :=
 | SupportedBandwidth_v1700__fr2_r17__mhz50
 | SupportedBandwidth_v1700__fr2_r17__mhz100
 | SupportedBandwidth_v1700__fr2_r17__mhz200
 | SupportedBandwidth_v1700__fr2_r17__mhz400
 | SupportedBandwidth_v1700__fr2_r17__mhz800
 | SupportedBandwidth_v1700__fr2_r17__mhz1600
 | SupportedBandwidth_v1700__fr2_r17__mhz2000
.
Definition SupportedBandwidth_v1700__fr2_r17__cond := (fun (_ : SupportedBandwidth_v1700__fr2_r17__Type) => True).
Lemma SupportedBandwidth_v1700__fr2_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SupportedBandwidth_v1700__fr2_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SupportedBandwidth_v1700__fr2_r17__nat__helper.

Definition SupportedBandwidth_v1700__fr2_r17__F1 t :=
  match t with
  | SupportedBandwidth_v1700__fr2_r17__mhz50 => 0
  | SupportedBandwidth_v1700__fr2_r17__mhz100 => 1
  | SupportedBandwidth_v1700__fr2_r17__mhz200 => 2
  | SupportedBandwidth_v1700__fr2_r17__mhz400 => 3
  | SupportedBandwidth_v1700__fr2_r17__mhz800 => 4
  | SupportedBandwidth_v1700__fr2_r17__mhz1600 => 5
  | SupportedBandwidth_v1700__fr2_r17__mhz2000 => 6
  end.
Definition SupportedBandwidth_v1700__fr2_r17__F2 n :=
  match n with
  | 0 => SupportedBandwidth_v1700__fr2_r17__mhz50
  | 1 => SupportedBandwidth_v1700__fr2_r17__mhz100
  | 2 => SupportedBandwidth_v1700__fr2_r17__mhz200
  | 3 => SupportedBandwidth_v1700__fr2_r17__mhz400
  | 4 => SupportedBandwidth_v1700__fr2_r17__mhz800
  | 5 => SupportedBandwidth_v1700__fr2_r17__mhz1600
  | 6 => SupportedBandwidth_v1700__fr2_r17__mhz2000
  | _ => SupportedBandwidth_v1700__fr2_r17__mhz50
  end.
Lemma SupportedBandwidth_v1700__fr2_r17__F1F2 : forall x : SupportedBandwidth_v1700__fr2_r17__Type, (SupportedBandwidth_v1700__fr2_r17__F1 x <= 6) /\ SupportedBandwidth_v1700__fr2_r17__F2 (SupportedBandwidth_v1700__fr2_r17__F1 x) = x. imp_solve. Qed.
Lemma SupportedBandwidth_v1700__fr2_r17__F2F1 : forall (y : nat) (H : y <= 6), SupportedBandwidth_v1700__fr2_r17__F1 (SupportedBandwidth_v1700__fr2_r17__F2 y) = y. enum_solve H y. Qed.


Inductive SupportedBandwidth_v1700__Type : Set :=
  | SupportedBandwidth_v1700__fr1_r17 : SupportedBandwidth_v1700__fr1_r17__Type -> SupportedBandwidth_v1700__Type
  | SupportedBandwidth_v1700__fr2_r17 : SupportedBandwidth_v1700__fr2_r17__Type -> SupportedBandwidth_v1700__Type
.
Definition SupportedBandwidth_v1700__list : list typ := (
typ_cons SupportedBandwidth_v1700__fr1_r17__Type SupportedBandwidth_v1700__fr1_r17__cond ::
typ_cons SupportedBandwidth_v1700__fr2_r17__Type SupportedBandwidth_v1700__fr2_r17__cond ::
 nil).
Definition SupportedBandwidth_v1700__cond (c : SupportedBandwidth_v1700__Type) := 
  match c with
  | SupportedBandwidth_v1700__fr1_r17 t => SupportedBandwidth_v1700__fr1_r17__cond t 
  | SupportedBandwidth_v1700__fr2_r17 t => SupportedBandwidth_v1700__fr2_r17__cond t 
  end.

Lemma SupportedBandwidth_v1700__len_helper1 : to_bit_sz (length SupportedBandwidth_v1700__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SupportedBandwidth_v1700__len_helper2 : 2 <= length2 SupportedBandwidth_v1700__list.
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
Definition SupportedBandwidth_v1700__fr1_r17__Format : T_Format SupportedBandwidth_v1700__fr1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SupportedBandwidth_v1700__fr1_r17__nat__Format SupportedBandwidth_v1700__fr1_r17__F1 SupportedBandwidth_v1700__fr1_r17__F2 SupportedBandwidth_v1700__fr1_r17__F1F2 SupportedBandwidth_v1700__fr1_r17__F2F1.

Opaque SupportedBandwidth_v1700__fr1_r17__cond SupportedBandwidth_v1700__fr1_r17__Format.

Definition SupportedBandwidth_v1700__fr2_r17__Format : T_Format SupportedBandwidth_v1700__fr2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SupportedBandwidth_v1700__fr2_r17__nat__Format SupportedBandwidth_v1700__fr2_r17__F1 SupportedBandwidth_v1700__fr2_r17__F2 SupportedBandwidth_v1700__fr2_r17__F1F2 SupportedBandwidth_v1700__fr2_r17__F2F1.

Opaque SupportedBandwidth_v1700__fr2_r17__cond SupportedBandwidth_v1700__fr2_r17__Format.


Definition SupportedBandwidth_v1700__Format_Type := Eval cbn in get_formats SupportedBandwidth_v1700__list.
Definition SupportedBandwidth_v1700__Format_list : SupportedBandwidth_v1700__Format_Type :=
  (SupportedBandwidth_v1700__fr1_r17__Format, (SupportedBandwidth_v1700__fr2_r17__Format, unit__Format)).
Definition SupportedBandwidth_v1700__list__Format := Eval compute in choice_format SupportedBandwidth_v1700__list SupportedBandwidth_v1700__len_helper1 SupportedBandwidth_v1700__len_helper2  SupportedBandwidth_v1700__Format_list.
Definition SupportedBandwidth_v1700__F1 (z : SupportedBandwidth_v1700__Type) : (choice SupportedBandwidth_v1700__list) :=
  match z with
   | SupportedBandwidth_v1700__fr1_r17 t => existT _ 0 t
  | SupportedBandwidth_v1700__fr2_r17 t => existT _ 1 t
  end.
Definition SupportedBandwidth_v1700__g := (fun n => typ_set (get_nth_typ SupportedBandwidth_v1700__list n)).
Definition SupportedBandwidth_v1700__F2 (y : choice SupportedBandwidth_v1700__list) : SupportedBandwidth_v1700__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SupportedBandwidth_v1700__g n -> SupportedBandwidth_v1700__Type) with
    | 0 => fun (t : SupportedBandwidth_v1700__fr1_r17__Type) => SupportedBandwidth_v1700__fr1_r17 t 
    | 1 => fun (t : SupportedBandwidth_v1700__fr2_r17__Type) => SupportedBandwidth_v1700__fr2_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SupportedBandwidth_v1700__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SupportedBandwidth_v1700__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SupportedBandwidth_v1700__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SupportedBandwidth_v1700__Type with end) n0
           end t0).

Lemma SupportedBandwidth_v1700__helper2 :  forall (y : SupportedBandwidth_v1700__Type), SupportedBandwidth_v1700__cond y -> choice_cond SupportedBandwidth_v1700__list (SupportedBandwidth_v1700__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SupportedBandwidth_v1700__helper3 :  forall (y : SupportedBandwidth_v1700__Type), SupportedBandwidth_v1700__F2 (SupportedBandwidth_v1700__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SupportedBandwidth_v1700__helper4 : (forall b : choice SupportedBandwidth_v1700__list, choice_cond SupportedBandwidth_v1700__list b -> SupportedBandwidth_v1700__cond (SupportedBandwidth_v1700__F2 b) /\ SupportedBandwidth_v1700__F1 (SupportedBandwidth_v1700__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SupportedBandwidth_v1700__F1 SupportedBandwidth_v1700__F2.
Definition SupportedBandwidth_v1700__Format : T_Format SupportedBandwidth_v1700__Type SupportedBandwidth_v1700__cond :=
  (* Eval compute in *) proj2_format SupportedBandwidth_v1700__cond SupportedBandwidth_v1700__list__Format SupportedBandwidth_v1700__F1 SupportedBandwidth_v1700__F2 SupportedBandwidth_v1700__helper2 SupportedBandwidth_v1700__helper3 SupportedBandwidth_v1700__helper4.
Opaque SupportedBandwidth_v1700__cond SupportedBandwidth_v1700__Format.

