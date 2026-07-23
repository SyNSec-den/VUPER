Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SupportedBandwidth__fr1__Type : Set :=
 | SupportedBandwidth__fr1__mhz5
 | SupportedBandwidth__fr1__mhz10
 | SupportedBandwidth__fr1__mhz15
 | SupportedBandwidth__fr1__mhz20
 | SupportedBandwidth__fr1__mhz25
 | SupportedBandwidth__fr1__mhz30
 | SupportedBandwidth__fr1__mhz40
 | SupportedBandwidth__fr1__mhz50
 | SupportedBandwidth__fr1__mhz60
 | SupportedBandwidth__fr1__mhz80
 | SupportedBandwidth__fr1__mhz100
.
Definition SupportedBandwidth__fr1__cond := (fun (_ : SupportedBandwidth__fr1__Type) => True).
Lemma SupportedBandwidth__fr1__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SupportedBandwidth__fr1__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 SupportedBandwidth__fr1__nat__helper.

Definition SupportedBandwidth__fr1__F1 t :=
  match t with
  | SupportedBandwidth__fr1__mhz5 => 0
  | SupportedBandwidth__fr1__mhz10 => 1
  | SupportedBandwidth__fr1__mhz15 => 2
  | SupportedBandwidth__fr1__mhz20 => 3
  | SupportedBandwidth__fr1__mhz25 => 4
  | SupportedBandwidth__fr1__mhz30 => 5
  | SupportedBandwidth__fr1__mhz40 => 6
  | SupportedBandwidth__fr1__mhz50 => 7
  | SupportedBandwidth__fr1__mhz60 => 8
  | SupportedBandwidth__fr1__mhz80 => 9
  | SupportedBandwidth__fr1__mhz100 => 10
  end.
Definition SupportedBandwidth__fr1__F2 n :=
  match n with
  | 0 => SupportedBandwidth__fr1__mhz5
  | 1 => SupportedBandwidth__fr1__mhz10
  | 2 => SupportedBandwidth__fr1__mhz15
  | 3 => SupportedBandwidth__fr1__mhz20
  | 4 => SupportedBandwidth__fr1__mhz25
  | 5 => SupportedBandwidth__fr1__mhz30
  | 6 => SupportedBandwidth__fr1__mhz40
  | 7 => SupportedBandwidth__fr1__mhz50
  | 8 => SupportedBandwidth__fr1__mhz60
  | 9 => SupportedBandwidth__fr1__mhz80
  | 10 => SupportedBandwidth__fr1__mhz100
  | _ => SupportedBandwidth__fr1__mhz5
  end.
Lemma SupportedBandwidth__fr1__F1F2 : forall x : SupportedBandwidth__fr1__Type, (SupportedBandwidth__fr1__F1 x <= 10) /\ SupportedBandwidth__fr1__F2 (SupportedBandwidth__fr1__F1 x) = x. imp_solve. Qed.
Lemma SupportedBandwidth__fr1__F2F1 : forall (y : nat) (H : y <= 10), SupportedBandwidth__fr1__F1 (SupportedBandwidth__fr1__F2 y) = y. enum_solve H y. Qed.

Inductive SupportedBandwidth__fr2__Type : Set :=
 | SupportedBandwidth__fr2__mhz50
 | SupportedBandwidth__fr2__mhz100
 | SupportedBandwidth__fr2__mhz200
 | SupportedBandwidth__fr2__mhz400
.
Definition SupportedBandwidth__fr2__cond := (fun (_ : SupportedBandwidth__fr2__Type) => True).
Lemma SupportedBandwidth__fr2__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SupportedBandwidth__fr2__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SupportedBandwidth__fr2__nat__helper.

Definition SupportedBandwidth__fr2__F1 t :=
  match t with
  | SupportedBandwidth__fr2__mhz50 => 0
  | SupportedBandwidth__fr2__mhz100 => 1
  | SupportedBandwidth__fr2__mhz200 => 2
  | SupportedBandwidth__fr2__mhz400 => 3
  end.
Definition SupportedBandwidth__fr2__F2 n :=
  match n with
  | 0 => SupportedBandwidth__fr2__mhz50
  | 1 => SupportedBandwidth__fr2__mhz100
  | 2 => SupportedBandwidth__fr2__mhz200
  | 3 => SupportedBandwidth__fr2__mhz400
  | _ => SupportedBandwidth__fr2__mhz50
  end.
Lemma SupportedBandwidth__fr2__F1F2 : forall x : SupportedBandwidth__fr2__Type, (SupportedBandwidth__fr2__F1 x <= 3) /\ SupportedBandwidth__fr2__F2 (SupportedBandwidth__fr2__F1 x) = x. imp_solve. Qed.
Lemma SupportedBandwidth__fr2__F2F1 : forall (y : nat) (H : y <= 3), SupportedBandwidth__fr2__F1 (SupportedBandwidth__fr2__F2 y) = y. enum_solve H y. Qed.


Inductive SupportedBandwidth__Type : Set :=
  | SupportedBandwidth__fr1 : SupportedBandwidth__fr1__Type -> SupportedBandwidth__Type
  | SupportedBandwidth__fr2 : SupportedBandwidth__fr2__Type -> SupportedBandwidth__Type
.
Definition SupportedBandwidth__list : list typ := (
typ_cons SupportedBandwidth__fr1__Type SupportedBandwidth__fr1__cond ::
typ_cons SupportedBandwidth__fr2__Type SupportedBandwidth__fr2__cond ::
 nil).
Definition SupportedBandwidth__cond (c : SupportedBandwidth__Type) := 
  match c with
  | SupportedBandwidth__fr1 t => SupportedBandwidth__fr1__cond t 
  | SupportedBandwidth__fr2 t => SupportedBandwidth__fr2__cond t 
  end.

Lemma SupportedBandwidth__len_helper1 : to_bit_sz (length SupportedBandwidth__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SupportedBandwidth__len_helper2 : 2 <= length2 SupportedBandwidth__list.
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
Definition SupportedBandwidth__fr1__Format : T_Format SupportedBandwidth__fr1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SupportedBandwidth__fr1__nat__Format SupportedBandwidth__fr1__F1 SupportedBandwidth__fr1__F2 SupportedBandwidth__fr1__F1F2 SupportedBandwidth__fr1__F2F1.

Opaque SupportedBandwidth__fr1__cond SupportedBandwidth__fr1__Format.

Definition SupportedBandwidth__fr2__Format : T_Format SupportedBandwidth__fr2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SupportedBandwidth__fr2__nat__Format SupportedBandwidth__fr2__F1 SupportedBandwidth__fr2__F2 SupportedBandwidth__fr2__F1F2 SupportedBandwidth__fr2__F2F1.

Opaque SupportedBandwidth__fr2__cond SupportedBandwidth__fr2__Format.


Definition SupportedBandwidth__Format_Type := Eval cbn in get_formats SupportedBandwidth__list.
Definition SupportedBandwidth__Format_list : SupportedBandwidth__Format_Type :=
  (SupportedBandwidth__fr1__Format, (SupportedBandwidth__fr2__Format, unit__Format)).
Definition SupportedBandwidth__list__Format := Eval compute in choice_format SupportedBandwidth__list SupportedBandwidth__len_helper1 SupportedBandwidth__len_helper2  SupportedBandwidth__Format_list.
Definition SupportedBandwidth__F1 (z : SupportedBandwidth__Type) : (choice SupportedBandwidth__list) :=
  match z with
   | SupportedBandwidth__fr1 t => existT _ 0 t
  | SupportedBandwidth__fr2 t => existT _ 1 t
  end.
Definition SupportedBandwidth__g := (fun n => typ_set (get_nth_typ SupportedBandwidth__list n)).
Definition SupportedBandwidth__F2 (y : choice SupportedBandwidth__list) : SupportedBandwidth__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SupportedBandwidth__g n -> SupportedBandwidth__Type) with
    | 0 => fun (t : SupportedBandwidth__fr1__Type) => SupportedBandwidth__fr1 t 
    | 1 => fun (t : SupportedBandwidth__fr2__Type) => SupportedBandwidth__fr2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SupportedBandwidth__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SupportedBandwidth__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SupportedBandwidth__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SupportedBandwidth__Type with end) n0
           end t0).

Lemma SupportedBandwidth__helper2 :  forall (y : SupportedBandwidth__Type), SupportedBandwidth__cond y -> choice_cond SupportedBandwidth__list (SupportedBandwidth__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SupportedBandwidth__helper3 :  forall (y : SupportedBandwidth__Type), SupportedBandwidth__F2 (SupportedBandwidth__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SupportedBandwidth__helper4 : (forall b : choice SupportedBandwidth__list, choice_cond SupportedBandwidth__list b -> SupportedBandwidth__cond (SupportedBandwidth__F2 b) /\ SupportedBandwidth__F1 (SupportedBandwidth__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SupportedBandwidth__F1 SupportedBandwidth__F2.
Definition SupportedBandwidth__Format : T_Format SupportedBandwidth__Type SupportedBandwidth__cond :=
  (* Eval compute in *) proj2_format SupportedBandwidth__cond SupportedBandwidth__list__Format SupportedBandwidth__F1 SupportedBandwidth__F2 SupportedBandwidth__helper2 SupportedBandwidth__helper3 SupportedBandwidth__helper4.
Opaque SupportedBandwidth__cond SupportedBandwidth__Format.

