Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BetaOffsets.

Opaque BetaOffsets__cond BetaOffsets__Format.

Definition UCI_OnPUSCH__betaOffsets__dynamic__Type := list BetaOffsets__Type.

Definition UCI_OnPUSCH__betaOffsets__dynamic__cond (z : UCI_OnPUSCH__betaOffsets__dynamic__Type) := (list_and BetaOffsets__cond z) /\ (length z = Z.to_nat 4).

Require Import NR.BetaOffsets.

Opaque BetaOffsets__cond BetaOffsets__Format.


Inductive UCI_OnPUSCH__betaOffsets__Type : Set :=
  | UCI_OnPUSCH__betaOffsets__dynamic : UCI_OnPUSCH__betaOffsets__dynamic__Type -> UCI_OnPUSCH__betaOffsets__Type
  | UCI_OnPUSCH__betaOffsets__semiStatic : BetaOffsets__Type -> UCI_OnPUSCH__betaOffsets__Type
.
Definition UCI_OnPUSCH__betaOffsets__list : list typ := (
typ_cons UCI_OnPUSCH__betaOffsets__dynamic__Type UCI_OnPUSCH__betaOffsets__dynamic__cond ::
typ_cons BetaOffsets__Type BetaOffsets__cond ::
 nil).
Definition UCI_OnPUSCH__betaOffsets__cond (c : UCI_OnPUSCH__betaOffsets__Type) := 
  match c with
  | UCI_OnPUSCH__betaOffsets__dynamic t => UCI_OnPUSCH__betaOffsets__dynamic__cond t 
  | UCI_OnPUSCH__betaOffsets__semiStatic t => BetaOffsets__cond t 
  end.

Lemma UCI_OnPUSCH__betaOffsets__len_helper1 : to_bit_sz (length UCI_OnPUSCH__betaOffsets__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UCI_OnPUSCH__betaOffsets__len_helper2 : 2 <= length2 UCI_OnPUSCH__betaOffsets__list.
 simpl. lia. Qed.
Inductive UCI_OnPUSCH__scaling__Type : Set :=
 | UCI_OnPUSCH__scaling__f0p5
 | UCI_OnPUSCH__scaling__f0p65
 | UCI_OnPUSCH__scaling__f0p8
 | UCI_OnPUSCH__scaling__f1
.
Definition UCI_OnPUSCH__scaling__cond := (fun (_ : UCI_OnPUSCH__scaling__Type) => True).
Lemma UCI_OnPUSCH__scaling__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UCI_OnPUSCH__scaling__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 UCI_OnPUSCH__scaling__nat__helper.

Definition UCI_OnPUSCH__scaling__F1 t :=
  match t with
  | UCI_OnPUSCH__scaling__f0p5 => 0
  | UCI_OnPUSCH__scaling__f0p65 => 1
  | UCI_OnPUSCH__scaling__f0p8 => 2
  | UCI_OnPUSCH__scaling__f1 => 3
  end.
Definition UCI_OnPUSCH__scaling__F2 n :=
  match n with
  | 0 => UCI_OnPUSCH__scaling__f0p5
  | 1 => UCI_OnPUSCH__scaling__f0p65
  | 2 => UCI_OnPUSCH__scaling__f0p8
  | 3 => UCI_OnPUSCH__scaling__f1
  | _ => UCI_OnPUSCH__scaling__f0p5
  end.
Lemma UCI_OnPUSCH__scaling__F1F2 : forall x : UCI_OnPUSCH__scaling__Type, (UCI_OnPUSCH__scaling__F1 x <= 3) /\ UCI_OnPUSCH__scaling__F2 (UCI_OnPUSCH__scaling__F1 x) = x. imp_solve. Qed.
Lemma UCI_OnPUSCH__scaling__F2F1 : forall (y : nat) (H : y <= 3), UCI_OnPUSCH__scaling__F1 (UCI_OnPUSCH__scaling__F2 y) = y. enum_solve H y. Qed.

Record UCI_OnPUSCH__Type : Set :=
  make__UCI_OnPUSCH__Type {
    UCI_OnPUSCH__betaOffsets : option UCI_OnPUSCH__betaOffsets__Type ;
    UCI_OnPUSCH__scaling : UCI_OnPUSCH__scaling__Type ;
}.
Definition UCI_OnPUSCH__list := (
 Opt UCI_OnPUSCH__betaOffsets__Type UCI_OnPUSCH__betaOffsets__cond ::
 Nor UCI_OnPUSCH__scaling__Type UCI_OnPUSCH__scaling__cond ::
 nil).
Definition UCI_OnPUSCH__cond z := 
  opt_cond UCI_OnPUSCH__betaOffsets__cond (UCI_OnPUSCH__betaOffsets z) /\
  UCI_OnPUSCH__scaling__cond (UCI_OnPUSCH__scaling z) /\
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
Definition UCI_OnPUSCH__betaOffsets__dynamic__Format : T_Format UCI_OnPUSCH__betaOffsets__dynamic__Type UCI_OnPUSCH__betaOffsets__dynamic__cond := seq_of_fixed_format BetaOffsets__Format 4.

Opaque UCI_OnPUSCH__betaOffsets__dynamic__cond UCI_OnPUSCH__betaOffsets__dynamic__Format.


Definition UCI_OnPUSCH__betaOffsets__Format_Type := Eval cbn in get_formats UCI_OnPUSCH__betaOffsets__list.
Definition UCI_OnPUSCH__betaOffsets__Format_list : UCI_OnPUSCH__betaOffsets__Format_Type :=
  (UCI_OnPUSCH__betaOffsets__dynamic__Format, (BetaOffsets__Format, unit__Format)).
Definition UCI_OnPUSCH__betaOffsets__list__Format := Eval compute in choice_format UCI_OnPUSCH__betaOffsets__list UCI_OnPUSCH__betaOffsets__len_helper1 UCI_OnPUSCH__betaOffsets__len_helper2  UCI_OnPUSCH__betaOffsets__Format_list.
Definition UCI_OnPUSCH__betaOffsets__F1 (z : UCI_OnPUSCH__betaOffsets__Type) : (choice UCI_OnPUSCH__betaOffsets__list) :=
  match z with
   | UCI_OnPUSCH__betaOffsets__dynamic t => existT _ 0 t
  | UCI_OnPUSCH__betaOffsets__semiStatic t => existT _ 1 t
  end.
Definition UCI_OnPUSCH__betaOffsets__g := (fun n => typ_set (get_nth_typ UCI_OnPUSCH__betaOffsets__list n)).
Definition UCI_OnPUSCH__betaOffsets__F2 (y : choice UCI_OnPUSCH__betaOffsets__list) : UCI_OnPUSCH__betaOffsets__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UCI_OnPUSCH__betaOffsets__g n -> UCI_OnPUSCH__betaOffsets__Type) with
    | 0 => fun (t : UCI_OnPUSCH__betaOffsets__dynamic__Type) => UCI_OnPUSCH__betaOffsets__dynamic t 
    | 1 => fun (t : BetaOffsets__Type) => UCI_OnPUSCH__betaOffsets__semiStatic t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UCI_OnPUSCH__betaOffsets__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UCI_OnPUSCH__betaOffsets__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UCI_OnPUSCH__betaOffsets__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UCI_OnPUSCH__betaOffsets__Type with end) n0
           end t0).

Lemma UCI_OnPUSCH__betaOffsets__helper2 :  forall (y : UCI_OnPUSCH__betaOffsets__Type), UCI_OnPUSCH__betaOffsets__cond y -> choice_cond UCI_OnPUSCH__betaOffsets__list (UCI_OnPUSCH__betaOffsets__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UCI_OnPUSCH__betaOffsets__helper3 :  forall (y : UCI_OnPUSCH__betaOffsets__Type), UCI_OnPUSCH__betaOffsets__F2 (UCI_OnPUSCH__betaOffsets__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UCI_OnPUSCH__betaOffsets__helper4 : (forall b : choice UCI_OnPUSCH__betaOffsets__list, choice_cond UCI_OnPUSCH__betaOffsets__list b -> UCI_OnPUSCH__betaOffsets__cond (UCI_OnPUSCH__betaOffsets__F2 b) /\ UCI_OnPUSCH__betaOffsets__F1 (UCI_OnPUSCH__betaOffsets__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UCI_OnPUSCH__betaOffsets__F1 UCI_OnPUSCH__betaOffsets__F2.
Definition UCI_OnPUSCH__betaOffsets__Format : T_Format UCI_OnPUSCH__betaOffsets__Type UCI_OnPUSCH__betaOffsets__cond :=
  (* Eval compute in *) proj2_format UCI_OnPUSCH__betaOffsets__cond UCI_OnPUSCH__betaOffsets__list__Format UCI_OnPUSCH__betaOffsets__F1 UCI_OnPUSCH__betaOffsets__F2 UCI_OnPUSCH__betaOffsets__helper2 UCI_OnPUSCH__betaOffsets__helper3 UCI_OnPUSCH__betaOffsets__helper4.
Opaque UCI_OnPUSCH__betaOffsets__cond UCI_OnPUSCH__betaOffsets__Format.

Definition UCI_OnPUSCH__scaling__Format : T_Format UCI_OnPUSCH__scaling__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UCI_OnPUSCH__scaling__nat__Format UCI_OnPUSCH__scaling__F1 UCI_OnPUSCH__scaling__F2 UCI_OnPUSCH__scaling__F1F2 UCI_OnPUSCH__scaling__F2F1.

Opaque UCI_OnPUSCH__scaling__cond UCI_OnPUSCH__scaling__Format.


Definition UCI_OnPUSCH__Format_Type := Eval cbn in seq_format_prod UCI_OnPUSCH__list.
Definition UCI_OnPUSCH__Format_list : UCI_OnPUSCH__Format_Type :=
  (UCI_OnPUSCH__betaOffsets__Format, (UCI_OnPUSCH__scaling__Format, unit_format)).
Definition UCI_OnPUSCH__list__Format := (*Eval compute in *) seq_format UCI_OnPUSCH__list UCI_OnPUSCH__Format_list.
Definition UCI_OnPUSCH__F1 z :=
  (UCI_OnPUSCH__betaOffsets z, (UCI_OnPUSCH__scaling z, tt)).
Definition UCI_OnPUSCH__F2 (y : seq_type UCI_OnPUSCH__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UCI_OnPUSCH__Type i0 i1
  end.
Lemma UCI_OnPUSCH__F1F2_cond (z : UCI_OnPUSCH__Type)
  : UCI_OnPUSCH__cond z ->
  (seq_cond UCI_OnPUSCH__list (UCI_OnPUSCH__F1 z)).
intro H. unfold UCI_OnPUSCH__cond in H. simpl. auto. Qed.
Lemma UCI_OnPUSCH__F1F2_cond2 (z : UCI_OnPUSCH__Type)
 : UCI_OnPUSCH__F2 (UCI_OnPUSCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UCI_OnPUSCH__F2F1_cond (y : seq_type UCI_OnPUSCH__list)
  : seq_cond UCI_OnPUSCH__list y ->
 (UCI_OnPUSCH__cond (UCI_OnPUSCH__F2 y)) /\  UCI_OnPUSCH__F1 (UCI_OnPUSCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UCI_OnPUSCH__cond. simpl in *. auto.
 - simpl. unfold UCI_OnPUSCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UCI_OnPUSCH__Format : T_Format UCI_OnPUSCH__Type UCI_OnPUSCH__cond :=
        proj2_format  UCI_OnPUSCH__cond UCI_OnPUSCH__list__Format
    UCI_OnPUSCH__F1 UCI_OnPUSCH__F2 UCI_OnPUSCH__F1F2_cond  UCI_OnPUSCH__F1F2_cond2 UCI_OnPUSCH__F2F1_cond.
Opaque UCI_OnPUSCH__cond UCI_OnPUSCH__Format.

