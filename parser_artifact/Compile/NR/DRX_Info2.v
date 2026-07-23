Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Lemma DRX_Info2__drx_onDurationTimer__subMilliSeconds__helper1 : (1 <= 31)%Z.  lia. Qed.
Lemma DRX_Info2__drx_onDurationTimer__subMilliSeconds__helper2 : to_bit_sz (Z.to_nat (31 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info2__drx_onDurationTimer__subMilliSeconds__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info2__drx_onDurationTimer__subMilliSeconds__Type := Z.
Definition DRX_Info2__drx_onDurationTimer__subMilliSeconds__cond := (fun z => (1 <= z <= 31)%Z).
Inductive DRX_Info2__drx_onDurationTimer__milliSeconds__Type : Set :=
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms2
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms3
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms4
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms5
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms6
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms8
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms10
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms20
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms30
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms40
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms50
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms60
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms80
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms100
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms200
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms300
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms400
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms500
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms600
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms800
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1000
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1200
 | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1600
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare8
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare7
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare6
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare5
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare4
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare3
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare2
 | DRX_Info2__drx_onDurationTimer__milliSeconds__spare1
.
Definition DRX_Info2__drx_onDurationTimer__milliSeconds__cond := (fun (_ : DRX_Info2__drx_onDurationTimer__milliSeconds__Type) => True).
Lemma DRX_Info2__drx_onDurationTimer__milliSeconds__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_Info2__drx_onDurationTimer__milliSeconds__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_Info2__drx_onDurationTimer__milliSeconds__nat__helper.

Definition DRX_Info2__drx_onDurationTimer__milliSeconds__F1 t :=
  match t with
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1 => 0
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms2 => 1
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms3 => 2
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms4 => 3
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms5 => 4
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms6 => 5
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms8 => 6
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms10 => 7
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms20 => 8
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms30 => 9
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms40 => 10
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms50 => 11
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms60 => 12
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms80 => 13
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms100 => 14
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms200 => 15
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms300 => 16
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms400 => 17
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms500 => 18
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms600 => 19
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms800 => 20
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1000 => 21
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1200 => 22
  | DRX_Info2__drx_onDurationTimer__milliSeconds__ms1600 => 23
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare8 => 24
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare7 => 25
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare6 => 26
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare5 => 27
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare4 => 28
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare3 => 29
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare2 => 30
  | DRX_Info2__drx_onDurationTimer__milliSeconds__spare1 => 31
  end.
Definition DRX_Info2__drx_onDurationTimer__milliSeconds__F2 n :=
  match n with
  | 0 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms1
  | 1 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms2
  | 2 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms3
  | 3 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms4
  | 4 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms5
  | 5 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms6
  | 6 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms8
  | 7 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms10
  | 8 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms20
  | 9 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms30
  | 10 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms40
  | 11 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms50
  | 12 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms60
  | 13 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms80
  | 14 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms100
  | 15 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms200
  | 16 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms300
  | 17 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms400
  | 18 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms500
  | 19 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms600
  | 20 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms800
  | 21 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms1000
  | 22 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms1200
  | 23 => DRX_Info2__drx_onDurationTimer__milliSeconds__ms1600
  | 24 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare8
  | 25 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare7
  | 26 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare6
  | 27 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare5
  | 28 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare4
  | 29 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare3
  | 30 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare2
  | 31 => DRX_Info2__drx_onDurationTimer__milliSeconds__spare1
  | _ => DRX_Info2__drx_onDurationTimer__milliSeconds__ms1
  end.
Lemma DRX_Info2__drx_onDurationTimer__milliSeconds__F1F2 : forall x : DRX_Info2__drx_onDurationTimer__milliSeconds__Type, (DRX_Info2__drx_onDurationTimer__milliSeconds__F1 x <= 31) /\ DRX_Info2__drx_onDurationTimer__milliSeconds__F2 (DRX_Info2__drx_onDurationTimer__milliSeconds__F1 x) = x. imp_solve. Qed.
Lemma DRX_Info2__drx_onDurationTimer__milliSeconds__F2F1 : forall (y : nat) (H : y <= 31), DRX_Info2__drx_onDurationTimer__milliSeconds__F1 (DRX_Info2__drx_onDurationTimer__milliSeconds__F2 y) = y. enum_solve H y. Qed.


Inductive DRX_Info2__drx_onDurationTimer__Type : Set :=
  | DRX_Info2__drx_onDurationTimer__subMilliSeconds : Z -> DRX_Info2__drx_onDurationTimer__Type
  | DRX_Info2__drx_onDurationTimer__milliSeconds : DRX_Info2__drx_onDurationTimer__milliSeconds__Type -> DRX_Info2__drx_onDurationTimer__Type
.
Definition DRX_Info2__drx_onDurationTimer__list : list typ := (
typ_cons Z DRX_Info2__drx_onDurationTimer__subMilliSeconds__cond ::
typ_cons DRX_Info2__drx_onDurationTimer__milliSeconds__Type DRX_Info2__drx_onDurationTimer__milliSeconds__cond ::
 nil).
Definition DRX_Info2__drx_onDurationTimer__cond (c : DRX_Info2__drx_onDurationTimer__Type) := 
  match c with
  | DRX_Info2__drx_onDurationTimer__subMilliSeconds t => DRX_Info2__drx_onDurationTimer__subMilliSeconds__cond t 
  | DRX_Info2__drx_onDurationTimer__milliSeconds t => DRX_Info2__drx_onDurationTimer__milliSeconds__cond t 
  end.

Lemma DRX_Info2__drx_onDurationTimer__len_helper1 : to_bit_sz (length DRX_Info2__drx_onDurationTimer__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DRX_Info2__drx_onDurationTimer__len_helper2 : 2 <= length2 DRX_Info2__drx_onDurationTimer__list.
 simpl. lia. Qed.
Record DRX_Info2__Type : Set :=
  make__DRX_Info2__Type {
    DRX_Info2__drx_onDurationTimer : DRX_Info2__drx_onDurationTimer__Type ;
}.
Definition DRX_Info2__list := (
 Nor DRX_Info2__drx_onDurationTimer__Type DRX_Info2__drx_onDurationTimer__cond ::
 nil).
Definition DRX_Info2__cond z := 
  DRX_Info2__drx_onDurationTimer__cond (DRX_Info2__drx_onDurationTimer z) /\
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
Definition DRX_Info2__drx_onDurationTimer__subMilliSeconds__Format : T_Format Z DRX_Info2__drx_onDurationTimer__subMilliSeconds__cond :=
 ranged_int_format (1) (31) DRX_Info2__drx_onDurationTimer__subMilliSeconds__helper1 DRX_Info2__drx_onDurationTimer__subMilliSeconds__helper2.

Opaque DRX_Info2__drx_onDurationTimer__subMilliSeconds__cond DRX_Info2__drx_onDurationTimer__subMilliSeconds__Format.

Definition DRX_Info2__drx_onDurationTimer__milliSeconds__Format : T_Format DRX_Info2__drx_onDurationTimer__milliSeconds__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_Info2__drx_onDurationTimer__milliSeconds__nat__Format DRX_Info2__drx_onDurationTimer__milliSeconds__F1 DRX_Info2__drx_onDurationTimer__milliSeconds__F2 DRX_Info2__drx_onDurationTimer__milliSeconds__F1F2 DRX_Info2__drx_onDurationTimer__milliSeconds__F2F1.

Opaque DRX_Info2__drx_onDurationTimer__milliSeconds__cond DRX_Info2__drx_onDurationTimer__milliSeconds__Format.


Definition DRX_Info2__drx_onDurationTimer__Format_Type := Eval cbn in get_formats DRX_Info2__drx_onDurationTimer__list.
Definition DRX_Info2__drx_onDurationTimer__Format_list : DRX_Info2__drx_onDurationTimer__Format_Type :=
  (DRX_Info2__drx_onDurationTimer__subMilliSeconds__Format, (DRX_Info2__drx_onDurationTimer__milliSeconds__Format, unit__Format)).
Definition DRX_Info2__drx_onDurationTimer__list__Format := Eval compute in choice_format DRX_Info2__drx_onDurationTimer__list DRX_Info2__drx_onDurationTimer__len_helper1 DRX_Info2__drx_onDurationTimer__len_helper2  DRX_Info2__drx_onDurationTimer__Format_list.
Definition DRX_Info2__drx_onDurationTimer__F1 (z : DRX_Info2__drx_onDurationTimer__Type) : (choice DRX_Info2__drx_onDurationTimer__list) :=
  match z with
   | DRX_Info2__drx_onDurationTimer__subMilliSeconds t => existT _ 0 t
  | DRX_Info2__drx_onDurationTimer__milliSeconds t => existT _ 1 t
  end.
Definition DRX_Info2__drx_onDurationTimer__g := (fun n => typ_set (get_nth_typ DRX_Info2__drx_onDurationTimer__list n)).
Definition DRX_Info2__drx_onDurationTimer__F2 (y : choice DRX_Info2__drx_onDurationTimer__list) : DRX_Info2__drx_onDurationTimer__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DRX_Info2__drx_onDurationTimer__g n -> DRX_Info2__drx_onDurationTimer__Type) with
    | 0 => fun (t : Z) => DRX_Info2__drx_onDurationTimer__subMilliSeconds t 
    | 1 => fun (t : DRX_Info2__drx_onDurationTimer__milliSeconds__Type) => DRX_Info2__drx_onDurationTimer__milliSeconds t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DRX_Info2__drx_onDurationTimer__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DRX_Info2__drx_onDurationTimer__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DRX_Info2__drx_onDurationTimer__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DRX_Info2__drx_onDurationTimer__Type with end) n0
           end t0).

Lemma DRX_Info2__drx_onDurationTimer__helper2 :  forall (y : DRX_Info2__drx_onDurationTimer__Type), DRX_Info2__drx_onDurationTimer__cond y -> choice_cond DRX_Info2__drx_onDurationTimer__list (DRX_Info2__drx_onDurationTimer__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DRX_Info2__drx_onDurationTimer__helper3 :  forall (y : DRX_Info2__drx_onDurationTimer__Type), DRX_Info2__drx_onDurationTimer__F2 (DRX_Info2__drx_onDurationTimer__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DRX_Info2__drx_onDurationTimer__helper4 : (forall b : choice DRX_Info2__drx_onDurationTimer__list, choice_cond DRX_Info2__drx_onDurationTimer__list b -> DRX_Info2__drx_onDurationTimer__cond (DRX_Info2__drx_onDurationTimer__F2 b) /\ DRX_Info2__drx_onDurationTimer__F1 (DRX_Info2__drx_onDurationTimer__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DRX_Info2__drx_onDurationTimer__F1 DRX_Info2__drx_onDurationTimer__F2.
Definition DRX_Info2__drx_onDurationTimer__Format : T_Format DRX_Info2__drx_onDurationTimer__Type DRX_Info2__drx_onDurationTimer__cond :=
  (* Eval compute in *) proj2_format DRX_Info2__drx_onDurationTimer__cond DRX_Info2__drx_onDurationTimer__list__Format DRX_Info2__drx_onDurationTimer__F1 DRX_Info2__drx_onDurationTimer__F2 DRX_Info2__drx_onDurationTimer__helper2 DRX_Info2__drx_onDurationTimer__helper3 DRX_Info2__drx_onDurationTimer__helper4.
Opaque DRX_Info2__drx_onDurationTimer__cond DRX_Info2__drx_onDurationTimer__Format.


Definition DRX_Info2__Format_Type := Eval cbn in seq_format_prod DRX_Info2__list.
Definition DRX_Info2__Format_list : DRX_Info2__Format_Type :=
  (DRX_Info2__drx_onDurationTimer__Format, unit_format).
Definition DRX_Info2__list__Format := (*Eval compute in *) seq_format DRX_Info2__list DRX_Info2__Format_list.
Definition DRX_Info2__F1 z :=
  (DRX_Info2__drx_onDurationTimer z, tt).
Definition DRX_Info2__F2 (y : seq_type DRX_Info2__list) :=
  match y with
  | (i0, _)=>
    make__DRX_Info2__Type i0
  end.
Lemma DRX_Info2__F1F2_cond (z : DRX_Info2__Type)
  : DRX_Info2__cond z ->
  (seq_cond DRX_Info2__list (DRX_Info2__F1 z)).
intro H. unfold DRX_Info2__cond in H. simpl. auto. Qed.
Lemma DRX_Info2__F1F2_cond2 (z : DRX_Info2__Type)
 : DRX_Info2__F2 (DRX_Info2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_Info2__F2F1_cond (y : seq_type DRX_Info2__list)
  : seq_cond DRX_Info2__list y ->
 (DRX_Info2__cond (DRX_Info2__F2 y)) /\  DRX_Info2__F1 (DRX_Info2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_Info2__cond. simpl in *. auto.
 - simpl. unfold DRX_Info2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_Info2__Format : T_Format DRX_Info2__Type DRX_Info2__cond :=
        proj2_format  DRX_Info2__cond DRX_Info2__list__Format
    DRX_Info2__F1 DRX_Info2__F2 DRX_Info2__F1F2_cond  DRX_Info2__F1F2_cond2 DRX_Info2__F2F1_cond.
Opaque DRX_Info2__cond DRX_Info2__Format.

