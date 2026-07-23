Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Section SetupRelease__sec.
Variable ElementTypeParam__Type : Set.
Variable ElementTypeParam__cond : ElementTypeParam__Type -> Prop.
Variable ElementTypeParam__Format : T_Format ElementTypeParam__Type ElementTypeParam__cond.

Inductive SetupRelease__Type : Set :=
  | SetupRelease__release : unit -> SetupRelease__Type
  | SetupRelease__setup : ElementTypeParam__Type -> SetupRelease__Type
.
Definition SetupRelease__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons ElementTypeParam__Type ElementTypeParam__cond ::
 nil).
Definition SetupRelease__cond (c : SetupRelease__Type) := 
  match c with
  | SetupRelease__release t => (fun _ => True) t 
  | SetupRelease__setup t => ElementTypeParam__cond t 
  end.

Lemma SetupRelease__len_helper1 : to_bit_sz (length SetupRelease__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SetupRelease__len_helper2 : 2 <= length2 SetupRelease__list.
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

Definition SetupRelease__Format_Type := Eval cbn in get_formats SetupRelease__list.
Definition SetupRelease__Format_list : SetupRelease__Format_Type :=
  (unit__Format, (ElementTypeParam__Format, unit__Format)).
Definition SetupRelease__list__Format := Eval compute in choice_format SetupRelease__list SetupRelease__len_helper1 SetupRelease__len_helper2  SetupRelease__Format_list.
Definition SetupRelease__F1 (z : SetupRelease__Type) : (choice SetupRelease__list) :=
  match z with
   | SetupRelease__release t => existT _ 0 t
  | SetupRelease__setup t => existT _ 1 t
  end.
Definition SetupRelease__g := (fun n => typ_set (get_nth_typ SetupRelease__list n)).
Definition SetupRelease__F2 (y : choice SetupRelease__list) : SetupRelease__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SetupRelease__g n -> SetupRelease__Type) with
    | 0 => fun (t : unit) => SetupRelease__release t 
    | 1 => fun (t : ElementTypeParam__Type) => SetupRelease__setup t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SetupRelease__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SetupRelease__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SetupRelease__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SetupRelease__Type with end) n0
           end t0).

Lemma SetupRelease__helper2 :  forall (y : SetupRelease__Type), SetupRelease__cond y -> choice_cond SetupRelease__list (SetupRelease__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SetupRelease__helper3 :  forall (y : SetupRelease__Type), SetupRelease__F2 (SetupRelease__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SetupRelease__helper4 : (forall b : choice SetupRelease__list, choice_cond SetupRelease__list b -> SetupRelease__cond (SetupRelease__F2 b) /\ SetupRelease__F1 (SetupRelease__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SetupRelease__F1 SetupRelease__F2.
Definition SetupRelease__Format : T_Format SetupRelease__Type SetupRelease__cond :=
  (* Eval compute in *) proj2_format SetupRelease__cond SetupRelease__list__Format SetupRelease__F1 SetupRelease__F2 SetupRelease__helper2 SetupRelease__helper3 SetupRelease__helper4.
Opaque SetupRelease__cond SetupRelease__Format.

End SetupRelease__sec.
