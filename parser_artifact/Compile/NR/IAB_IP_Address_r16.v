Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition IAB_IP_Address_r16__root__iPv4_Address_r16__Type := bit_string_fixed.
Definition IAB_IP_Address_r16__root__iPv4_Address_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 32 /\ bit_string_len_prop (fst z) (snd z)).
Definition IAB_IP_Address_r16__root__iPv6_Address_r16__Type := bit_string_fixed.
Definition IAB_IP_Address_r16__root__iPv6_Address_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 128 /\ bit_string_len_prop (fst z) (snd z)).
Definition IAB_IP_Address_r16__root__iPv6_Prefix_r16__Type := bit_string_fixed.
Definition IAB_IP_Address_r16__root__iPv6_Prefix_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 64 /\ bit_string_len_prop (fst z) (snd z)).

Inductive IAB_IP_Address_r16__root__Type : Set :=
  | IAB_IP_Address_r16__root__iPv4_Address_r16 : IAB_IP_Address_r16__root__iPv4_Address_r16__Type -> IAB_IP_Address_r16__root__Type
  | IAB_IP_Address_r16__root__iPv6_Address_r16 : IAB_IP_Address_r16__root__iPv6_Address_r16__Type -> IAB_IP_Address_r16__root__Type
  | IAB_IP_Address_r16__root__iPv6_Prefix_r16 : IAB_IP_Address_r16__root__iPv6_Prefix_r16__Type -> IAB_IP_Address_r16__root__Type
.
Definition IAB_IP_Address_r16__root__list : list typ := (
typ_cons IAB_IP_Address_r16__root__iPv4_Address_r16__Type IAB_IP_Address_r16__root__iPv4_Address_r16__cond ::
typ_cons IAB_IP_Address_r16__root__iPv6_Address_r16__Type IAB_IP_Address_r16__root__iPv6_Address_r16__cond ::
typ_cons IAB_IP_Address_r16__root__iPv6_Prefix_r16__Type IAB_IP_Address_r16__root__iPv6_Prefix_r16__cond ::
 nil).
Definition IAB_IP_Address_r16__root__cond (c : IAB_IP_Address_r16__root__Type) := 
  match c with
  | IAB_IP_Address_r16__root__iPv4_Address_r16 t => IAB_IP_Address_r16__root__iPv4_Address_r16__cond t 
  | IAB_IP_Address_r16__root__iPv6_Address_r16 t => IAB_IP_Address_r16__root__iPv6_Address_r16__cond t 
  | IAB_IP_Address_r16__root__iPv6_Prefix_r16 t => IAB_IP_Address_r16__root__iPv6_Prefix_r16__cond t 
  end.

Lemma IAB_IP_Address_r16__root__len_helper1 : to_bit_sz (length IAB_IP_Address_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma IAB_IP_Address_r16__root__len_helper2 : 2 <= length2 IAB_IP_Address_r16__root__list.
 simpl. lia. Qed.

Definition IAB_IP_Address_r16__ext__Type : Set := Empty_set.
Definition IAB_IP_Address_r16__ext__cond (c : IAB_IP_Address_r16__ext__Type) := True.
Definition IAB_IP_Address_r16__Type : Set := IAB_IP_Address_r16__root__Type + IAB_IP_Address_r16__ext__Type.
Definition IAB_IP_Address_r16__cond :=
  sum_cond IAB_IP_Address_r16__root__cond IAB_IP_Address_r16__ext__cond.

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
Definition IAB_IP_Address_r16__root__iPv4_Address_r16__Format : T_Format IAB_IP_Address_r16__root__iPv4_Address_r16__Type IAB_IP_Address_r16__root__iPv4_Address_r16__cond := (* Eval compute in *) bit_string_fixed_format 32.
Opaque IAB_IP_Address_r16__root__iPv4_Address_r16__cond IAB_IP_Address_r16__root__iPv4_Address_r16__Format.

Definition IAB_IP_Address_r16__root__iPv6_Address_r16__Format : T_Format IAB_IP_Address_r16__root__iPv6_Address_r16__Type IAB_IP_Address_r16__root__iPv6_Address_r16__cond := (* Eval compute in *) bit_string_fixed_format 128.
Opaque IAB_IP_Address_r16__root__iPv6_Address_r16__cond IAB_IP_Address_r16__root__iPv6_Address_r16__Format.

Definition IAB_IP_Address_r16__root__iPv6_Prefix_r16__Format : T_Format IAB_IP_Address_r16__root__iPv6_Prefix_r16__Type IAB_IP_Address_r16__root__iPv6_Prefix_r16__cond := (* Eval compute in *) bit_string_fixed_format 64.
Opaque IAB_IP_Address_r16__root__iPv6_Prefix_r16__cond IAB_IP_Address_r16__root__iPv6_Prefix_r16__Format.


Definition IAB_IP_Address_r16__root__Format_Type := Eval cbn in get_formats IAB_IP_Address_r16__root__list.
Definition IAB_IP_Address_r16__root__Format_list : IAB_IP_Address_r16__root__Format_Type :=
  (IAB_IP_Address_r16__root__iPv4_Address_r16__Format, (IAB_IP_Address_r16__root__iPv6_Address_r16__Format, (IAB_IP_Address_r16__root__iPv6_Prefix_r16__Format, unit__Format))).
Definition IAB_IP_Address_r16__root__list__Format := Eval compute in choice_format IAB_IP_Address_r16__root__list IAB_IP_Address_r16__root__len_helper1 IAB_IP_Address_r16__root__len_helper2  IAB_IP_Address_r16__root__Format_list.
Definition IAB_IP_Address_r16__root__F1 (z : IAB_IP_Address_r16__root__Type) : (choice IAB_IP_Address_r16__root__list) :=
  match z with
   | IAB_IP_Address_r16__root__iPv4_Address_r16 t => existT _ 0 t
  | IAB_IP_Address_r16__root__iPv6_Address_r16 t => existT _ 1 t
  | IAB_IP_Address_r16__root__iPv6_Prefix_r16 t => existT _ 2 t
  end.
Definition IAB_IP_Address_r16__root__g := (fun n => typ_set (get_nth_typ IAB_IP_Address_r16__root__list n)).
Definition IAB_IP_Address_r16__root__F2 (y : choice IAB_IP_Address_r16__root__list) : IAB_IP_Address_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (IAB_IP_Address_r16__root__g n -> IAB_IP_Address_r16__root__Type) with
    | 0 => fun (t : IAB_IP_Address_r16__root__iPv4_Address_r16__Type) => IAB_IP_Address_r16__root__iPv4_Address_r16 t 
    | 1 => fun (t : IAB_IP_Address_r16__root__iPv6_Address_r16__Type) => IAB_IP_Address_r16__root__iPv6_Address_r16 t 
    | 2 => fun (t : IAB_IP_Address_r16__root__iPv6_Prefix_r16__Type) => IAB_IP_Address_r16__root__iPv6_Prefix_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : IAB_IP_Address_r16__root__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ IAB_IP_Address_r16__root__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len IAB_IP_Address_r16__root__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return IAB_IP_Address_r16__root__Type with end) n0
           end t0).

Lemma IAB_IP_Address_r16__root__helper2 :  forall (y : IAB_IP_Address_r16__root__Type), IAB_IP_Address_r16__root__cond y -> choice_cond IAB_IP_Address_r16__root__list (IAB_IP_Address_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma IAB_IP_Address_r16__root__helper3 :  forall (y : IAB_IP_Address_r16__root__Type), IAB_IP_Address_r16__root__F2 (IAB_IP_Address_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma IAB_IP_Address_r16__root__helper4 : (forall b : choice IAB_IP_Address_r16__root__list, choice_cond IAB_IP_Address_r16__root__list b -> IAB_IP_Address_r16__root__cond (IAB_IP_Address_r16__root__F2 b) /\ IAB_IP_Address_r16__root__F1 (IAB_IP_Address_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length IAB_IP_Address_r16__root__F1 IAB_IP_Address_r16__root__F2.
Definition IAB_IP_Address_r16__root__Format : T_Format IAB_IP_Address_r16__root__Type IAB_IP_Address_r16__root__cond :=
  (* Eval compute in *) proj2_format IAB_IP_Address_r16__root__cond IAB_IP_Address_r16__root__list__Format IAB_IP_Address_r16__root__F1 IAB_IP_Address_r16__root__F2 IAB_IP_Address_r16__root__helper2 IAB_IP_Address_r16__root__helper3 IAB_IP_Address_r16__root__helper4.
Opaque IAB_IP_Address_r16__root__cond IAB_IP_Address_r16__root__Format.

Definition IAB_IP_Address_r16__ext__Format : T_Format IAB_IP_Address_r16__ext__Type IAB_IP_Address_r16__ext__cond := empty_format.
Opaque IAB_IP_Address_r16__ext__cond IAB_IP_Address_r16__ext__Format.

Definition IAB_IP_Address_r16__Format : T_Format IAB_IP_Address_r16__Type IAB_IP_Address_r16__cond := sum_format IAB_IP_Address_r16__root__Format IAB_IP_Address_r16__ext__Format.
Opaque IAB_IP_Address_r16__cond IAB_IP_Address_r16__Format.

