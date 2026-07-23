Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.

Inductive RRCReconfigurationComplete_v1560_IEs__scg_Response__Type : Set :=
  | RRCReconfigurationComplete_v1560_IEs__scg_Response__nr_SCG_Response : octet_string -> RRCReconfigurationComplete_v1560_IEs__scg_Response__Type
  | RRCReconfigurationComplete_v1560_IEs__scg_Response__eutra_SCG_Response : octet_string -> RRCReconfigurationComplete_v1560_IEs__scg_Response__Type
.
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__list : list typ := (
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__cond (c : RRCReconfigurationComplete_v1560_IEs__scg_Response__Type) := 
  match c with
  | RRCReconfigurationComplete_v1560_IEs__scg_Response__nr_SCG_Response t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  | RRCReconfigurationComplete_v1560_IEs__scg_Response__eutra_SCG_Response t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  end.

Lemma RRCReconfigurationComplete_v1560_IEs__scg_Response__len_helper1 : to_bit_sz (length RRCReconfigurationComplete_v1560_IEs__scg_Response__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReconfigurationComplete_v1560_IEs__scg_Response__len_helper2 : 2 <= length2 RRCReconfigurationComplete_v1560_IEs__scg_Response__list.
 simpl. lia. Qed.
Require Import NR.RRCReconfigurationComplete_v1610_IEs.

Opaque RRCReconfigurationComplete_v1610_IEs__cond RRCReconfigurationComplete_v1610_IEs__Format.

Record RRCReconfigurationComplete_v1560_IEs__Type : Set :=
  make__RRCReconfigurationComplete_v1560_IEs__Type {
    RRCReconfigurationComplete_v1560_IEs__scg_Response : option RRCReconfigurationComplete_v1560_IEs__scg_Response__Type ;
    RRCReconfigurationComplete_v1560_IEs__nonCriticalExtension : option RRCReconfigurationComplete_v1610_IEs__Type ;
}.
Definition RRCReconfigurationComplete_v1560_IEs__list := (
 Opt RRCReconfigurationComplete_v1560_IEs__scg_Response__Type RRCReconfigurationComplete_v1560_IEs__scg_Response__cond ::
 Opt RRCReconfigurationComplete_v1610_IEs__Type RRCReconfigurationComplete_v1610_IEs__cond ::
 nil).
Definition RRCReconfigurationComplete_v1560_IEs__cond z := 
  opt_cond RRCReconfigurationComplete_v1560_IEs__scg_Response__cond (RRCReconfigurationComplete_v1560_IEs__scg_Response z) /\
  opt_cond RRCReconfigurationComplete_v1610_IEs__cond (RRCReconfigurationComplete_v1560_IEs__nonCriticalExtension z) /\
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

Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__Format_Type := Eval cbn in get_formats RRCReconfigurationComplete_v1560_IEs__scg_Response__list.
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__Format_list : RRCReconfigurationComplete_v1560_IEs__scg_Response__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, unit__Format)).
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__list__Format := Eval compute in choice_format RRCReconfigurationComplete_v1560_IEs__scg_Response__list RRCReconfigurationComplete_v1560_IEs__scg_Response__len_helper1 RRCReconfigurationComplete_v1560_IEs__scg_Response__len_helper2  RRCReconfigurationComplete_v1560_IEs__scg_Response__Format_list.
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__F1 (z : RRCReconfigurationComplete_v1560_IEs__scg_Response__Type) : (choice RRCReconfigurationComplete_v1560_IEs__scg_Response__list) :=
  match z with
   | RRCReconfigurationComplete_v1560_IEs__scg_Response__nr_SCG_Response t => existT _ 0 t
  | RRCReconfigurationComplete_v1560_IEs__scg_Response__eutra_SCG_Response t => existT _ 1 t
  end.
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__g := (fun n => typ_set (get_nth_typ RRCReconfigurationComplete_v1560_IEs__scg_Response__list n)).
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__F2 (y : choice RRCReconfigurationComplete_v1560_IEs__scg_Response__list) : RRCReconfigurationComplete_v1560_IEs__scg_Response__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReconfigurationComplete_v1560_IEs__scg_Response__g n -> RRCReconfigurationComplete_v1560_IEs__scg_Response__Type) with
    | 0 => fun (t : octet_string) => RRCReconfigurationComplete_v1560_IEs__scg_Response__nr_SCG_Response t 
    | 1 => fun (t : octet_string) => RRCReconfigurationComplete_v1560_IEs__scg_Response__eutra_SCG_Response t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReconfigurationComplete_v1560_IEs__scg_Response__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReconfigurationComplete_v1560_IEs__scg_Response__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReconfigurationComplete_v1560_IEs__scg_Response__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReconfigurationComplete_v1560_IEs__scg_Response__Type with end) n0
           end t0).

Lemma RRCReconfigurationComplete_v1560_IEs__scg_Response__helper2 :  forall (y : RRCReconfigurationComplete_v1560_IEs__scg_Response__Type), RRCReconfigurationComplete_v1560_IEs__scg_Response__cond y -> choice_cond RRCReconfigurationComplete_v1560_IEs__scg_Response__list (RRCReconfigurationComplete_v1560_IEs__scg_Response__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReconfigurationComplete_v1560_IEs__scg_Response__helper3 :  forall (y : RRCReconfigurationComplete_v1560_IEs__scg_Response__Type), RRCReconfigurationComplete_v1560_IEs__scg_Response__F2 (RRCReconfigurationComplete_v1560_IEs__scg_Response__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReconfigurationComplete_v1560_IEs__scg_Response__helper4 : (forall b : choice RRCReconfigurationComplete_v1560_IEs__scg_Response__list, choice_cond RRCReconfigurationComplete_v1560_IEs__scg_Response__list b -> RRCReconfigurationComplete_v1560_IEs__scg_Response__cond (RRCReconfigurationComplete_v1560_IEs__scg_Response__F2 b) /\ RRCReconfigurationComplete_v1560_IEs__scg_Response__F1 (RRCReconfigurationComplete_v1560_IEs__scg_Response__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReconfigurationComplete_v1560_IEs__scg_Response__F1 RRCReconfigurationComplete_v1560_IEs__scg_Response__F2.
Definition RRCReconfigurationComplete_v1560_IEs__scg_Response__Format : T_Format RRCReconfigurationComplete_v1560_IEs__scg_Response__Type RRCReconfigurationComplete_v1560_IEs__scg_Response__cond :=
  (* Eval compute in *) proj2_format RRCReconfigurationComplete_v1560_IEs__scg_Response__cond RRCReconfigurationComplete_v1560_IEs__scg_Response__list__Format RRCReconfigurationComplete_v1560_IEs__scg_Response__F1 RRCReconfigurationComplete_v1560_IEs__scg_Response__F2 RRCReconfigurationComplete_v1560_IEs__scg_Response__helper2 RRCReconfigurationComplete_v1560_IEs__scg_Response__helper3 RRCReconfigurationComplete_v1560_IEs__scg_Response__helper4.
Opaque RRCReconfigurationComplete_v1560_IEs__scg_Response__cond RRCReconfigurationComplete_v1560_IEs__scg_Response__Format.


Definition RRCReconfigurationComplete_v1560_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationComplete_v1560_IEs__list.
Definition RRCReconfigurationComplete_v1560_IEs__Format_list : RRCReconfigurationComplete_v1560_IEs__Format_Type :=
  (RRCReconfigurationComplete_v1560_IEs__scg_Response__Format, (RRCReconfigurationComplete_v1610_IEs__Format, unit_format)).
Definition RRCReconfigurationComplete_v1560_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfigurationComplete_v1560_IEs__list RRCReconfigurationComplete_v1560_IEs__Format_list.
Definition RRCReconfigurationComplete_v1560_IEs__F1 z :=
  (RRCReconfigurationComplete_v1560_IEs__scg_Response z, (RRCReconfigurationComplete_v1560_IEs__nonCriticalExtension z, tt)).
Definition RRCReconfigurationComplete_v1560_IEs__F2 (y : seq_type RRCReconfigurationComplete_v1560_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfigurationComplete_v1560_IEs__Type i0 i1
  end.
Lemma RRCReconfigurationComplete_v1560_IEs__F1F2_cond (z : RRCReconfigurationComplete_v1560_IEs__Type)
  : RRCReconfigurationComplete_v1560_IEs__cond z ->
  (seq_cond RRCReconfigurationComplete_v1560_IEs__list (RRCReconfigurationComplete_v1560_IEs__F1 z)).
intro H. unfold RRCReconfigurationComplete_v1560_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationComplete_v1560_IEs__F1F2_cond2 (z : RRCReconfigurationComplete_v1560_IEs__Type)
 : RRCReconfigurationComplete_v1560_IEs__F2 (RRCReconfigurationComplete_v1560_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationComplete_v1560_IEs__F2F1_cond (y : seq_type RRCReconfigurationComplete_v1560_IEs__list)
  : seq_cond RRCReconfigurationComplete_v1560_IEs__list y ->
 (RRCReconfigurationComplete_v1560_IEs__cond (RRCReconfigurationComplete_v1560_IEs__F2 y)) /\  RRCReconfigurationComplete_v1560_IEs__F1 (RRCReconfigurationComplete_v1560_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationComplete_v1560_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationComplete_v1560_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationComplete_v1560_IEs__Format : T_Format RRCReconfigurationComplete_v1560_IEs__Type RRCReconfigurationComplete_v1560_IEs__cond :=
        proj2_format  RRCReconfigurationComplete_v1560_IEs__cond RRCReconfigurationComplete_v1560_IEs__list__Format
    RRCReconfigurationComplete_v1560_IEs__F1 RRCReconfigurationComplete_v1560_IEs__F2 RRCReconfigurationComplete_v1560_IEs__F1F2_cond  RRCReconfigurationComplete_v1560_IEs__F1F2_cond2 RRCReconfigurationComplete_v1560_IEs__F2F1_cond.
Opaque RRCReconfigurationComplete_v1560_IEs__cond RRCReconfigurationComplete_v1560_IEs__Format.

