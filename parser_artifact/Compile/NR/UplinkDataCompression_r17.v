Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UplinkDataCompression_r17__newSetup__bufferSize_r17__Type : Set :=
 | UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte2
 | UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte4
 | UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte8
 | UplinkDataCompression_r17__newSetup__bufferSize_r17__spare1
.
Definition UplinkDataCompression_r17__newSetup__bufferSize_r17__cond := (fun (_ : UplinkDataCompression_r17__newSetup__bufferSize_r17__Type) => True).
Lemma UplinkDataCompression_r17__newSetup__bufferSize_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkDataCompression_r17__newSetup__bufferSize_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 UplinkDataCompression_r17__newSetup__bufferSize_r17__nat__helper.

Definition UplinkDataCompression_r17__newSetup__bufferSize_r17__F1 t :=
  match t with
  | UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte2 => 0
  | UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte4 => 1
  | UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte8 => 2
  | UplinkDataCompression_r17__newSetup__bufferSize_r17__spare1 => 3
  end.
Definition UplinkDataCompression_r17__newSetup__bufferSize_r17__F2 n :=
  match n with
  | 0 => UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte2
  | 1 => UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte4
  | 2 => UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte8
  | 3 => UplinkDataCompression_r17__newSetup__bufferSize_r17__spare1
  | _ => UplinkDataCompression_r17__newSetup__bufferSize_r17__kbyte2
  end.
Lemma UplinkDataCompression_r17__newSetup__bufferSize_r17__F1F2 : forall x : UplinkDataCompression_r17__newSetup__bufferSize_r17__Type, (UplinkDataCompression_r17__newSetup__bufferSize_r17__F1 x <= 3) /\ UplinkDataCompression_r17__newSetup__bufferSize_r17__F2 (UplinkDataCompression_r17__newSetup__bufferSize_r17__F1 x) = x. imp_solve. Qed.
Lemma UplinkDataCompression_r17__newSetup__bufferSize_r17__F2F1 : forall (y : nat) (H : y <= 3), UplinkDataCompression_r17__newSetup__bufferSize_r17__F1 (UplinkDataCompression_r17__newSetup__bufferSize_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UplinkDataCompression_r17__newSetup__dictionary_r17__Type : Set :=
 | UplinkDataCompression_r17__newSetup__dictionary_r17__sip_SDP
 | UplinkDataCompression_r17__newSetup__dictionary_r17__operator
.
Definition UplinkDataCompression_r17__newSetup__dictionary_r17__cond := (fun (_ : UplinkDataCompression_r17__newSetup__dictionary_r17__Type) => True).
Lemma UplinkDataCompression_r17__newSetup__dictionary_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkDataCompression_r17__newSetup__dictionary_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 UplinkDataCompression_r17__newSetup__dictionary_r17__nat__helper.

Definition UplinkDataCompression_r17__newSetup__dictionary_r17__F1 t :=
  match t with
  | UplinkDataCompression_r17__newSetup__dictionary_r17__sip_SDP => 0
  | UplinkDataCompression_r17__newSetup__dictionary_r17__operator => 1
  end.
Definition UplinkDataCompression_r17__newSetup__dictionary_r17__F2 n :=
  match n with
  | 0 => UplinkDataCompression_r17__newSetup__dictionary_r17__sip_SDP
  | 1 => UplinkDataCompression_r17__newSetup__dictionary_r17__operator
  | _ => UplinkDataCompression_r17__newSetup__dictionary_r17__sip_SDP
  end.
Lemma UplinkDataCompression_r17__newSetup__dictionary_r17__F1F2 : forall x : UplinkDataCompression_r17__newSetup__dictionary_r17__Type, (UplinkDataCompression_r17__newSetup__dictionary_r17__F1 x <= 1) /\ UplinkDataCompression_r17__newSetup__dictionary_r17__F2 (UplinkDataCompression_r17__newSetup__dictionary_r17__F1 x) = x. imp_solve. Qed.
Lemma UplinkDataCompression_r17__newSetup__dictionary_r17__F2F1 : forall (y : nat) (H : y <= 1), UplinkDataCompression_r17__newSetup__dictionary_r17__F1 (UplinkDataCompression_r17__newSetup__dictionary_r17__F2 y) = y. enum_solve H y. Qed.

Record UplinkDataCompression_r17__newSetup__Type : Set :=
  make__UplinkDataCompression_r17__newSetup__Type {
    UplinkDataCompression_r17__newSetup__bufferSize_r17 : UplinkDataCompression_r17__newSetup__bufferSize_r17__Type ;
    UplinkDataCompression_r17__newSetup__dictionary_r17 : option UplinkDataCompression_r17__newSetup__dictionary_r17__Type ;
}.
Definition UplinkDataCompression_r17__newSetup__list := (
 Nor UplinkDataCompression_r17__newSetup__bufferSize_r17__Type UplinkDataCompression_r17__newSetup__bufferSize_r17__cond ::
 Opt UplinkDataCompression_r17__newSetup__dictionary_r17__Type UplinkDataCompression_r17__newSetup__dictionary_r17__cond ::
 nil).
Definition UplinkDataCompression_r17__newSetup__cond z := 
  UplinkDataCompression_r17__newSetup__bufferSize_r17__cond (UplinkDataCompression_r17__newSetup__bufferSize_r17 z) /\
  opt_cond UplinkDataCompression_r17__newSetup__dictionary_r17__cond (UplinkDataCompression_r17__newSetup__dictionary_r17 z) /\
  True.


Inductive UplinkDataCompression_r17__Type : Set :=
  | UplinkDataCompression_r17__newSetup : UplinkDataCompression_r17__newSetup__Type -> UplinkDataCompression_r17__Type
  | UplinkDataCompression_r17__drb_ContinueUDC : unit -> UplinkDataCompression_r17__Type
.
Definition UplinkDataCompression_r17__list : list typ := (
typ_cons UplinkDataCompression_r17__newSetup__Type UplinkDataCompression_r17__newSetup__cond ::
typ_cons unit (fun _ => True) ::
 nil).
Definition UplinkDataCompression_r17__cond (c : UplinkDataCompression_r17__Type) := 
  match c with
  | UplinkDataCompression_r17__newSetup t => UplinkDataCompression_r17__newSetup__cond t 
  | UplinkDataCompression_r17__drb_ContinueUDC t => (fun _ => True) t 
  end.

Lemma UplinkDataCompression_r17__len_helper1 : to_bit_sz (length UplinkDataCompression_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UplinkDataCompression_r17__len_helper2 : 2 <= length2 UplinkDataCompression_r17__list.
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
Definition UplinkDataCompression_r17__newSetup__bufferSize_r17__Format : T_Format UplinkDataCompression_r17__newSetup__bufferSize_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkDataCompression_r17__newSetup__bufferSize_r17__nat__Format UplinkDataCompression_r17__newSetup__bufferSize_r17__F1 UplinkDataCompression_r17__newSetup__bufferSize_r17__F2 UplinkDataCompression_r17__newSetup__bufferSize_r17__F1F2 UplinkDataCompression_r17__newSetup__bufferSize_r17__F2F1.

Opaque UplinkDataCompression_r17__newSetup__bufferSize_r17__cond UplinkDataCompression_r17__newSetup__bufferSize_r17__Format.

Definition UplinkDataCompression_r17__newSetup__dictionary_r17__Format : T_Format UplinkDataCompression_r17__newSetup__dictionary_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkDataCompression_r17__newSetup__dictionary_r17__nat__Format UplinkDataCompression_r17__newSetup__dictionary_r17__F1 UplinkDataCompression_r17__newSetup__dictionary_r17__F2 UplinkDataCompression_r17__newSetup__dictionary_r17__F1F2 UplinkDataCompression_r17__newSetup__dictionary_r17__F2F1.

Opaque UplinkDataCompression_r17__newSetup__dictionary_r17__cond UplinkDataCompression_r17__newSetup__dictionary_r17__Format.


Definition UplinkDataCompression_r17__newSetup__Format_Type := Eval cbn in seq_format_prod UplinkDataCompression_r17__newSetup__list.
Definition UplinkDataCompression_r17__newSetup__Format_list : UplinkDataCompression_r17__newSetup__Format_Type :=
  (UplinkDataCompression_r17__newSetup__bufferSize_r17__Format, (UplinkDataCompression_r17__newSetup__dictionary_r17__Format, unit_format)).
Definition UplinkDataCompression_r17__newSetup__list__Format := (*Eval compute in *) seq_format UplinkDataCompression_r17__newSetup__list UplinkDataCompression_r17__newSetup__Format_list.
Definition UplinkDataCompression_r17__newSetup__F1 z :=
  (UplinkDataCompression_r17__newSetup__bufferSize_r17 z, (UplinkDataCompression_r17__newSetup__dictionary_r17 z, tt)).
Definition UplinkDataCompression_r17__newSetup__F2 (y : seq_type UplinkDataCompression_r17__newSetup__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UplinkDataCompression_r17__newSetup__Type i0 i1
  end.
Lemma UplinkDataCompression_r17__newSetup__F1F2_cond (z : UplinkDataCompression_r17__newSetup__Type)
  : UplinkDataCompression_r17__newSetup__cond z ->
  (seq_cond UplinkDataCompression_r17__newSetup__list (UplinkDataCompression_r17__newSetup__F1 z)).
intro H. unfold UplinkDataCompression_r17__newSetup__cond in H. simpl. auto. Qed.
Lemma UplinkDataCompression_r17__newSetup__F1F2_cond2 (z : UplinkDataCompression_r17__newSetup__Type)
 : UplinkDataCompression_r17__newSetup__F2 (UplinkDataCompression_r17__newSetup__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkDataCompression_r17__newSetup__F2F1_cond (y : seq_type UplinkDataCompression_r17__newSetup__list)
  : seq_cond UplinkDataCompression_r17__newSetup__list y ->
 (UplinkDataCompression_r17__newSetup__cond (UplinkDataCompression_r17__newSetup__F2 y)) /\  UplinkDataCompression_r17__newSetup__F1 (UplinkDataCompression_r17__newSetup__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkDataCompression_r17__newSetup__cond. simpl in *. auto.
 - simpl. unfold UplinkDataCompression_r17__newSetup__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkDataCompression_r17__newSetup__Format : T_Format UplinkDataCompression_r17__newSetup__Type UplinkDataCompression_r17__newSetup__cond :=
        proj2_format  UplinkDataCompression_r17__newSetup__cond UplinkDataCompression_r17__newSetup__list__Format
    UplinkDataCompression_r17__newSetup__F1 UplinkDataCompression_r17__newSetup__F2 UplinkDataCompression_r17__newSetup__F1F2_cond  UplinkDataCompression_r17__newSetup__F1F2_cond2 UplinkDataCompression_r17__newSetup__F2F1_cond.
Opaque UplinkDataCompression_r17__newSetup__cond UplinkDataCompression_r17__newSetup__Format.


Definition UplinkDataCompression_r17__Format_Type := Eval cbn in get_formats UplinkDataCompression_r17__list.
Definition UplinkDataCompression_r17__Format_list : UplinkDataCompression_r17__Format_Type :=
  (UplinkDataCompression_r17__newSetup__Format, (unit__Format, unit__Format)).
Definition UplinkDataCompression_r17__list__Format := Eval compute in choice_format UplinkDataCompression_r17__list UplinkDataCompression_r17__len_helper1 UplinkDataCompression_r17__len_helper2  UplinkDataCompression_r17__Format_list.
Definition UplinkDataCompression_r17__F1 (z : UplinkDataCompression_r17__Type) : (choice UplinkDataCompression_r17__list) :=
  match z with
   | UplinkDataCompression_r17__newSetup t => existT _ 0 t
  | UplinkDataCompression_r17__drb_ContinueUDC t => existT _ 1 t
  end.
Definition UplinkDataCompression_r17__g := (fun n => typ_set (get_nth_typ UplinkDataCompression_r17__list n)).
Definition UplinkDataCompression_r17__F2 (y : choice UplinkDataCompression_r17__list) : UplinkDataCompression_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UplinkDataCompression_r17__g n -> UplinkDataCompression_r17__Type) with
    | 0 => fun (t : UplinkDataCompression_r17__newSetup__Type) => UplinkDataCompression_r17__newSetup t 
    | 1 => fun (t : unit) => UplinkDataCompression_r17__drb_ContinueUDC t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UplinkDataCompression_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UplinkDataCompression_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UplinkDataCompression_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UplinkDataCompression_r17__Type with end) n0
           end t0).

Lemma UplinkDataCompression_r17__helper2 :  forall (y : UplinkDataCompression_r17__Type), UplinkDataCompression_r17__cond y -> choice_cond UplinkDataCompression_r17__list (UplinkDataCompression_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UplinkDataCompression_r17__helper3 :  forall (y : UplinkDataCompression_r17__Type), UplinkDataCompression_r17__F2 (UplinkDataCompression_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UplinkDataCompression_r17__helper4 : (forall b : choice UplinkDataCompression_r17__list, choice_cond UplinkDataCompression_r17__list b -> UplinkDataCompression_r17__cond (UplinkDataCompression_r17__F2 b) /\ UplinkDataCompression_r17__F1 (UplinkDataCompression_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UplinkDataCompression_r17__F1 UplinkDataCompression_r17__F2.
Definition UplinkDataCompression_r17__Format : T_Format UplinkDataCompression_r17__Type UplinkDataCompression_r17__cond :=
  (* Eval compute in *) proj2_format UplinkDataCompression_r17__cond UplinkDataCompression_r17__list__Format UplinkDataCompression_r17__F1 UplinkDataCompression_r17__F2 UplinkDataCompression_r17__helper2 UplinkDataCompression_r17__helper3 UplinkDataCompression_r17__helper4.
Opaque UplinkDataCompression_r17__cond UplinkDataCompression_r17__Format.

