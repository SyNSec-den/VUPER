Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Type : Set :=
 | RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__true
.
Definition RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__cond := (fun (_ : RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Type) => True).
Lemma RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__nat__helper.

Definition RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1 t :=
  match t with
  | RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__true => 0
  end.
Definition RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F2 n :=
  match n with
  | 0 => RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__true
  | _ => RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__true
  end.
Lemma RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1F2 : forall x : RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Type, (RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1 x <= 0) /\ RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F2 (RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1 x) = x. imp_solve. Qed.
Lemma RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F2F1 : forall (y : nat) (H : y <= 0), RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1 (RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Type : Set :=
 | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__barred
 | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__notBarred
.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__cond := (fun (_ : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Type) => True).
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__nat__helper.

Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1 t :=
  match t with
  | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__barred => 0
  | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__notBarred => 1
  end.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F2 n :=
  match n with
  | 0 => RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__barred
  | 1 => RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__notBarred
  | _ => RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__barred
  end.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1F2 : forall x : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Type, (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1 x <= 1) /\ RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F2 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1 x) = x. imp_solve. Qed.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F2F1 : forall (y : nat) (H : y <= 1), RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Type : Set :=
 | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__barred
 | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__notBarred
.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__cond := (fun (_ : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Type) => True).
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__nat__helper.

Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1 t :=
  match t with
  | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__barred => 0
  | RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__notBarred => 1
  end.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F2 n :=
  match n with
  | 0 => RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__barred
  | 1 => RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__notBarred
  | _ => RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__barred
  end.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1F2 : forall x : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Type, (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1 x <= 1) /\ RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F2 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1 x) = x. imp_solve. Qed.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F2F1 : forall (y : nat) (H : y <= 1), RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F2 y) = y. enum_solve H y. Qed.

Record RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type : Set :=
  make__RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type {
    RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17 : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Type ;
    RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17 : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Type ;
}.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list := (
 Nor RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Type RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__cond ::
 Nor RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Type RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__cond ::
 nil).
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond z := 
  RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__cond (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17 z) /\
  RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__cond (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17 z) /\
  True.

Record RedCap_ConfigCommonSIB_r17__Type : Set :=
  make__RedCap_ConfigCommonSIB_r17__Type {
    RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17 : option RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Type ;
    RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17 : option RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type ;
}.
Definition RedCap_ConfigCommonSIB_r17__root_list : list seq_elem := (
 Opt RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Type RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__cond ::
 Opt RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond ::
 nil).
Definition RedCap_ConfigCommonSIB_r17__ext_list : list typ := (
  nil).
Definition RedCap_ConfigCommonSIB_r17__cond (z : RedCap_ConfigCommonSIB_r17__Type) := 
(  opt_cond RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__cond (RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17 z) /\
  opt_cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17 z) /\
  True) /\ 
(  True).


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
Definition RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Format : T_Format RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__nat__Format RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1 RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F2 RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F1F2 RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__F2F1.

Opaque RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__cond RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Format.

Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Format : T_Format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__nat__Format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F2 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F1F2 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__F2F1.

Opaque RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Format.

Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Format : T_Format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__nat__Format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F2 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F1F2 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__F2F1.

Opaque RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Format.


Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format_Type := Eval cbn in seq_format_prod RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format_list : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format_Type :=
  (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17__Format, (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17__Format, unit_format)).
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list__Format := (*Eval compute in *) seq_format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format_list.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1 z :=
  (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap1Rx_r17 z, (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cellBarredRedCap2Rx_r17 z, tt)).
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2 (y : seq_type RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type i0 i1
  end.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1F2_cond (z : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type)
  : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond z ->
  (seq_cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1 z)).
intro H. unfold RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond in H. simpl. auto. Qed.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1F2_cond2 (z : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type)
 : RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2F1_cond (y : seq_type RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list)
  : seq_cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list y ->
 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2 y)) /\  RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1 (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond. simpl in *. auto.
 - simpl. unfold RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format : T_Format RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Type RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond :=
        proj2_format  RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__list__Format
    RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1F2_cond  RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F1F2_cond2 RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__F2F1_cond.
Opaque RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__cond RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format.


Definition RedCap_ConfigCommonSIB_r17__root_Format_Type := Eval cbn in seq_format_prod RedCap_ConfigCommonSIB_r17__root_list.
Definition RedCap_ConfigCommonSIB_r17__root_Format_list : RedCap_ConfigCommonSIB_r17__root_Format_Type :=
  (RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17__Format, (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17__Format, unit_format)).

Definition RedCap_ConfigCommonSIB_r17__ext_Format_Type := Eval cbn in get_formats RedCap_ConfigCommonSIB_r17__ext_list.
Definition RedCap_ConfigCommonSIB_r17__ext_Format_list : RedCap_ConfigCommonSIB_r17__ext_Format_Type :=
  unit__Format.

Definition RedCap_ConfigCommonSIB_r17__list_type : Set := (seq_type RedCap_ConfigCommonSIB_r17__root_list) * (seq_ext_type RedCap_ConfigCommonSIB_r17__ext_list).
Definition RedCap_ConfigCommonSIB_r17__list_cond (z : RedCap_ConfigCommonSIB_r17__list_type) : Prop :=
        (seq_cond RedCap_ConfigCommonSIB_r17__root_list (fst z)) /\ (seq_ext_cond RedCap_ConfigCommonSIB_r17__ext_list (snd z)).
Definition RedCap_ConfigCommonSIB_r17__list_format : T_Format RedCap_ConfigCommonSIB_r17__list_type RedCap_ConfigCommonSIB_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RedCap_ConfigCommonSIB_r17__root_list RedCap_ConfigCommonSIB_r17__root_Format_list RedCap_ConfigCommonSIB_r17__ext_list RedCap_ConfigCommonSIB_r17__ext_Format_list.

Opaque RedCap_ConfigCommonSIB_r17__list_format.
Definition RedCap_ConfigCommonSIB_r17__F1 (z : RedCap_ConfigCommonSIB_r17__Type) : RedCap_ConfigCommonSIB_r17__list_type :=
  (((RedCap_ConfigCommonSIB_r17__halfDuplexRedCapAllowed_r17 z, (RedCap_ConfigCommonSIB_r17__cellBarredRedCap_r17 z, tt))), (
tt)).
Definition RedCap_ConfigCommonSIB_r17__F2 (y : RedCap_ConfigCommonSIB_r17__list_type) : RedCap_ConfigCommonSIB_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__RedCap_ConfigCommonSIB_r17__Type j0 j1
  end.
Definition RedCap_ConfigCommonSIB_r17__helper1 : (forall a : RedCap_ConfigCommonSIB_r17__Type, RedCap_ConfigCommonSIB_r17__cond a -> RedCap_ConfigCommonSIB_r17__list_cond (RedCap_ConfigCommonSIB_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RedCap_ConfigCommonSIB_r17__helper2 : (forall a : RedCap_ConfigCommonSIB_r17__Type, RedCap_ConfigCommonSIB_r17__F2 (RedCap_ConfigCommonSIB_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RedCap_ConfigCommonSIB_r17__helper3 : (forall b : RedCap_ConfigCommonSIB_r17__list_type, RedCap_ConfigCommonSIB_r17__list_cond b -> RedCap_ConfigCommonSIB_r17__cond (RedCap_ConfigCommonSIB_r17__F2 b) /\ RedCap_ConfigCommonSIB_r17__F1 (RedCap_ConfigCommonSIB_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RedCap_ConfigCommonSIB_r17__cond, RedCap_ConfigCommonSIB_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RedCap_ConfigCommonSIB_r17__Format : T_Format RedCap_ConfigCommonSIB_r17__Type RedCap_ConfigCommonSIB_r17__cond :=
 proj2_format RedCap_ConfigCommonSIB_r17__cond RedCap_ConfigCommonSIB_r17__list_format  RedCap_ConfigCommonSIB_r17__F1 RedCap_ConfigCommonSIB_r17__F2 RedCap_ConfigCommonSIB_r17__helper1 RedCap_ConfigCommonSIB_r17__helper2 RedCap_ConfigCommonSIB_r17__helper3.

Opaque RedCap_ConfigCommonSIB_r17__cond RedCap_ConfigCommonSIB_r17__Format.

