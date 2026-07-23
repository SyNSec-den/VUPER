Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ProcessingParameters__fallback__Type : Set :=
 | ProcessingParameters__fallback__sc
 | ProcessingParameters__fallback__cap1_only
.
Definition ProcessingParameters__fallback__cond := (fun (_ : ProcessingParameters__fallback__Type) => True).
Lemma ProcessingParameters__fallback__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ProcessingParameters__fallback__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ProcessingParameters__fallback__nat__helper.

Definition ProcessingParameters__fallback__F1 t :=
  match t with
  | ProcessingParameters__fallback__sc => 0
  | ProcessingParameters__fallback__cap1_only => 1
  end.
Definition ProcessingParameters__fallback__F2 n :=
  match n with
  | 0 => ProcessingParameters__fallback__sc
  | 1 => ProcessingParameters__fallback__cap1_only
  | _ => ProcessingParameters__fallback__sc
  end.
Lemma ProcessingParameters__fallback__F1F2 : forall x : ProcessingParameters__fallback__Type, (ProcessingParameters__fallback__F1 x <= 1) /\ ProcessingParameters__fallback__F2 (ProcessingParameters__fallback__F1 x) = x. imp_solve. Qed.
Lemma ProcessingParameters__fallback__F2F1 : forall (y : nat) (H : y <= 1), ProcessingParameters__fallback__F1 (ProcessingParameters__fallback__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NumberOfCarriers.

Opaque NumberOfCarriers__cond NumberOfCarriers__Format.

Require Import NR.NumberOfCarriers.

Opaque NumberOfCarriers__cond NumberOfCarriers__Format.

Require Import NR.NumberOfCarriers.

Opaque NumberOfCarriers__cond NumberOfCarriers__Format.

Require Import NR.NumberOfCarriers.

Opaque NumberOfCarriers__cond NumberOfCarriers__Format.

Record ProcessingParameters__differentTB_PerSlot__Type : Set :=
  make__ProcessingParameters__differentTB_PerSlot__Type {
    ProcessingParameters__differentTB_PerSlot__upto1 : option NumberOfCarriers__Type ;
    ProcessingParameters__differentTB_PerSlot__upto2 : option NumberOfCarriers__Type ;
    ProcessingParameters__differentTB_PerSlot__upto4 : option NumberOfCarriers__Type ;
    ProcessingParameters__differentTB_PerSlot__upto7 : option NumberOfCarriers__Type ;
}.
Definition ProcessingParameters__differentTB_PerSlot__list := (
 Opt NumberOfCarriers__Type NumberOfCarriers__cond ::
 Opt NumberOfCarriers__Type NumberOfCarriers__cond ::
 Opt NumberOfCarriers__Type NumberOfCarriers__cond ::
 Opt NumberOfCarriers__Type NumberOfCarriers__cond ::
 nil).
Definition ProcessingParameters__differentTB_PerSlot__cond z := 
  opt_cond NumberOfCarriers__cond (ProcessingParameters__differentTB_PerSlot__upto1 z) /\
  opt_cond NumberOfCarriers__cond (ProcessingParameters__differentTB_PerSlot__upto2 z) /\
  opt_cond NumberOfCarriers__cond (ProcessingParameters__differentTB_PerSlot__upto4 z) /\
  opt_cond NumberOfCarriers__cond (ProcessingParameters__differentTB_PerSlot__upto7 z) /\
  True.

Record ProcessingParameters__Type : Set :=
  make__ProcessingParameters__Type {
    ProcessingParameters__fallback : ProcessingParameters__fallback__Type ;
    ProcessingParameters__differentTB_PerSlot : option ProcessingParameters__differentTB_PerSlot__Type ;
}.
Definition ProcessingParameters__list := (
 Nor ProcessingParameters__fallback__Type ProcessingParameters__fallback__cond ::
 Opt ProcessingParameters__differentTB_PerSlot__Type ProcessingParameters__differentTB_PerSlot__cond ::
 nil).
Definition ProcessingParameters__cond z := 
  ProcessingParameters__fallback__cond (ProcessingParameters__fallback z) /\
  opt_cond ProcessingParameters__differentTB_PerSlot__cond (ProcessingParameters__differentTB_PerSlot z) /\
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
Definition ProcessingParameters__fallback__Format : T_Format ProcessingParameters__fallback__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ProcessingParameters__fallback__nat__Format ProcessingParameters__fallback__F1 ProcessingParameters__fallback__F2 ProcessingParameters__fallback__F1F2 ProcessingParameters__fallback__F2F1.

Opaque ProcessingParameters__fallback__cond ProcessingParameters__fallback__Format.


Definition ProcessingParameters__differentTB_PerSlot__Format_Type := Eval cbn in seq_format_prod ProcessingParameters__differentTB_PerSlot__list.
Definition ProcessingParameters__differentTB_PerSlot__Format_list : ProcessingParameters__differentTB_PerSlot__Format_Type :=
  (NumberOfCarriers__Format, (NumberOfCarriers__Format, (NumberOfCarriers__Format, (NumberOfCarriers__Format, unit_format)))).
Definition ProcessingParameters__differentTB_PerSlot__list__Format := (*Eval compute in *) seq_format ProcessingParameters__differentTB_PerSlot__list ProcessingParameters__differentTB_PerSlot__Format_list.
Definition ProcessingParameters__differentTB_PerSlot__F1 z :=
  (ProcessingParameters__differentTB_PerSlot__upto1 z, (ProcessingParameters__differentTB_PerSlot__upto2 z, (ProcessingParameters__differentTB_PerSlot__upto4 z, (ProcessingParameters__differentTB_PerSlot__upto7 z, tt)))).
Definition ProcessingParameters__differentTB_PerSlot__F2 (y : seq_type ProcessingParameters__differentTB_PerSlot__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ProcessingParameters__differentTB_PerSlot__Type i0 i1 i2 i3
  end.
Lemma ProcessingParameters__differentTB_PerSlot__F1F2_cond (z : ProcessingParameters__differentTB_PerSlot__Type)
  : ProcessingParameters__differentTB_PerSlot__cond z ->
  (seq_cond ProcessingParameters__differentTB_PerSlot__list (ProcessingParameters__differentTB_PerSlot__F1 z)).
intro H. unfold ProcessingParameters__differentTB_PerSlot__cond in H. simpl. auto. Qed.
Lemma ProcessingParameters__differentTB_PerSlot__F1F2_cond2 (z : ProcessingParameters__differentTB_PerSlot__Type)
 : ProcessingParameters__differentTB_PerSlot__F2 (ProcessingParameters__differentTB_PerSlot__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ProcessingParameters__differentTB_PerSlot__F2F1_cond (y : seq_type ProcessingParameters__differentTB_PerSlot__list)
  : seq_cond ProcessingParameters__differentTB_PerSlot__list y ->
 (ProcessingParameters__differentTB_PerSlot__cond (ProcessingParameters__differentTB_PerSlot__F2 y)) /\  ProcessingParameters__differentTB_PerSlot__F1 (ProcessingParameters__differentTB_PerSlot__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ProcessingParameters__differentTB_PerSlot__cond. simpl in *. auto.
 - simpl. unfold ProcessingParameters__differentTB_PerSlot__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ProcessingParameters__differentTB_PerSlot__Format : T_Format ProcessingParameters__differentTB_PerSlot__Type ProcessingParameters__differentTB_PerSlot__cond :=
        proj2_format  ProcessingParameters__differentTB_PerSlot__cond ProcessingParameters__differentTB_PerSlot__list__Format
    ProcessingParameters__differentTB_PerSlot__F1 ProcessingParameters__differentTB_PerSlot__F2 ProcessingParameters__differentTB_PerSlot__F1F2_cond  ProcessingParameters__differentTB_PerSlot__F1F2_cond2 ProcessingParameters__differentTB_PerSlot__F2F1_cond.
Opaque ProcessingParameters__differentTB_PerSlot__cond ProcessingParameters__differentTB_PerSlot__Format.


Definition ProcessingParameters__Format_Type := Eval cbn in seq_format_prod ProcessingParameters__list.
Definition ProcessingParameters__Format_list : ProcessingParameters__Format_Type :=
  (ProcessingParameters__fallback__Format, (ProcessingParameters__differentTB_PerSlot__Format, unit_format)).
Definition ProcessingParameters__list__Format := (*Eval compute in *) seq_format ProcessingParameters__list ProcessingParameters__Format_list.
Definition ProcessingParameters__F1 z :=
  (ProcessingParameters__fallback z, (ProcessingParameters__differentTB_PerSlot z, tt)).
Definition ProcessingParameters__F2 (y : seq_type ProcessingParameters__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ProcessingParameters__Type i0 i1
  end.
Lemma ProcessingParameters__F1F2_cond (z : ProcessingParameters__Type)
  : ProcessingParameters__cond z ->
  (seq_cond ProcessingParameters__list (ProcessingParameters__F1 z)).
intro H. unfold ProcessingParameters__cond in H. simpl. auto. Qed.
Lemma ProcessingParameters__F1F2_cond2 (z : ProcessingParameters__Type)
 : ProcessingParameters__F2 (ProcessingParameters__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ProcessingParameters__F2F1_cond (y : seq_type ProcessingParameters__list)
  : seq_cond ProcessingParameters__list y ->
 (ProcessingParameters__cond (ProcessingParameters__F2 y)) /\  ProcessingParameters__F1 (ProcessingParameters__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ProcessingParameters__cond. simpl in *. auto.
 - simpl. unfold ProcessingParameters__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ProcessingParameters__Format : T_Format ProcessingParameters__Type ProcessingParameters__cond :=
        proj2_format  ProcessingParameters__cond ProcessingParameters__list__Format
    ProcessingParameters__F1 ProcessingParameters__F2 ProcessingParameters__F1F2_cond  ProcessingParameters__F1F2_cond2 ProcessingParameters__F2F1_cond.
Opaque ProcessingParameters__cond ProcessingParameters__Format.

