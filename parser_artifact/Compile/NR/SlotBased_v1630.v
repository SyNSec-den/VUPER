Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SlotBased_v1630__tciMapping_r16__Type : Set :=
 | SlotBased_v1630__tciMapping_r16__cyclicMapping
 | SlotBased_v1630__tciMapping_r16__sequentialMapping
.
Definition SlotBased_v1630__tciMapping_r16__cond := (fun (_ : SlotBased_v1630__tciMapping_r16__Type) => True).
Lemma SlotBased_v1630__tciMapping_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SlotBased_v1630__tciMapping_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SlotBased_v1630__tciMapping_r16__nat__helper.

Definition SlotBased_v1630__tciMapping_r16__F1 t :=
  match t with
  | SlotBased_v1630__tciMapping_r16__cyclicMapping => 0
  | SlotBased_v1630__tciMapping_r16__sequentialMapping => 1
  end.
Definition SlotBased_v1630__tciMapping_r16__F2 n :=
  match n with
  | 0 => SlotBased_v1630__tciMapping_r16__cyclicMapping
  | 1 => SlotBased_v1630__tciMapping_r16__sequentialMapping
  | _ => SlotBased_v1630__tciMapping_r16__cyclicMapping
  end.
Lemma SlotBased_v1630__tciMapping_r16__F1F2 : forall x : SlotBased_v1630__tciMapping_r16__Type, (SlotBased_v1630__tciMapping_r16__F1 x <= 1) /\ SlotBased_v1630__tciMapping_r16__F2 (SlotBased_v1630__tciMapping_r16__F1 x) = x. imp_solve. Qed.
Lemma SlotBased_v1630__tciMapping_r16__F2F1 : forall (y : nat) (H : y <= 1), SlotBased_v1630__tciMapping_r16__F1 (SlotBased_v1630__tciMapping_r16__F2 y) = y. enum_solve H y. Qed.

Definition SlotBased_v1630__sequenceOffsetForRV_r16__Type := Z.
Definition SlotBased_v1630__sequenceOffsetForRV_r16__cond := (fun z : Z => z = 0)%Z.
Record SlotBased_v1630__Type : Set :=
  make__SlotBased_v1630__Type {
    SlotBased_v1630__tciMapping_r16 : SlotBased_v1630__tciMapping_r16__Type ;
    SlotBased_v1630__sequenceOffsetForRV_r16 : Z ;
}.
Definition SlotBased_v1630__list := (
 Nor SlotBased_v1630__tciMapping_r16__Type SlotBased_v1630__tciMapping_r16__cond ::
 Nor Z SlotBased_v1630__sequenceOffsetForRV_r16__cond ::
 nil).
Definition SlotBased_v1630__cond z := 
  SlotBased_v1630__tciMapping_r16__cond (SlotBased_v1630__tciMapping_r16 z) /\
  SlotBased_v1630__sequenceOffsetForRV_r16__cond (SlotBased_v1630__sequenceOffsetForRV_r16 z) /\
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
Definition SlotBased_v1630__tciMapping_r16__Format : T_Format SlotBased_v1630__tciMapping_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SlotBased_v1630__tciMapping_r16__nat__Format SlotBased_v1630__tciMapping_r16__F1 SlotBased_v1630__tciMapping_r16__F2 SlotBased_v1630__tciMapping_r16__F1F2 SlotBased_v1630__tciMapping_r16__F2F1.

Opaque SlotBased_v1630__tciMapping_r16__cond SlotBased_v1630__tciMapping_r16__Format.

Definition SlotBased_v1630__sequenceOffsetForRV_r16__Format : T_Format Z SlotBased_v1630__sequenceOffsetForRV_r16__cond := fixed_int_format 0. Opaque SlotBased_v1630__sequenceOffsetForRV_r16__cond SlotBased_v1630__sequenceOffsetForRV_r16__Format.


Definition SlotBased_v1630__Format_Type := Eval cbn in seq_format_prod SlotBased_v1630__list.
Definition SlotBased_v1630__Format_list : SlotBased_v1630__Format_Type :=
  (SlotBased_v1630__tciMapping_r16__Format, (SlotBased_v1630__sequenceOffsetForRV_r16__Format, unit_format)).
Definition SlotBased_v1630__list__Format := (*Eval compute in *) seq_format SlotBased_v1630__list SlotBased_v1630__Format_list.
Definition SlotBased_v1630__F1 z :=
  (SlotBased_v1630__tciMapping_r16 z, (SlotBased_v1630__sequenceOffsetForRV_r16 z, tt)).
Definition SlotBased_v1630__F2 (y : seq_type SlotBased_v1630__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SlotBased_v1630__Type i0 i1
  end.
Lemma SlotBased_v1630__F1F2_cond (z : SlotBased_v1630__Type)
  : SlotBased_v1630__cond z ->
  (seq_cond SlotBased_v1630__list (SlotBased_v1630__F1 z)).
intro H. unfold SlotBased_v1630__cond in H. simpl. auto. Qed.
Lemma SlotBased_v1630__F1F2_cond2 (z : SlotBased_v1630__Type)
 : SlotBased_v1630__F2 (SlotBased_v1630__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SlotBased_v1630__F2F1_cond (y : seq_type SlotBased_v1630__list)
  : seq_cond SlotBased_v1630__list y ->
 (SlotBased_v1630__cond (SlotBased_v1630__F2 y)) /\  SlotBased_v1630__F1 (SlotBased_v1630__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SlotBased_v1630__cond. simpl in *. auto.
 - simpl. unfold SlotBased_v1630__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SlotBased_v1630__Format : T_Format SlotBased_v1630__Type SlotBased_v1630__cond :=
        proj2_format  SlotBased_v1630__cond SlotBased_v1630__list__Format
    SlotBased_v1630__F1 SlotBased_v1630__F2 SlotBased_v1630__F1F2_cond  SlotBased_v1630__F1F2_cond2 SlotBased_v1630__F2F1_cond.
Opaque SlotBased_v1630__cond SlotBased_v1630__Format.

