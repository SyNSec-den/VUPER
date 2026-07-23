Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Inductive FR_Info__fr_Type__Type : Set :=
 | FR_Info__fr_Type__fr1
 | FR_Info__fr_Type__fr2
.
Definition FR_Info__fr_Type__cond := (fun (_ : FR_Info__fr_Type__Type) => True).
Lemma FR_Info__fr_Type__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR_Info__fr_Type__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FR_Info__fr_Type__nat__helper.

Definition FR_Info__fr_Type__F1 t :=
  match t with
  | FR_Info__fr_Type__fr1 => 0
  | FR_Info__fr_Type__fr2 => 1
  end.
Definition FR_Info__fr_Type__F2 n :=
  match n with
  | 0 => FR_Info__fr_Type__fr1
  | 1 => FR_Info__fr_Type__fr2
  | _ => FR_Info__fr_Type__fr1
  end.
Lemma FR_Info__fr_Type__F1F2 : forall x : FR_Info__fr_Type__Type, (FR_Info__fr_Type__F1 x <= 1) /\ FR_Info__fr_Type__F2 (FR_Info__fr_Type__F1 x) = x. imp_solve. Qed.
Lemma FR_Info__fr_Type__F2F1 : forall (y : nat) (H : y <= 1), FR_Info__fr_Type__F1 (FR_Info__fr_Type__F2 y) = y. enum_solve H y. Qed.

Record FR_Info__Type : Set :=
  make__FR_Info__Type {
    FR_Info__servCellIndex : ServCellIndex__Type ;
    FR_Info__fr_Type : FR_Info__fr_Type__Type ;
}.
Definition FR_Info__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor FR_Info__fr_Type__Type FR_Info__fr_Type__cond ::
 nil).
Definition FR_Info__cond z := 
  ServCellIndex__cond (FR_Info__servCellIndex z) /\
  FR_Info__fr_Type__cond (FR_Info__fr_Type z) /\
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
Definition FR_Info__fr_Type__Format : T_Format FR_Info__fr_Type__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR_Info__fr_Type__nat__Format FR_Info__fr_Type__F1 FR_Info__fr_Type__F2 FR_Info__fr_Type__F1F2 FR_Info__fr_Type__F2F1.

Opaque FR_Info__fr_Type__cond FR_Info__fr_Type__Format.


Definition FR_Info__Format_Type := Eval cbn in seq_format_prod FR_Info__list.
Definition FR_Info__Format_list : FR_Info__Format_Type :=
  (ServCellIndex__Format, (FR_Info__fr_Type__Format, unit_format)).
Definition FR_Info__list__Format := (*Eval compute in *) seq_format FR_Info__list FR_Info__Format_list.
Definition FR_Info__F1 z :=
  (FR_Info__servCellIndex z, (FR_Info__fr_Type z, tt)).
Definition FR_Info__F2 (y : seq_type FR_Info__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FR_Info__Type i0 i1
  end.
Lemma FR_Info__F1F2_cond (z : FR_Info__Type)
  : FR_Info__cond z ->
  (seq_cond FR_Info__list (FR_Info__F1 z)).
intro H. unfold FR_Info__cond in H. simpl. auto. Qed.
Lemma FR_Info__F1F2_cond2 (z : FR_Info__Type)
 : FR_Info__F2 (FR_Info__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FR_Info__F2F1_cond (y : seq_type FR_Info__list)
  : seq_cond FR_Info__list y ->
 (FR_Info__cond (FR_Info__F2 y)) /\  FR_Info__F1 (FR_Info__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FR_Info__cond. simpl in *. auto.
 - simpl. unfold FR_Info__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FR_Info__Format : T_Format FR_Info__Type FR_Info__cond :=
        proj2_format  FR_Info__cond FR_Info__list__Format
    FR_Info__F1 FR_Info__F2 FR_Info__F1F2_cond  FR_Info__F1F2_cond2 FR_Info__F2F1_cond.
Opaque FR_Info__cond FR_Info__Format.

