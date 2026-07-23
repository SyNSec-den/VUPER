Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FailureInfoDAPS_r16__failureType_r16__Type : Set :=
 | FailureInfoDAPS_r16__failureType_r16__daps_failure
 | FailureInfoDAPS_r16__failureType_r16__spare3
 | FailureInfoDAPS_r16__failureType_r16__spare2
 | FailureInfoDAPS_r16__failureType_r16__spare1
.
Definition FailureInfoDAPS_r16__failureType_r16__cond := (fun (_ : FailureInfoDAPS_r16__failureType_r16__Type) => True).
Lemma FailureInfoDAPS_r16__failureType_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FailureInfoDAPS_r16__failureType_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 FailureInfoDAPS_r16__failureType_r16__nat__helper.

Definition FailureInfoDAPS_r16__failureType_r16__F1 t :=
  match t with
  | FailureInfoDAPS_r16__failureType_r16__daps_failure => 0
  | FailureInfoDAPS_r16__failureType_r16__spare3 => 1
  | FailureInfoDAPS_r16__failureType_r16__spare2 => 2
  | FailureInfoDAPS_r16__failureType_r16__spare1 => 3
  end.
Definition FailureInfoDAPS_r16__failureType_r16__F2 n :=
  match n with
  | 0 => FailureInfoDAPS_r16__failureType_r16__daps_failure
  | 1 => FailureInfoDAPS_r16__failureType_r16__spare3
  | 2 => FailureInfoDAPS_r16__failureType_r16__spare2
  | 3 => FailureInfoDAPS_r16__failureType_r16__spare1
  | _ => FailureInfoDAPS_r16__failureType_r16__daps_failure
  end.
Lemma FailureInfoDAPS_r16__failureType_r16__F1F2 : forall x : FailureInfoDAPS_r16__failureType_r16__Type, (FailureInfoDAPS_r16__failureType_r16__F1 x <= 3) /\ FailureInfoDAPS_r16__failureType_r16__F2 (FailureInfoDAPS_r16__failureType_r16__F1 x) = x. imp_solve. Qed.
Lemma FailureInfoDAPS_r16__failureType_r16__F2F1 : forall (y : nat) (H : y <= 3), FailureInfoDAPS_r16__failureType_r16__F1 (FailureInfoDAPS_r16__failureType_r16__F2 y) = y. enum_solve H y. Qed.

Record FailureInfoDAPS_r16__Type : Set :=
  make__FailureInfoDAPS_r16__Type {
    FailureInfoDAPS_r16__failureType_r16 : FailureInfoDAPS_r16__failureType_r16__Type ;
}.
Definition FailureInfoDAPS_r16__list := (
 Nor FailureInfoDAPS_r16__failureType_r16__Type FailureInfoDAPS_r16__failureType_r16__cond ::
 nil).
Definition FailureInfoDAPS_r16__cond z := 
  FailureInfoDAPS_r16__failureType_r16__cond (FailureInfoDAPS_r16__failureType_r16 z) /\
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
Definition FailureInfoDAPS_r16__failureType_r16__Format : T_Format FailureInfoDAPS_r16__failureType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FailureInfoDAPS_r16__failureType_r16__nat__Format FailureInfoDAPS_r16__failureType_r16__F1 FailureInfoDAPS_r16__failureType_r16__F2 FailureInfoDAPS_r16__failureType_r16__F1F2 FailureInfoDAPS_r16__failureType_r16__F2F1.

Opaque FailureInfoDAPS_r16__failureType_r16__cond FailureInfoDAPS_r16__failureType_r16__Format.


Definition FailureInfoDAPS_r16__Format_Type := Eval cbn in seq_format_prod FailureInfoDAPS_r16__list.
Definition FailureInfoDAPS_r16__Format_list : FailureInfoDAPS_r16__Format_Type :=
  (FailureInfoDAPS_r16__failureType_r16__Format, unit_format).
Definition FailureInfoDAPS_r16__list__Format := (*Eval compute in *) seq_format FailureInfoDAPS_r16__list FailureInfoDAPS_r16__Format_list.
Definition FailureInfoDAPS_r16__F1 z :=
  (FailureInfoDAPS_r16__failureType_r16 z, tt).
Definition FailureInfoDAPS_r16__F2 (y : seq_type FailureInfoDAPS_r16__list) :=
  match y with
  | (i0, _)=>
    make__FailureInfoDAPS_r16__Type i0
  end.
Lemma FailureInfoDAPS_r16__F1F2_cond (z : FailureInfoDAPS_r16__Type)
  : FailureInfoDAPS_r16__cond z ->
  (seq_cond FailureInfoDAPS_r16__list (FailureInfoDAPS_r16__F1 z)).
intro H. unfold FailureInfoDAPS_r16__cond in H. simpl. auto. Qed.
Lemma FailureInfoDAPS_r16__F1F2_cond2 (z : FailureInfoDAPS_r16__Type)
 : FailureInfoDAPS_r16__F2 (FailureInfoDAPS_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureInfoDAPS_r16__F2F1_cond (y : seq_type FailureInfoDAPS_r16__list)
  : seq_cond FailureInfoDAPS_r16__list y ->
 (FailureInfoDAPS_r16__cond (FailureInfoDAPS_r16__F2 y)) /\  FailureInfoDAPS_r16__F1 (FailureInfoDAPS_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureInfoDAPS_r16__cond. simpl in *. auto.
 - simpl. unfold FailureInfoDAPS_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureInfoDAPS_r16__Format : T_Format FailureInfoDAPS_r16__Type FailureInfoDAPS_r16__cond :=
        proj2_format  FailureInfoDAPS_r16__cond FailureInfoDAPS_r16__list__Format
    FailureInfoDAPS_r16__F1 FailureInfoDAPS_r16__F2 FailureInfoDAPS_r16__F1F2_cond  FailureInfoDAPS_r16__F1F2_cond2 FailureInfoDAPS_r16__F2F1_cond.
Opaque FailureInfoDAPS_r16__cond FailureInfoDAPS_r16__Format.

