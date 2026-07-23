Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BCCH_Config__modificationPeriodCoeff__Type : Set :=
 | BCCH_Config__modificationPeriodCoeff__n2
 | BCCH_Config__modificationPeriodCoeff__n4
 | BCCH_Config__modificationPeriodCoeff__n8
 | BCCH_Config__modificationPeriodCoeff__n16
.
Definition BCCH_Config__modificationPeriodCoeff__cond := (fun (_ : BCCH_Config__modificationPeriodCoeff__Type) => True).
Lemma BCCH_Config__modificationPeriodCoeff__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BCCH_Config__modificationPeriodCoeff__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BCCH_Config__modificationPeriodCoeff__nat__helper.

Definition BCCH_Config__modificationPeriodCoeff__F1 t :=
  match t with
  | BCCH_Config__modificationPeriodCoeff__n2 => 0
  | BCCH_Config__modificationPeriodCoeff__n4 => 1
  | BCCH_Config__modificationPeriodCoeff__n8 => 2
  | BCCH_Config__modificationPeriodCoeff__n16 => 3
  end.
Definition BCCH_Config__modificationPeriodCoeff__F2 n :=
  match n with
  | 0 => BCCH_Config__modificationPeriodCoeff__n2
  | 1 => BCCH_Config__modificationPeriodCoeff__n4
  | 2 => BCCH_Config__modificationPeriodCoeff__n8
  | 3 => BCCH_Config__modificationPeriodCoeff__n16
  | _ => BCCH_Config__modificationPeriodCoeff__n2
  end.
Lemma BCCH_Config__modificationPeriodCoeff__F1F2 : forall x : BCCH_Config__modificationPeriodCoeff__Type, (BCCH_Config__modificationPeriodCoeff__F1 x <= 3) /\ BCCH_Config__modificationPeriodCoeff__F2 (BCCH_Config__modificationPeriodCoeff__F1 x) = x. imp_solve. Qed.
Lemma BCCH_Config__modificationPeriodCoeff__F2F1 : forall (y : nat) (H : y <= 3), BCCH_Config__modificationPeriodCoeff__F1 (BCCH_Config__modificationPeriodCoeff__F2 y) = y. enum_solve H y. Qed.

Record BCCH_Config__Type : Set :=
  make__BCCH_Config__Type {
    BCCH_Config__modificationPeriodCoeff : BCCH_Config__modificationPeriodCoeff__Type ;
}.
Definition BCCH_Config__root_list : list seq_elem := (
 Nor BCCH_Config__modificationPeriodCoeff__Type BCCH_Config__modificationPeriodCoeff__cond ::
 nil).
Definition BCCH_Config__ext_list : list typ := (
  nil).
Definition BCCH_Config__cond (z : BCCH_Config__Type) := 
(  BCCH_Config__modificationPeriodCoeff__cond (BCCH_Config__modificationPeriodCoeff z) /\
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
Definition BCCH_Config__modificationPeriodCoeff__Format : T_Format BCCH_Config__modificationPeriodCoeff__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BCCH_Config__modificationPeriodCoeff__nat__Format BCCH_Config__modificationPeriodCoeff__F1 BCCH_Config__modificationPeriodCoeff__F2 BCCH_Config__modificationPeriodCoeff__F1F2 BCCH_Config__modificationPeriodCoeff__F2F1.

Opaque BCCH_Config__modificationPeriodCoeff__cond BCCH_Config__modificationPeriodCoeff__Format.


Definition BCCH_Config__root_Format_Type := Eval cbn in seq_format_prod BCCH_Config__root_list.
Definition BCCH_Config__root_Format_list : BCCH_Config__root_Format_Type :=
  (BCCH_Config__modificationPeriodCoeff__Format, unit_format).

Definition BCCH_Config__ext_Format_Type := Eval cbn in get_formats BCCH_Config__ext_list.
Definition BCCH_Config__ext_Format_list : BCCH_Config__ext_Format_Type :=
  unit__Format.

Definition BCCH_Config__list_type : Set := (seq_type BCCH_Config__root_list) * (seq_ext_type BCCH_Config__ext_list).
Definition BCCH_Config__list_cond (z : BCCH_Config__list_type) : Prop :=
        (seq_cond BCCH_Config__root_list (fst z)) /\ (seq_ext_cond BCCH_Config__ext_list (snd z)).
Definition BCCH_Config__list_format : T_Format BCCH_Config__list_type BCCH_Config__list_cond :=
 (* Eval compute in *) seq_ext_format BCCH_Config__root_list BCCH_Config__root_Format_list BCCH_Config__ext_list BCCH_Config__ext_Format_list.

Opaque BCCH_Config__list_format.
Definition BCCH_Config__F1 (z : BCCH_Config__Type) : BCCH_Config__list_type :=
  (((BCCH_Config__modificationPeriodCoeff z, tt)), (
tt)).
Definition BCCH_Config__F2 (y : BCCH_Config__list_type) : BCCH_Config__Type :=
  match y with
  | ((j0, _), _)=>
    make__BCCH_Config__Type j0
  end.
Definition BCCH_Config__helper1 : (forall a : BCCH_Config__Type, BCCH_Config__cond a -> BCCH_Config__list_cond (BCCH_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BCCH_Config__helper2 : (forall a : BCCH_Config__Type, BCCH_Config__F2 (BCCH_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BCCH_Config__helper3 : (forall b : BCCH_Config__list_type, BCCH_Config__list_cond b -> BCCH_Config__cond (BCCH_Config__F2 b) /\ BCCH_Config__F1 (BCCH_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BCCH_Config__cond, BCCH_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BCCH_Config__Format : T_Format BCCH_Config__Type BCCH_Config__cond :=
 proj2_format BCCH_Config__cond BCCH_Config__list_format  BCCH_Config__F1 BCCH_Config__F2 BCCH_Config__helper1 BCCH_Config__helper2 BCCH_Config__helper3.

Opaque BCCH_Config__cond BCCH_Config__Format.

