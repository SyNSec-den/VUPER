Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type : Set :=
 | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2
 | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n4
 | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n6
 | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n8
.
Definition PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond := (fun (_ : PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type) => True).
Lemma PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__helper.

Definition PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 t :=
  match t with
  | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2 => 0
  | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n4 => 1
  | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n6 => 2
  | PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n8 => 3
  end.
Definition PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 n :=
  match n with
  | 0 => PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2
  | 1 => PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n4
  | 2 => PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n6
  | 3 => PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n8
  | _ => PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2
  end.
Lemma PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1F2 : forall x : PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type, (PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 x <= 3) /\ PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 (PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2F1 : forall (y : nat) (H : y <= 3), PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 (PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 y) = y. enum_solve H y. Qed.

Record PUSCH_CodeBlockGroupTransmission__Type : Set :=
  make__PUSCH_CodeBlockGroupTransmission__Type {
    PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock : PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type ;
}.
Definition PUSCH_CodeBlockGroupTransmission__root_list : list seq_elem := (
 Nor PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond ::
 nil).
Definition PUSCH_CodeBlockGroupTransmission__ext_list : list typ := (
  nil).
Definition PUSCH_CodeBlockGroupTransmission__cond (z : PUSCH_CodeBlockGroupTransmission__Type) := 
(  PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond (PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock z) /\
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
Definition PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Format : T_Format PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__Format PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1F2 PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2F1.

Opaque PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Format.


Definition PUSCH_CodeBlockGroupTransmission__root_Format_Type := Eval cbn in seq_format_prod PUSCH_CodeBlockGroupTransmission__root_list.
Definition PUSCH_CodeBlockGroupTransmission__root_Format_list : PUSCH_CodeBlockGroupTransmission__root_Format_Type :=
  (PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Format, unit_format).

Definition PUSCH_CodeBlockGroupTransmission__ext_Format_Type := Eval cbn in get_formats PUSCH_CodeBlockGroupTransmission__ext_list.
Definition PUSCH_CodeBlockGroupTransmission__ext_Format_list : PUSCH_CodeBlockGroupTransmission__ext_Format_Type :=
  unit__Format.

Definition PUSCH_CodeBlockGroupTransmission__list_type : Set := (seq_type PUSCH_CodeBlockGroupTransmission__root_list) * (seq_ext_type PUSCH_CodeBlockGroupTransmission__ext_list).
Definition PUSCH_CodeBlockGroupTransmission__list_cond (z : PUSCH_CodeBlockGroupTransmission__list_type) : Prop :=
        (seq_cond PUSCH_CodeBlockGroupTransmission__root_list (fst z)) /\ (seq_ext_cond PUSCH_CodeBlockGroupTransmission__ext_list (snd z)).
Definition PUSCH_CodeBlockGroupTransmission__list_format : T_Format PUSCH_CodeBlockGroupTransmission__list_type PUSCH_CodeBlockGroupTransmission__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_CodeBlockGroupTransmission__root_list PUSCH_CodeBlockGroupTransmission__root_Format_list PUSCH_CodeBlockGroupTransmission__ext_list PUSCH_CodeBlockGroupTransmission__ext_Format_list.

Opaque PUSCH_CodeBlockGroupTransmission__list_format.
Definition PUSCH_CodeBlockGroupTransmission__F1 (z : PUSCH_CodeBlockGroupTransmission__Type) : PUSCH_CodeBlockGroupTransmission__list_type :=
  (((PUSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock z, tt)), (
tt)).
Definition PUSCH_CodeBlockGroupTransmission__F2 (y : PUSCH_CodeBlockGroupTransmission__list_type) : PUSCH_CodeBlockGroupTransmission__Type :=
  match y with
  | ((j0, _), _)=>
    make__PUSCH_CodeBlockGroupTransmission__Type j0
  end.
Definition PUSCH_CodeBlockGroupTransmission__helper1 : (forall a : PUSCH_CodeBlockGroupTransmission__Type, PUSCH_CodeBlockGroupTransmission__cond a -> PUSCH_CodeBlockGroupTransmission__list_cond (PUSCH_CodeBlockGroupTransmission__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_CodeBlockGroupTransmission__helper2 : (forall a : PUSCH_CodeBlockGroupTransmission__Type, PUSCH_CodeBlockGroupTransmission__F2 (PUSCH_CodeBlockGroupTransmission__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_CodeBlockGroupTransmission__helper3 : (forall b : PUSCH_CodeBlockGroupTransmission__list_type, PUSCH_CodeBlockGroupTransmission__list_cond b -> PUSCH_CodeBlockGroupTransmission__cond (PUSCH_CodeBlockGroupTransmission__F2 b) /\ PUSCH_CodeBlockGroupTransmission__F1 (PUSCH_CodeBlockGroupTransmission__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_CodeBlockGroupTransmission__cond, PUSCH_CodeBlockGroupTransmission__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_CodeBlockGroupTransmission__Format : T_Format PUSCH_CodeBlockGroupTransmission__Type PUSCH_CodeBlockGroupTransmission__cond :=
 proj2_format PUSCH_CodeBlockGroupTransmission__cond PUSCH_CodeBlockGroupTransmission__list_format  PUSCH_CodeBlockGroupTransmission__F1 PUSCH_CodeBlockGroupTransmission__F2 PUSCH_CodeBlockGroupTransmission__helper1 PUSCH_CodeBlockGroupTransmission__helper2 PUSCH_CodeBlockGroupTransmission__helper3.

Opaque PUSCH_CodeBlockGroupTransmission__cond PUSCH_CodeBlockGroupTransmission__Format.

