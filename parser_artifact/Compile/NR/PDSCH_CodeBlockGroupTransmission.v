Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type : Set :=
 | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2
 | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n4
 | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n6
 | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n8
.
Definition PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond := (fun (_ : PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type) => True).
Lemma PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__helper.

Definition PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 t :=
  match t with
  | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2 => 0
  | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n4 => 1
  | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n6 => 2
  | PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n8 => 3
  end.
Definition PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 n :=
  match n with
  | 0 => PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2
  | 1 => PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n4
  | 2 => PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n6
  | 3 => PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n8
  | _ => PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__n2
  end.
Lemma PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1F2 : forall x : PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type, (PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 x <= 3) /\ PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 (PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2F1 : forall (y : nat) (H : y <= 3), PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 (PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_CodeBlockGroupTransmission__Type : Set :=
  make__PDSCH_CodeBlockGroupTransmission__Type {
    PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock : PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type ;
    PDSCH_CodeBlockGroupTransmission__codeBlockGroupFlushIndicator : bool ;
}.
Definition PDSCH_CodeBlockGroupTransmission__root_list : list seq_elem := (
 Nor PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition PDSCH_CodeBlockGroupTransmission__ext_list : list typ := (
  nil).
Definition PDSCH_CodeBlockGroupTransmission__cond (z : PDSCH_CodeBlockGroupTransmission__Type) := 
(  PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond (PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock z) /\
  (fun _ => True) (PDSCH_CodeBlockGroupTransmission__codeBlockGroupFlushIndicator z) /\
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
Definition PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Format : T_Format PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__nat__Format PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1 PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2 PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F1F2 PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__F2F1.

Opaque PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__cond PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Format.


Definition PDSCH_CodeBlockGroupTransmission__root_Format_Type := Eval cbn in seq_format_prod PDSCH_CodeBlockGroupTransmission__root_list.
Definition PDSCH_CodeBlockGroupTransmission__root_Format_list : PDSCH_CodeBlockGroupTransmission__root_Format_Type :=
  (PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock__Format, (bool__Format, unit_format)).

Definition PDSCH_CodeBlockGroupTransmission__ext_Format_Type := Eval cbn in get_formats PDSCH_CodeBlockGroupTransmission__ext_list.
Definition PDSCH_CodeBlockGroupTransmission__ext_Format_list : PDSCH_CodeBlockGroupTransmission__ext_Format_Type :=
  unit__Format.

Definition PDSCH_CodeBlockGroupTransmission__list_type : Set := (seq_type PDSCH_CodeBlockGroupTransmission__root_list) * (seq_ext_type PDSCH_CodeBlockGroupTransmission__ext_list).
Definition PDSCH_CodeBlockGroupTransmission__list_cond (z : PDSCH_CodeBlockGroupTransmission__list_type) : Prop :=
        (seq_cond PDSCH_CodeBlockGroupTransmission__root_list (fst z)) /\ (seq_ext_cond PDSCH_CodeBlockGroupTransmission__ext_list (snd z)).
Definition PDSCH_CodeBlockGroupTransmission__list_format : T_Format PDSCH_CodeBlockGroupTransmission__list_type PDSCH_CodeBlockGroupTransmission__list_cond :=
 (* Eval compute in *) seq_ext_format PDSCH_CodeBlockGroupTransmission__root_list PDSCH_CodeBlockGroupTransmission__root_Format_list PDSCH_CodeBlockGroupTransmission__ext_list PDSCH_CodeBlockGroupTransmission__ext_Format_list.

Opaque PDSCH_CodeBlockGroupTransmission__list_format.
Definition PDSCH_CodeBlockGroupTransmission__F1 (z : PDSCH_CodeBlockGroupTransmission__Type) : PDSCH_CodeBlockGroupTransmission__list_type :=
  (((PDSCH_CodeBlockGroupTransmission__maxCodeBlockGroupsPerTransportBlock z, (PDSCH_CodeBlockGroupTransmission__codeBlockGroupFlushIndicator z, tt))), (
tt)).
Definition PDSCH_CodeBlockGroupTransmission__F2 (y : PDSCH_CodeBlockGroupTransmission__list_type) : PDSCH_CodeBlockGroupTransmission__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__PDSCH_CodeBlockGroupTransmission__Type j0 j1
  end.
Definition PDSCH_CodeBlockGroupTransmission__helper1 : (forall a : PDSCH_CodeBlockGroupTransmission__Type, PDSCH_CodeBlockGroupTransmission__cond a -> PDSCH_CodeBlockGroupTransmission__list_cond (PDSCH_CodeBlockGroupTransmission__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDSCH_CodeBlockGroupTransmission__helper2 : (forall a : PDSCH_CodeBlockGroupTransmission__Type, PDSCH_CodeBlockGroupTransmission__F2 (PDSCH_CodeBlockGroupTransmission__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDSCH_CodeBlockGroupTransmission__helper3 : (forall b : PDSCH_CodeBlockGroupTransmission__list_type, PDSCH_CodeBlockGroupTransmission__list_cond b -> PDSCH_CodeBlockGroupTransmission__cond (PDSCH_CodeBlockGroupTransmission__F2 b) /\ PDSCH_CodeBlockGroupTransmission__F1 (PDSCH_CodeBlockGroupTransmission__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDSCH_CodeBlockGroupTransmission__cond, PDSCH_CodeBlockGroupTransmission__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDSCH_CodeBlockGroupTransmission__Format : T_Format PDSCH_CodeBlockGroupTransmission__Type PDSCH_CodeBlockGroupTransmission__cond :=
 proj2_format PDSCH_CodeBlockGroupTransmission__cond PDSCH_CodeBlockGroupTransmission__list_format  PDSCH_CodeBlockGroupTransmission__F1 PDSCH_CodeBlockGroupTransmission__F2 PDSCH_CodeBlockGroupTransmission__helper1 PDSCH_CodeBlockGroupTransmission__helper2 PDSCH_CodeBlockGroupTransmission__helper3.

Opaque PDSCH_CodeBlockGroupTransmission__cond PDSCH_CodeBlockGroupTransmission__Format.

