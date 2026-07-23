Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SSB_PositionQCL_Relation_r16__Type : Set :=
 | SSB_PositionQCL_Relation_r16__n1
 | SSB_PositionQCL_Relation_r16__n2
 | SSB_PositionQCL_Relation_r16__n4
 | SSB_PositionQCL_Relation_r16__n8
.
Definition SSB_PositionQCL_Relation_r16__cond := (fun (_ : SSB_PositionQCL_Relation_r16__Type) => True).
Lemma SSB_PositionQCL_Relation_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SSB_PositionQCL_Relation_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SSB_PositionQCL_Relation_r16__nat__helper.

Definition SSB_PositionQCL_Relation_r16__F1 t :=
  match t with
  | SSB_PositionQCL_Relation_r16__n1 => 0
  | SSB_PositionQCL_Relation_r16__n2 => 1
  | SSB_PositionQCL_Relation_r16__n4 => 2
  | SSB_PositionQCL_Relation_r16__n8 => 3
  end.
Definition SSB_PositionQCL_Relation_r16__F2 n :=
  match n with
  | 0 => SSB_PositionQCL_Relation_r16__n1
  | 1 => SSB_PositionQCL_Relation_r16__n2
  | 2 => SSB_PositionQCL_Relation_r16__n4
  | 3 => SSB_PositionQCL_Relation_r16__n8
  | _ => SSB_PositionQCL_Relation_r16__n1
  end.
Lemma SSB_PositionQCL_Relation_r16__F1F2 : forall x : SSB_PositionQCL_Relation_r16__Type, (SSB_PositionQCL_Relation_r16__F1 x <= 3) /\ SSB_PositionQCL_Relation_r16__F2 (SSB_PositionQCL_Relation_r16__F1 x) = x. imp_solve. Qed.
Lemma SSB_PositionQCL_Relation_r16__F2F1 : forall (y : nat) (H : y <= 3), SSB_PositionQCL_Relation_r16__F1 (SSB_PositionQCL_Relation_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition SSB_PositionQCL_Relation_r16__Format : T_Format SSB_PositionQCL_Relation_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SSB_PositionQCL_Relation_r16__nat__Format SSB_PositionQCL_Relation_r16__F1 SSB_PositionQCL_Relation_r16__F2 SSB_PositionQCL_Relation_r16__F1F2 SSB_PositionQCL_Relation_r16__F2F1.

Opaque SSB_PositionQCL_Relation_r16__cond SSB_PositionQCL_Relation_r16__Format.

