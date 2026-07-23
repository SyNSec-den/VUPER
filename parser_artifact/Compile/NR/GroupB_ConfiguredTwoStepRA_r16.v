Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Type : Set :=
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b56
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b144
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b208
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b256
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b282
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b480
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b640
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b800
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b1000
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b72
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare6
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare5
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare4
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare3
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare2
 | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare1
.
Definition GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__cond := (fun (_ : GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Type) => True).
Lemma GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__nat__helper.

Definition GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1 t :=
  match t with
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b56 => 0
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b144 => 1
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b208 => 2
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b256 => 3
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b282 => 4
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b480 => 5
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b640 => 6
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b800 => 7
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b1000 => 8
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b72 => 9
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare6 => 10
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare5 => 11
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare4 => 12
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare3 => 13
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare2 => 14
  | GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare1 => 15
  end.
Definition GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F2 n :=
  match n with
  | 0 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b56
  | 1 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b144
  | 2 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b208
  | 3 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b256
  | 4 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b282
  | 5 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b480
  | 6 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b640
  | 7 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b800
  | 8 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b1000
  | 9 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b72
  | 10 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare6
  | 11 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare5
  | 12 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare4
  | 13 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare3
  | 14 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare2
  | 15 => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__spare1
  | _ => GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__b56
  end.
Lemma GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1F2 : forall x : GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Type, (GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1 x <= 15) /\ GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F2 (GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1 x) = x. imp_solve. Qed.
Lemma GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F2F1 : forall (y : nat) (H : y <= 15), GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1 (GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F2 y) = y. enum_solve H y. Qed.

Inductive GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Type : Set :=
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__minusinfinity
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB0
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB5
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB8
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB10
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB12
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB15
 | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB18
.
Definition GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__cond := (fun (_ : GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Type) => True).
Lemma GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__nat__helper.

Definition GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1 t :=
  match t with
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__minusinfinity => 0
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB0 => 1
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB5 => 2
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB8 => 3
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB10 => 4
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB12 => 5
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB15 => 6
  | GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB18 => 7
  end.
Definition GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F2 n :=
  match n with
  | 0 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__minusinfinity
  | 1 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB0
  | 2 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB5
  | 3 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB8
  | 4 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB10
  | 5 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB12
  | 6 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB15
  | 7 => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__dB18
  | _ => GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__minusinfinity
  end.
Lemma GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1F2 : forall x : GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Type, (GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1 x <= 7) /\ GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F2 (GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1 x) = x. imp_solve. Qed.
Lemma GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F2F1 : forall (y : nat) (H : y <= 7), GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1 (GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F2 y) = y. enum_solve H y. Qed.

Lemma GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__Type := Z.
Definition GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__cond := (fun z => (1 <= z <= 64)%Z).
Record GroupB_ConfiguredTwoStepRA_r16__Type : Set :=
  make__GroupB_ConfiguredTwoStepRA_r16__Type {
    GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA : GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Type ;
    GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB : GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Type ;
    GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA : Z ;
}.
Definition GroupB_ConfiguredTwoStepRA_r16__list := (
 Nor GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Type GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__cond ::
 Nor GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Type GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__cond ::
 Nor Z GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__cond ::
 nil).
Definition GroupB_ConfiguredTwoStepRA_r16__cond z := 
  GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__cond (GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA z) /\
  GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__cond (GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB z) /\
  GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__cond (GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA z) /\
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
Definition GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Format : T_Format GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__nat__Format GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1 GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F2 GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F1F2 GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__F2F1.

Opaque GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__cond GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Format.

Definition GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Format : T_Format GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__nat__Format GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1 GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F2 GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F1F2 GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__F2F1.

Opaque GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__cond GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Format.

Definition GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__Format : T_Format Z GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__cond :=
 ranged_int_format (1) (64) GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__helper1 GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__helper2.

Opaque GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__cond GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__Format.


Definition GroupB_ConfiguredTwoStepRA_r16__Format_Type := Eval cbn in seq_format_prod GroupB_ConfiguredTwoStepRA_r16__list.
Definition GroupB_ConfiguredTwoStepRA_r16__Format_list : GroupB_ConfiguredTwoStepRA_r16__Format_Type :=
  (GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA__Format, (GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB__Format, (GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA__Format, unit_format))).
Definition GroupB_ConfiguredTwoStepRA_r16__list__Format := (*Eval compute in *) seq_format GroupB_ConfiguredTwoStepRA_r16__list GroupB_ConfiguredTwoStepRA_r16__Format_list.
Definition GroupB_ConfiguredTwoStepRA_r16__F1 z :=
  (GroupB_ConfiguredTwoStepRA_r16__ra_MsgA_SizeGroupA z, (GroupB_ConfiguredTwoStepRA_r16__messagePowerOffsetGroupB z, (GroupB_ConfiguredTwoStepRA_r16__numberOfRA_PreamblesGroupA z, tt))).
Definition GroupB_ConfiguredTwoStepRA_r16__F2 (y : seq_type GroupB_ConfiguredTwoStepRA_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__GroupB_ConfiguredTwoStepRA_r16__Type i0 i1 i2
  end.
Lemma GroupB_ConfiguredTwoStepRA_r16__F1F2_cond (z : GroupB_ConfiguredTwoStepRA_r16__Type)
  : GroupB_ConfiguredTwoStepRA_r16__cond z ->
  (seq_cond GroupB_ConfiguredTwoStepRA_r16__list (GroupB_ConfiguredTwoStepRA_r16__F1 z)).
intro H. unfold GroupB_ConfiguredTwoStepRA_r16__cond in H. simpl. auto. Qed.
Lemma GroupB_ConfiguredTwoStepRA_r16__F1F2_cond2 (z : GroupB_ConfiguredTwoStepRA_r16__Type)
 : GroupB_ConfiguredTwoStepRA_r16__F2 (GroupB_ConfiguredTwoStepRA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma GroupB_ConfiguredTwoStepRA_r16__F2F1_cond (y : seq_type GroupB_ConfiguredTwoStepRA_r16__list)
  : seq_cond GroupB_ConfiguredTwoStepRA_r16__list y ->
 (GroupB_ConfiguredTwoStepRA_r16__cond (GroupB_ConfiguredTwoStepRA_r16__F2 y)) /\  GroupB_ConfiguredTwoStepRA_r16__F1 (GroupB_ConfiguredTwoStepRA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold GroupB_ConfiguredTwoStepRA_r16__cond. simpl in *. auto.
 - simpl. unfold GroupB_ConfiguredTwoStepRA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition GroupB_ConfiguredTwoStepRA_r16__Format : T_Format GroupB_ConfiguredTwoStepRA_r16__Type GroupB_ConfiguredTwoStepRA_r16__cond :=
        proj2_format  GroupB_ConfiguredTwoStepRA_r16__cond GroupB_ConfiguredTwoStepRA_r16__list__Format
    GroupB_ConfiguredTwoStepRA_r16__F1 GroupB_ConfiguredTwoStepRA_r16__F2 GroupB_ConfiguredTwoStepRA_r16__F1F2_cond  GroupB_ConfiguredTwoStepRA_r16__F1F2_cond2 GroupB_ConfiguredTwoStepRA_r16__F2F1_cond.
Opaque GroupB_ConfiguredTwoStepRA_r16__cond GroupB_ConfiguredTwoStepRA_r16__Format.

