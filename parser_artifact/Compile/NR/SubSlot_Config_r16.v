Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Type : Set :=
 | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n4
 | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n5
 | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n6
 | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n7
.
Definition SubSlot_Config_r16__sub_SlotConfig_NCP_r16__cond := (fun (_ : SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Type) => True).
Lemma SubSlot_Config_r16__sub_SlotConfig_NCP_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SubSlot_Config_r16__sub_SlotConfig_NCP_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SubSlot_Config_r16__sub_SlotConfig_NCP_r16__nat__helper.

Definition SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1 t :=
  match t with
  | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n4 => 0
  | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n5 => 1
  | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n6 => 2
  | SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n7 => 3
  end.
Definition SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F2 n :=
  match n with
  | 0 => SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n4
  | 1 => SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n5
  | 2 => SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n6
  | 3 => SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n7
  | _ => SubSlot_Config_r16__sub_SlotConfig_NCP_r16__n4
  end.
Lemma SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1F2 : forall x : SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Type, (SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1 x <= 3) /\ SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F2 (SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1 x) = x. imp_solve. Qed.
Lemma SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F2F1 : forall (y : nat) (H : y <= 3), SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1 (SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Type : Set :=
 | SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n4
 | SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n5
 | SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n6
.
Definition SubSlot_Config_r16__sub_SlotConfig_ECP_r16__cond := (fun (_ : SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Type) => True).
Lemma SubSlot_Config_r16__sub_SlotConfig_ECP_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SubSlot_Config_r16__sub_SlotConfig_ECP_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SubSlot_Config_r16__sub_SlotConfig_ECP_r16__nat__helper.

Definition SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1 t :=
  match t with
  | SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n4 => 0
  | SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n5 => 1
  | SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n6 => 2
  end.
Definition SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F2 n :=
  match n with
  | 0 => SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n4
  | 1 => SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n5
  | 2 => SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n6
  | _ => SubSlot_Config_r16__sub_SlotConfig_ECP_r16__n4
  end.
Lemma SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1F2 : forall x : SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Type, (SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1 x <= 2) /\ SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F2 (SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1 x) = x. imp_solve. Qed.
Lemma SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F2F1 : forall (y : nat) (H : y <= 2), SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1 (SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F2 y) = y. enum_solve H y. Qed.

Record SubSlot_Config_r16__Type : Set :=
  make__SubSlot_Config_r16__Type {
    SubSlot_Config_r16__sub_SlotConfig_NCP_r16 : option SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Type ;
    SubSlot_Config_r16__sub_SlotConfig_ECP_r16 : option SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Type ;
}.
Definition SubSlot_Config_r16__list := (
 Opt SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Type SubSlot_Config_r16__sub_SlotConfig_NCP_r16__cond ::
 Opt SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Type SubSlot_Config_r16__sub_SlotConfig_ECP_r16__cond ::
 nil).
Definition SubSlot_Config_r16__cond z := 
  opt_cond SubSlot_Config_r16__sub_SlotConfig_NCP_r16__cond (SubSlot_Config_r16__sub_SlotConfig_NCP_r16 z) /\
  opt_cond SubSlot_Config_r16__sub_SlotConfig_ECP_r16__cond (SubSlot_Config_r16__sub_SlotConfig_ECP_r16 z) /\
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
Definition SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Format : T_Format SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SubSlot_Config_r16__sub_SlotConfig_NCP_r16__nat__Format SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1 SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F2 SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F1F2 SubSlot_Config_r16__sub_SlotConfig_NCP_r16__F2F1.

Opaque SubSlot_Config_r16__sub_SlotConfig_NCP_r16__cond SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Format.

Definition SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Format : T_Format SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SubSlot_Config_r16__sub_SlotConfig_ECP_r16__nat__Format SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1 SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F2 SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F1F2 SubSlot_Config_r16__sub_SlotConfig_ECP_r16__F2F1.

Opaque SubSlot_Config_r16__sub_SlotConfig_ECP_r16__cond SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Format.


Definition SubSlot_Config_r16__Format_Type := Eval cbn in seq_format_prod SubSlot_Config_r16__list.
Definition SubSlot_Config_r16__Format_list : SubSlot_Config_r16__Format_Type :=
  (SubSlot_Config_r16__sub_SlotConfig_NCP_r16__Format, (SubSlot_Config_r16__sub_SlotConfig_ECP_r16__Format, unit_format)).
Definition SubSlot_Config_r16__list__Format := (*Eval compute in *) seq_format SubSlot_Config_r16__list SubSlot_Config_r16__Format_list.
Definition SubSlot_Config_r16__F1 z :=
  (SubSlot_Config_r16__sub_SlotConfig_NCP_r16 z, (SubSlot_Config_r16__sub_SlotConfig_ECP_r16 z, tt)).
Definition SubSlot_Config_r16__F2 (y : seq_type SubSlot_Config_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SubSlot_Config_r16__Type i0 i1
  end.
Lemma SubSlot_Config_r16__F1F2_cond (z : SubSlot_Config_r16__Type)
  : SubSlot_Config_r16__cond z ->
  (seq_cond SubSlot_Config_r16__list (SubSlot_Config_r16__F1 z)).
intro H. unfold SubSlot_Config_r16__cond in H. simpl. auto. Qed.
Lemma SubSlot_Config_r16__F1F2_cond2 (z : SubSlot_Config_r16__Type)
 : SubSlot_Config_r16__F2 (SubSlot_Config_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SubSlot_Config_r16__F2F1_cond (y : seq_type SubSlot_Config_r16__list)
  : seq_cond SubSlot_Config_r16__list y ->
 (SubSlot_Config_r16__cond (SubSlot_Config_r16__F2 y)) /\  SubSlot_Config_r16__F1 (SubSlot_Config_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SubSlot_Config_r16__cond. simpl in *. auto.
 - simpl. unfold SubSlot_Config_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SubSlot_Config_r16__Format : T_Format SubSlot_Config_r16__Type SubSlot_Config_r16__cond :=
        proj2_format  SubSlot_Config_r16__cond SubSlot_Config_r16__list__Format
    SubSlot_Config_r16__F1 SubSlot_Config_r16__F2 SubSlot_Config_r16__F1F2_cond  SubSlot_Config_r16__F1F2_cond2 SubSlot_Config_r16__F2F1_cond.
Opaque SubSlot_Config_r16__cond SubSlot_Config_r16__Format.

