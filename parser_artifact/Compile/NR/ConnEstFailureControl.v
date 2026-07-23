Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ConnEstFailureControl__connEstFailCount__Type : Set :=
 | ConnEstFailureControl__connEstFailCount__n1
 | ConnEstFailureControl__connEstFailCount__n2
 | ConnEstFailureControl__connEstFailCount__n3
 | ConnEstFailureControl__connEstFailCount__n4
.
Definition ConnEstFailureControl__connEstFailCount__cond := (fun (_ : ConnEstFailureControl__connEstFailCount__Type) => True).
Lemma ConnEstFailureControl__connEstFailCount__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConnEstFailureControl__connEstFailCount__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 ConnEstFailureControl__connEstFailCount__nat__helper.

Definition ConnEstFailureControl__connEstFailCount__F1 t :=
  match t with
  | ConnEstFailureControl__connEstFailCount__n1 => 0
  | ConnEstFailureControl__connEstFailCount__n2 => 1
  | ConnEstFailureControl__connEstFailCount__n3 => 2
  | ConnEstFailureControl__connEstFailCount__n4 => 3
  end.
Definition ConnEstFailureControl__connEstFailCount__F2 n :=
  match n with
  | 0 => ConnEstFailureControl__connEstFailCount__n1
  | 1 => ConnEstFailureControl__connEstFailCount__n2
  | 2 => ConnEstFailureControl__connEstFailCount__n3
  | 3 => ConnEstFailureControl__connEstFailCount__n4
  | _ => ConnEstFailureControl__connEstFailCount__n1
  end.
Lemma ConnEstFailureControl__connEstFailCount__F1F2 : forall x : ConnEstFailureControl__connEstFailCount__Type, (ConnEstFailureControl__connEstFailCount__F1 x <= 3) /\ ConnEstFailureControl__connEstFailCount__F2 (ConnEstFailureControl__connEstFailCount__F1 x) = x. imp_solve. Qed.
Lemma ConnEstFailureControl__connEstFailCount__F2F1 : forall (y : nat) (H : y <= 3), ConnEstFailureControl__connEstFailCount__F1 (ConnEstFailureControl__connEstFailCount__F2 y) = y. enum_solve H y. Qed.

Inductive ConnEstFailureControl__connEstFailOffsetValidity__Type : Set :=
 | ConnEstFailureControl__connEstFailOffsetValidity__s30
 | ConnEstFailureControl__connEstFailOffsetValidity__s60
 | ConnEstFailureControl__connEstFailOffsetValidity__s120
 | ConnEstFailureControl__connEstFailOffsetValidity__s240
 | ConnEstFailureControl__connEstFailOffsetValidity__s300
 | ConnEstFailureControl__connEstFailOffsetValidity__s420
 | ConnEstFailureControl__connEstFailOffsetValidity__s600
 | ConnEstFailureControl__connEstFailOffsetValidity__s900
.
Definition ConnEstFailureControl__connEstFailOffsetValidity__cond := (fun (_ : ConnEstFailureControl__connEstFailOffsetValidity__Type) => True).
Lemma ConnEstFailureControl__connEstFailOffsetValidity__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConnEstFailureControl__connEstFailOffsetValidity__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 ConnEstFailureControl__connEstFailOffsetValidity__nat__helper.

Definition ConnEstFailureControl__connEstFailOffsetValidity__F1 t :=
  match t with
  | ConnEstFailureControl__connEstFailOffsetValidity__s30 => 0
  | ConnEstFailureControl__connEstFailOffsetValidity__s60 => 1
  | ConnEstFailureControl__connEstFailOffsetValidity__s120 => 2
  | ConnEstFailureControl__connEstFailOffsetValidity__s240 => 3
  | ConnEstFailureControl__connEstFailOffsetValidity__s300 => 4
  | ConnEstFailureControl__connEstFailOffsetValidity__s420 => 5
  | ConnEstFailureControl__connEstFailOffsetValidity__s600 => 6
  | ConnEstFailureControl__connEstFailOffsetValidity__s900 => 7
  end.
Definition ConnEstFailureControl__connEstFailOffsetValidity__F2 n :=
  match n with
  | 0 => ConnEstFailureControl__connEstFailOffsetValidity__s30
  | 1 => ConnEstFailureControl__connEstFailOffsetValidity__s60
  | 2 => ConnEstFailureControl__connEstFailOffsetValidity__s120
  | 3 => ConnEstFailureControl__connEstFailOffsetValidity__s240
  | 4 => ConnEstFailureControl__connEstFailOffsetValidity__s300
  | 5 => ConnEstFailureControl__connEstFailOffsetValidity__s420
  | 6 => ConnEstFailureControl__connEstFailOffsetValidity__s600
  | 7 => ConnEstFailureControl__connEstFailOffsetValidity__s900
  | _ => ConnEstFailureControl__connEstFailOffsetValidity__s30
  end.
Lemma ConnEstFailureControl__connEstFailOffsetValidity__F1F2 : forall x : ConnEstFailureControl__connEstFailOffsetValidity__Type, (ConnEstFailureControl__connEstFailOffsetValidity__F1 x <= 7) /\ ConnEstFailureControl__connEstFailOffsetValidity__F2 (ConnEstFailureControl__connEstFailOffsetValidity__F1 x) = x. imp_solve. Qed.
Lemma ConnEstFailureControl__connEstFailOffsetValidity__F2F1 : forall (y : nat) (H : y <= 7), ConnEstFailureControl__connEstFailOffsetValidity__F1 (ConnEstFailureControl__connEstFailOffsetValidity__F2 y) = y. enum_solve H y. Qed.

Lemma ConnEstFailureControl__connEstFailOffset__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ConnEstFailureControl__connEstFailOffset__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConnEstFailureControl__connEstFailOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConnEstFailureControl__connEstFailOffset__Type := Z.
Definition ConnEstFailureControl__connEstFailOffset__cond := (fun z => (0 <= z <= 15)%Z).
Record ConnEstFailureControl__Type : Set :=
  make__ConnEstFailureControl__Type {
    ConnEstFailureControl__connEstFailCount : ConnEstFailureControl__connEstFailCount__Type ;
    ConnEstFailureControl__connEstFailOffsetValidity : ConnEstFailureControl__connEstFailOffsetValidity__Type ;
    ConnEstFailureControl__connEstFailOffset : option Z ;
}.
Definition ConnEstFailureControl__list := (
 Nor ConnEstFailureControl__connEstFailCount__Type ConnEstFailureControl__connEstFailCount__cond ::
 Nor ConnEstFailureControl__connEstFailOffsetValidity__Type ConnEstFailureControl__connEstFailOffsetValidity__cond ::
 Opt Z ConnEstFailureControl__connEstFailOffset__cond ::
 nil).
Definition ConnEstFailureControl__cond z := 
  ConnEstFailureControl__connEstFailCount__cond (ConnEstFailureControl__connEstFailCount z) /\
  ConnEstFailureControl__connEstFailOffsetValidity__cond (ConnEstFailureControl__connEstFailOffsetValidity z) /\
  opt_cond ConnEstFailureControl__connEstFailOffset__cond (ConnEstFailureControl__connEstFailOffset z) /\
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
Definition ConnEstFailureControl__connEstFailCount__Format : T_Format ConnEstFailureControl__connEstFailCount__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConnEstFailureControl__connEstFailCount__nat__Format ConnEstFailureControl__connEstFailCount__F1 ConnEstFailureControl__connEstFailCount__F2 ConnEstFailureControl__connEstFailCount__F1F2 ConnEstFailureControl__connEstFailCount__F2F1.

Opaque ConnEstFailureControl__connEstFailCount__cond ConnEstFailureControl__connEstFailCount__Format.

Definition ConnEstFailureControl__connEstFailOffsetValidity__Format : T_Format ConnEstFailureControl__connEstFailOffsetValidity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConnEstFailureControl__connEstFailOffsetValidity__nat__Format ConnEstFailureControl__connEstFailOffsetValidity__F1 ConnEstFailureControl__connEstFailOffsetValidity__F2 ConnEstFailureControl__connEstFailOffsetValidity__F1F2 ConnEstFailureControl__connEstFailOffsetValidity__F2F1.

Opaque ConnEstFailureControl__connEstFailOffsetValidity__cond ConnEstFailureControl__connEstFailOffsetValidity__Format.

Definition ConnEstFailureControl__connEstFailOffset__Format : T_Format Z ConnEstFailureControl__connEstFailOffset__cond :=
 ranged_int_format (0) (15) ConnEstFailureControl__connEstFailOffset__helper1 ConnEstFailureControl__connEstFailOffset__helper2.

Opaque ConnEstFailureControl__connEstFailOffset__cond ConnEstFailureControl__connEstFailOffset__Format.


Definition ConnEstFailureControl__Format_Type := Eval cbn in seq_format_prod ConnEstFailureControl__list.
Definition ConnEstFailureControl__Format_list : ConnEstFailureControl__Format_Type :=
  (ConnEstFailureControl__connEstFailCount__Format, (ConnEstFailureControl__connEstFailOffsetValidity__Format, (ConnEstFailureControl__connEstFailOffset__Format, unit_format))).
Definition ConnEstFailureControl__list__Format := (*Eval compute in *) seq_format ConnEstFailureControl__list ConnEstFailureControl__Format_list.
Definition ConnEstFailureControl__F1 z :=
  (ConnEstFailureControl__connEstFailCount z, (ConnEstFailureControl__connEstFailOffsetValidity z, (ConnEstFailureControl__connEstFailOffset z, tt))).
Definition ConnEstFailureControl__F2 (y : seq_type ConnEstFailureControl__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConnEstFailureControl__Type i0 i1 i2
  end.
Lemma ConnEstFailureControl__F1F2_cond (z : ConnEstFailureControl__Type)
  : ConnEstFailureControl__cond z ->
  (seq_cond ConnEstFailureControl__list (ConnEstFailureControl__F1 z)).
intro H. unfold ConnEstFailureControl__cond in H. simpl. auto. Qed.
Lemma ConnEstFailureControl__F1F2_cond2 (z : ConnEstFailureControl__Type)
 : ConnEstFailureControl__F2 (ConnEstFailureControl__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConnEstFailureControl__F2F1_cond (y : seq_type ConnEstFailureControl__list)
  : seq_cond ConnEstFailureControl__list y ->
 (ConnEstFailureControl__cond (ConnEstFailureControl__F2 y)) /\  ConnEstFailureControl__F1 (ConnEstFailureControl__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConnEstFailureControl__cond. simpl in *. auto.
 - simpl. unfold ConnEstFailureControl__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConnEstFailureControl__Format : T_Format ConnEstFailureControl__Type ConnEstFailureControl__cond :=
        proj2_format  ConnEstFailureControl__cond ConnEstFailureControl__list__Format
    ConnEstFailureControl__F1 ConnEstFailureControl__F2 ConnEstFailureControl__F1F2_cond  ConnEstFailureControl__F1F2_cond2 ConnEstFailureControl__F2F1_cond.
Opaque ConnEstFailureControl__cond ConnEstFailureControl__Format.

