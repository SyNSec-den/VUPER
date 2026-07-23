Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Type : Set :=
 | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n2
 | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n3
 | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n4
 | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n5
.
Definition MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__cond := (fun (_ : MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Type) => True).
Lemma MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__nat__helper.

Definition MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1 t :=
  match t with
  | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n2 => 0
  | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n3 => 1
  | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n4 => 2
  | MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n5 => 3
  end.
Definition MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F2 n :=
  match n with
  | 0 => MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n2
  | 1 => MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n3
  | 2 => MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n4
  | 3 => MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n5
  | _ => MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__n2
  end.
Lemma MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1F2 : forall x : MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Type, (MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1 x <= 3) /\ MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F2 (MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1 x) = x. imp_solve. Qed.
Lemma MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F2F1 : forall (y : nat) (H : y <= 3), MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1 (MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__helper1 : (1 <= 3)%Z.  lia. Qed.
Lemma MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__Type := Z.
Definition MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__cond := (fun z => (1 <= z <= 3)%Z).
Inductive MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Type : Set :=
 | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n1
 | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n2
 | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n3
 | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n4
 | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n7
.
Definition MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__cond := (fun (_ : MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Type) => True).
Lemma MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__nat__helper.

Definition MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1 t :=
  match t with
  | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n1 => 0
  | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n2 => 1
  | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n3 => 2
  | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n4 => 3
  | MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n7 => 4
  end.
Definition MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F2 n :=
  match n with
  | 0 => MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n1
  | 1 => MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n2
  | 2 => MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n3
  | 3 => MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n4
  | 4 => MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n7
  | _ => MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__n1
  end.
Lemma MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1F2 : forall x : MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Type, (MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1 x <= 4) /\ MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F2 (MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1 x) = x. imp_solve. Qed.
Lemma MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F2F1 : forall (y : nat) (H : y <= 4), MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1 (MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F2 y) = y. enum_solve H y. Qed.

Record MultiDCI_MultiTRP_r16__Type : Set :=
  make__MultiDCI_MultiTRP_r16__Type {
    MultiDCI_MultiTRP_r16__maxNumberCORESET_r16 : MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Type ;
    MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16 : Z ;
    MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16 : MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Type ;
}.
Definition MultiDCI_MultiTRP_r16__list := (
 Nor MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Type MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__cond ::
 Nor Z MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__cond ::
 Nor MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Type MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__cond ::
 nil).
Definition MultiDCI_MultiTRP_r16__cond z := 
  MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__cond (MultiDCI_MultiTRP_r16__maxNumberCORESET_r16 z) /\
  MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__cond (MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16 z) /\
  MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__cond (MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16 z) /\
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
Definition MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Format : T_Format MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__nat__Format MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1 MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F2 MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F1F2 MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__F2F1.

Opaque MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__cond MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Format.

Definition MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__Format : T_Format Z MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__cond :=
 ranged_int_format (1) (3) MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__helper1 MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__helper2.

Opaque MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__cond MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__Format.

Definition MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Format : T_Format MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__nat__Format MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1 MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F2 MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F1F2 MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__F2F1.

Opaque MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__cond MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Format.


Definition MultiDCI_MultiTRP_r16__Format_Type := Eval cbn in seq_format_prod MultiDCI_MultiTRP_r16__list.
Definition MultiDCI_MultiTRP_r16__Format_list : MultiDCI_MultiTRP_r16__Format_Type :=
  (MultiDCI_MultiTRP_r16__maxNumberCORESET_r16__Format, (MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16__Format, (MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16__Format, unit_format))).
Definition MultiDCI_MultiTRP_r16__list__Format := (*Eval compute in *) seq_format MultiDCI_MultiTRP_r16__list MultiDCI_MultiTRP_r16__Format_list.
Definition MultiDCI_MultiTRP_r16__F1 z :=
  (MultiDCI_MultiTRP_r16__maxNumberCORESET_r16 z, (MultiDCI_MultiTRP_r16__maxNumberCORESETPerPoolIndex_r16 z, (MultiDCI_MultiTRP_r16__maxNumberUnicastPDSCH_PerPool_r16 z, tt))).
Definition MultiDCI_MultiTRP_r16__F2 (y : seq_type MultiDCI_MultiTRP_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MultiDCI_MultiTRP_r16__Type i0 i1 i2
  end.
Lemma MultiDCI_MultiTRP_r16__F1F2_cond (z : MultiDCI_MultiTRP_r16__Type)
  : MultiDCI_MultiTRP_r16__cond z ->
  (seq_cond MultiDCI_MultiTRP_r16__list (MultiDCI_MultiTRP_r16__F1 z)).
intro H. unfold MultiDCI_MultiTRP_r16__cond in H. simpl. auto. Qed.
Lemma MultiDCI_MultiTRP_r16__F1F2_cond2 (z : MultiDCI_MultiTRP_r16__Type)
 : MultiDCI_MultiTRP_r16__F2 (MultiDCI_MultiTRP_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MultiDCI_MultiTRP_r16__F2F1_cond (y : seq_type MultiDCI_MultiTRP_r16__list)
  : seq_cond MultiDCI_MultiTRP_r16__list y ->
 (MultiDCI_MultiTRP_r16__cond (MultiDCI_MultiTRP_r16__F2 y)) /\  MultiDCI_MultiTRP_r16__F1 (MultiDCI_MultiTRP_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MultiDCI_MultiTRP_r16__cond. simpl in *. auto.
 - simpl. unfold MultiDCI_MultiTRP_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MultiDCI_MultiTRP_r16__Format : T_Format MultiDCI_MultiTRP_r16__Type MultiDCI_MultiTRP_r16__cond :=
        proj2_format  MultiDCI_MultiTRP_r16__cond MultiDCI_MultiTRP_r16__list__Format
    MultiDCI_MultiTRP_r16__F1 MultiDCI_MultiTRP_r16__F2 MultiDCI_MultiTRP_r16__F1F2_cond  MultiDCI_MultiTRP_r16__F1F2_cond2 MultiDCI_MultiTRP_r16__F2F1_cond.
Opaque MultiDCI_MultiTRP_r16__cond MultiDCI_MultiTRP_r16__Format.

