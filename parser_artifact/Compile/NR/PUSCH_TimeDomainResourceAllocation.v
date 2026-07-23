Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUSCH_TimeDomainResourceAllocation__k2__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma PUSCH_TimeDomainResourceAllocation__k2__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_TimeDomainResourceAllocation__k2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_TimeDomainResourceAllocation__k2__Type := Z.
Definition PUSCH_TimeDomainResourceAllocation__k2__cond := (fun z => (0 <= z <= 32)%Z).
Inductive PUSCH_TimeDomainResourceAllocation__mappingType__Type : Set :=
 | PUSCH_TimeDomainResourceAllocation__mappingType__typeA
 | PUSCH_TimeDomainResourceAllocation__mappingType__typeB
.
Definition PUSCH_TimeDomainResourceAllocation__mappingType__cond := (fun (_ : PUSCH_TimeDomainResourceAllocation__mappingType__Type) => True).
Lemma PUSCH_TimeDomainResourceAllocation__mappingType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_TimeDomainResourceAllocation__mappingType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_TimeDomainResourceAllocation__mappingType__nat__helper.

Definition PUSCH_TimeDomainResourceAllocation__mappingType__F1 t :=
  match t with
  | PUSCH_TimeDomainResourceAllocation__mappingType__typeA => 0
  | PUSCH_TimeDomainResourceAllocation__mappingType__typeB => 1
  end.
Definition PUSCH_TimeDomainResourceAllocation__mappingType__F2 n :=
  match n with
  | 0 => PUSCH_TimeDomainResourceAllocation__mappingType__typeA
  | 1 => PUSCH_TimeDomainResourceAllocation__mappingType__typeB
  | _ => PUSCH_TimeDomainResourceAllocation__mappingType__typeA
  end.
Lemma PUSCH_TimeDomainResourceAllocation__mappingType__F1F2 : forall x : PUSCH_TimeDomainResourceAllocation__mappingType__Type, (PUSCH_TimeDomainResourceAllocation__mappingType__F1 x <= 1) /\ PUSCH_TimeDomainResourceAllocation__mappingType__F2 (PUSCH_TimeDomainResourceAllocation__mappingType__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_TimeDomainResourceAllocation__mappingType__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_TimeDomainResourceAllocation__mappingType__F1 (PUSCH_TimeDomainResourceAllocation__mappingType__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__Type := Z.
Definition PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond := (fun z => (0 <= z <= 127)%Z).
Record PUSCH_TimeDomainResourceAllocation__Type : Set :=
  make__PUSCH_TimeDomainResourceAllocation__Type {
    PUSCH_TimeDomainResourceAllocation__k2 : option Z ;
    PUSCH_TimeDomainResourceAllocation__mappingType : PUSCH_TimeDomainResourceAllocation__mappingType__Type ;
    PUSCH_TimeDomainResourceAllocation__startSymbolAndLength : Z ;
}.
Definition PUSCH_TimeDomainResourceAllocation__list := (
 Opt Z PUSCH_TimeDomainResourceAllocation__k2__cond ::
 Nor PUSCH_TimeDomainResourceAllocation__mappingType__Type PUSCH_TimeDomainResourceAllocation__mappingType__cond ::
 Nor Z PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond ::
 nil).
Definition PUSCH_TimeDomainResourceAllocation__cond z := 
  opt_cond PUSCH_TimeDomainResourceAllocation__k2__cond (PUSCH_TimeDomainResourceAllocation__k2 z) /\
  PUSCH_TimeDomainResourceAllocation__mappingType__cond (PUSCH_TimeDomainResourceAllocation__mappingType z) /\
  PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond (PUSCH_TimeDomainResourceAllocation__startSymbolAndLength z) /\
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
Definition PUSCH_TimeDomainResourceAllocation__k2__Format : T_Format Z PUSCH_TimeDomainResourceAllocation__k2__cond :=
 ranged_int_format (0) (32) PUSCH_TimeDomainResourceAllocation__k2__helper1 PUSCH_TimeDomainResourceAllocation__k2__helper2.

Opaque PUSCH_TimeDomainResourceAllocation__k2__cond PUSCH_TimeDomainResourceAllocation__k2__Format.

Definition PUSCH_TimeDomainResourceAllocation__mappingType__Format : T_Format PUSCH_TimeDomainResourceAllocation__mappingType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_TimeDomainResourceAllocation__mappingType__nat__Format PUSCH_TimeDomainResourceAllocation__mappingType__F1 PUSCH_TimeDomainResourceAllocation__mappingType__F2 PUSCH_TimeDomainResourceAllocation__mappingType__F1F2 PUSCH_TimeDomainResourceAllocation__mappingType__F2F1.

Opaque PUSCH_TimeDomainResourceAllocation__mappingType__cond PUSCH_TimeDomainResourceAllocation__mappingType__Format.

Definition PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__Format : T_Format Z PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond :=
 ranged_int_format (0) (127) PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper1 PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper2.

Opaque PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__Format.


Definition PUSCH_TimeDomainResourceAllocation__Format_Type := Eval cbn in seq_format_prod PUSCH_TimeDomainResourceAllocation__list.
Definition PUSCH_TimeDomainResourceAllocation__Format_list : PUSCH_TimeDomainResourceAllocation__Format_Type :=
  (PUSCH_TimeDomainResourceAllocation__k2__Format, (PUSCH_TimeDomainResourceAllocation__mappingType__Format, (PUSCH_TimeDomainResourceAllocation__startSymbolAndLength__Format, unit_format))).
Definition PUSCH_TimeDomainResourceAllocation__list__Format := (*Eval compute in *) seq_format PUSCH_TimeDomainResourceAllocation__list PUSCH_TimeDomainResourceAllocation__Format_list.
Definition PUSCH_TimeDomainResourceAllocation__F1 z :=
  (PUSCH_TimeDomainResourceAllocation__k2 z, (PUSCH_TimeDomainResourceAllocation__mappingType z, (PUSCH_TimeDomainResourceAllocation__startSymbolAndLength z, tt))).
Definition PUSCH_TimeDomainResourceAllocation__F2 (y : seq_type PUSCH_TimeDomainResourceAllocation__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PUSCH_TimeDomainResourceAllocation__Type i0 i1 i2
  end.
Lemma PUSCH_TimeDomainResourceAllocation__F1F2_cond (z : PUSCH_TimeDomainResourceAllocation__Type)
  : PUSCH_TimeDomainResourceAllocation__cond z ->
  (seq_cond PUSCH_TimeDomainResourceAllocation__list (PUSCH_TimeDomainResourceAllocation__F1 z)).
intro H. unfold PUSCH_TimeDomainResourceAllocation__cond in H. simpl. auto. Qed.
Lemma PUSCH_TimeDomainResourceAllocation__F1F2_cond2 (z : PUSCH_TimeDomainResourceAllocation__Type)
 : PUSCH_TimeDomainResourceAllocation__F2 (PUSCH_TimeDomainResourceAllocation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_TimeDomainResourceAllocation__F2F1_cond (y : seq_type PUSCH_TimeDomainResourceAllocation__list)
  : seq_cond PUSCH_TimeDomainResourceAllocation__list y ->
 (PUSCH_TimeDomainResourceAllocation__cond (PUSCH_TimeDomainResourceAllocation__F2 y)) /\  PUSCH_TimeDomainResourceAllocation__F1 (PUSCH_TimeDomainResourceAllocation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_TimeDomainResourceAllocation__cond. simpl in *. auto.
 - simpl. unfold PUSCH_TimeDomainResourceAllocation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_TimeDomainResourceAllocation__Format : T_Format PUSCH_TimeDomainResourceAllocation__Type PUSCH_TimeDomainResourceAllocation__cond :=
        proj2_format  PUSCH_TimeDomainResourceAllocation__cond PUSCH_TimeDomainResourceAllocation__list__Format
    PUSCH_TimeDomainResourceAllocation__F1 PUSCH_TimeDomainResourceAllocation__F2 PUSCH_TimeDomainResourceAllocation__F1F2_cond  PUSCH_TimeDomainResourceAllocation__F1F2_cond2 PUSCH_TimeDomainResourceAllocation__F2F1_cond.
Opaque PUSCH_TimeDomainResourceAllocation__cond PUSCH_TimeDomainResourceAllocation__Format.

