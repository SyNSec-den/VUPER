Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PDSCH_TimeDomainResourceAllocation__k0__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma PDSCH_TimeDomainResourceAllocation__k0__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_TimeDomainResourceAllocation__k0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_TimeDomainResourceAllocation__k0__Type := Z.
Definition PDSCH_TimeDomainResourceAllocation__k0__cond := (fun z => (0 <= z <= 32)%Z).
Inductive PDSCH_TimeDomainResourceAllocation__mappingType__Type : Set :=
 | PDSCH_TimeDomainResourceAllocation__mappingType__typeA
 | PDSCH_TimeDomainResourceAllocation__mappingType__typeB
.
Definition PDSCH_TimeDomainResourceAllocation__mappingType__cond := (fun (_ : PDSCH_TimeDomainResourceAllocation__mappingType__Type) => True).
Lemma PDSCH_TimeDomainResourceAllocation__mappingType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_TimeDomainResourceAllocation__mappingType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_TimeDomainResourceAllocation__mappingType__nat__helper.

Definition PDSCH_TimeDomainResourceAllocation__mappingType__F1 t :=
  match t with
  | PDSCH_TimeDomainResourceAllocation__mappingType__typeA => 0
  | PDSCH_TimeDomainResourceAllocation__mappingType__typeB => 1
  end.
Definition PDSCH_TimeDomainResourceAllocation__mappingType__F2 n :=
  match n with
  | 0 => PDSCH_TimeDomainResourceAllocation__mappingType__typeA
  | 1 => PDSCH_TimeDomainResourceAllocation__mappingType__typeB
  | _ => PDSCH_TimeDomainResourceAllocation__mappingType__typeA
  end.
Lemma PDSCH_TimeDomainResourceAllocation__mappingType__F1F2 : forall x : PDSCH_TimeDomainResourceAllocation__mappingType__Type, (PDSCH_TimeDomainResourceAllocation__mappingType__F1 x <= 1) /\ PDSCH_TimeDomainResourceAllocation__mappingType__F2 (PDSCH_TimeDomainResourceAllocation__mappingType__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_TimeDomainResourceAllocation__mappingType__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_TimeDomainResourceAllocation__mappingType__F1 (PDSCH_TimeDomainResourceAllocation__mappingType__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__Type := Z.
Definition PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond := (fun z => (0 <= z <= 127)%Z).
Record PDSCH_TimeDomainResourceAllocation__Type : Set :=
  make__PDSCH_TimeDomainResourceAllocation__Type {
    PDSCH_TimeDomainResourceAllocation__k0 : option Z ;
    PDSCH_TimeDomainResourceAllocation__mappingType : PDSCH_TimeDomainResourceAllocation__mappingType__Type ;
    PDSCH_TimeDomainResourceAllocation__startSymbolAndLength : Z ;
}.
Definition PDSCH_TimeDomainResourceAllocation__list := (
 Opt Z PDSCH_TimeDomainResourceAllocation__k0__cond ::
 Nor PDSCH_TimeDomainResourceAllocation__mappingType__Type PDSCH_TimeDomainResourceAllocation__mappingType__cond ::
 Nor Z PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond ::
 nil).
Definition PDSCH_TimeDomainResourceAllocation__cond z := 
  opt_cond PDSCH_TimeDomainResourceAllocation__k0__cond (PDSCH_TimeDomainResourceAllocation__k0 z) /\
  PDSCH_TimeDomainResourceAllocation__mappingType__cond (PDSCH_TimeDomainResourceAllocation__mappingType z) /\
  PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond (PDSCH_TimeDomainResourceAllocation__startSymbolAndLength z) /\
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
Definition PDSCH_TimeDomainResourceAllocation__k0__Format : T_Format Z PDSCH_TimeDomainResourceAllocation__k0__cond :=
 ranged_int_format (0) (32) PDSCH_TimeDomainResourceAllocation__k0__helper1 PDSCH_TimeDomainResourceAllocation__k0__helper2.

Opaque PDSCH_TimeDomainResourceAllocation__k0__cond PDSCH_TimeDomainResourceAllocation__k0__Format.

Definition PDSCH_TimeDomainResourceAllocation__mappingType__Format : T_Format PDSCH_TimeDomainResourceAllocation__mappingType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_TimeDomainResourceAllocation__mappingType__nat__Format PDSCH_TimeDomainResourceAllocation__mappingType__F1 PDSCH_TimeDomainResourceAllocation__mappingType__F2 PDSCH_TimeDomainResourceAllocation__mappingType__F1F2 PDSCH_TimeDomainResourceAllocation__mappingType__F2F1.

Opaque PDSCH_TimeDomainResourceAllocation__mappingType__cond PDSCH_TimeDomainResourceAllocation__mappingType__Format.

Definition PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__Format : T_Format Z PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond :=
 ranged_int_format (0) (127) PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper1 PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__helper2.

Opaque PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__cond PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__Format.


Definition PDSCH_TimeDomainResourceAllocation__Format_Type := Eval cbn in seq_format_prod PDSCH_TimeDomainResourceAllocation__list.
Definition PDSCH_TimeDomainResourceAllocation__Format_list : PDSCH_TimeDomainResourceAllocation__Format_Type :=
  (PDSCH_TimeDomainResourceAllocation__k0__Format, (PDSCH_TimeDomainResourceAllocation__mappingType__Format, (PDSCH_TimeDomainResourceAllocation__startSymbolAndLength__Format, unit_format))).
Definition PDSCH_TimeDomainResourceAllocation__list__Format := (*Eval compute in *) seq_format PDSCH_TimeDomainResourceAllocation__list PDSCH_TimeDomainResourceAllocation__Format_list.
Definition PDSCH_TimeDomainResourceAllocation__F1 z :=
  (PDSCH_TimeDomainResourceAllocation__k0 z, (PDSCH_TimeDomainResourceAllocation__mappingType z, (PDSCH_TimeDomainResourceAllocation__startSymbolAndLength z, tt))).
Definition PDSCH_TimeDomainResourceAllocation__F2 (y : seq_type PDSCH_TimeDomainResourceAllocation__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDSCH_TimeDomainResourceAllocation__Type i0 i1 i2
  end.
Lemma PDSCH_TimeDomainResourceAllocation__F1F2_cond (z : PDSCH_TimeDomainResourceAllocation__Type)
  : PDSCH_TimeDomainResourceAllocation__cond z ->
  (seq_cond PDSCH_TimeDomainResourceAllocation__list (PDSCH_TimeDomainResourceAllocation__F1 z)).
intro H. unfold PDSCH_TimeDomainResourceAllocation__cond in H. simpl. auto. Qed.
Lemma PDSCH_TimeDomainResourceAllocation__F1F2_cond2 (z : PDSCH_TimeDomainResourceAllocation__Type)
 : PDSCH_TimeDomainResourceAllocation__F2 (PDSCH_TimeDomainResourceAllocation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_TimeDomainResourceAllocation__F2F1_cond (y : seq_type PDSCH_TimeDomainResourceAllocation__list)
  : seq_cond PDSCH_TimeDomainResourceAllocation__list y ->
 (PDSCH_TimeDomainResourceAllocation__cond (PDSCH_TimeDomainResourceAllocation__F2 y)) /\  PDSCH_TimeDomainResourceAllocation__F1 (PDSCH_TimeDomainResourceAllocation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_TimeDomainResourceAllocation__cond. simpl in *. auto.
 - simpl. unfold PDSCH_TimeDomainResourceAllocation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_TimeDomainResourceAllocation__Format : T_Format PDSCH_TimeDomainResourceAllocation__Type PDSCH_TimeDomainResourceAllocation__cond :=
        proj2_format  PDSCH_TimeDomainResourceAllocation__cond PDSCH_TimeDomainResourceAllocation__list__Format
    PDSCH_TimeDomainResourceAllocation__F1 PDSCH_TimeDomainResourceAllocation__F2 PDSCH_TimeDomainResourceAllocation__F1F2_cond  PDSCH_TimeDomainResourceAllocation__F1F2_cond2 PDSCH_TimeDomainResourceAllocation__F2F1_cond.
Opaque PDSCH_TimeDomainResourceAllocation__cond PDSCH_TimeDomainResourceAllocation__Format.

