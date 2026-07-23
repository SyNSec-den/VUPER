Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PDSCH_TimeDomainResourceAllocation_r16__k0_r16__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__k0_r16__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_TimeDomainResourceAllocation_r16__k0_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__k0_r16__Type := Z.
Definition PDSCH_TimeDomainResourceAllocation_r16__k0_r16__cond := (fun z => (0 <= z <= 32)%Z).
Inductive PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Type : Set :=
 | PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeA
 | PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeB
.
Definition PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__cond := (fun (_ : PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Type) => True).
Lemma PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__nat__helper.

Definition PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1 t :=
  match t with
  | PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeA => 0
  | PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeB => 1
  end.
Definition PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F2 n :=
  match n with
  | 0 => PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeA
  | 1 => PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeB
  | _ => PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__typeA
  end.
Lemma PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1F2 : forall x : PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Type, (PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1 x <= 1) /\ PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F2 (PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1 (PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__Type := Z.
Definition PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__cond := (fun z => (0 <= z <= 127)%Z).
Inductive PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Type : Set :=
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n2
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n3
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n4
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n5
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n6
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n7
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n8
 | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n16
.
Definition PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__cond := (fun (_ : PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Type) => True).
Lemma PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__nat__helper.

Definition PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1 t :=
  match t with
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n2 => 0
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n3 => 1
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n4 => 2
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n5 => 3
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n6 => 4
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n7 => 5
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n8 => 6
  | PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n16 => 7
  end.
Definition PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F2 n :=
  match n with
  | 0 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n2
  | 1 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n3
  | 2 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n4
  | 3 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n5
  | 4 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n6
  | 5 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n7
  | 6 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n8
  | 7 => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n16
  | _ => PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__n2
  end.
Lemma PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1F2 : forall x : PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Type, (PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1 x <= 7) /\ PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F2 (PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F2F1 : forall (y : nat) (H : y <= 7), PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1 (PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__helper1 : (33 <= 128)%Z.  lia. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__helper2 : to_bit_sz (Z.to_nat (128 - 33)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 33))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__Type := Z.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__cond := (fun z => (33 <= z <= 128)%Z).
Record PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type : Set :=
  make__PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type {
    PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710 : option Z ;
}.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__list := (
 Opt Z PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__cond ::
 nil).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond z := 
  opt_cond PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__cond (PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710 z) /\
  True.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext0__Type := PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0__cond := PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond.

Inductive PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Type : Set :=
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n2
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n3
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n4
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n5
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n6
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n7
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n8
 | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n16
.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__cond := (fun (_ : PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Type) => True).
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__nat__helper.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1 t :=
  match t with
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n2 => 0
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n3 => 1
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n4 => 2
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n5 => 3
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n6 => 4
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n7 => 5
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n8 => 6
  | PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n16 => 7
  end.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F2 n :=
  match n with
  | 0 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n2
  | 1 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n3
  | 2 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n4
  | 3 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n5
  | 4 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n6
  | 5 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n7
  | 6 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n8
  | 7 => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n16
  | _ => PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__n2
  end.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1F2 : forall x : PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Type, (PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1 x <= 7) /\ PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F2 (PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F2F1 : forall (y : nat) (H : y <= 7), PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1 (PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type : Set :=
  make__PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type {
    PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730 : option PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Type ;
}.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__list := (
 Opt PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Type PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__cond ::
 nil).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond z := 
  opt_cond PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__cond (PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730 z) /\
  True.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext1__Type := PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1__cond := PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond.

Record PDSCH_TimeDomainResourceAllocation_r16__Type : Set :=
  make__PDSCH_TimeDomainResourceAllocation_r16__Type {
    PDSCH_TimeDomainResourceAllocation_r16__k0_r16 : option Z ;
    PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16 : PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Type ;
    PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16 : Z ;
    PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16 : option PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Type ;
    PDSCH_TimeDomainResourceAllocation_r16__ext0 : option PDSCH_TimeDomainResourceAllocation_r16__ext0__Type ;
    PDSCH_TimeDomainResourceAllocation_r16__ext1 : option PDSCH_TimeDomainResourceAllocation_r16__ext1__Type ;
}.
Definition PDSCH_TimeDomainResourceAllocation_r16__root_list : list seq_elem := (
 Opt Z PDSCH_TimeDomainResourceAllocation_r16__k0_r16__cond ::
 Nor PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Type PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__cond ::
 Nor Z PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__cond ::
 Opt PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Type PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__cond ::
 nil).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext_list : list typ := (
  typ_cons PDSCH_TimeDomainResourceAllocation_r16__ext0__Type PDSCH_TimeDomainResourceAllocation_r16__ext0__cond ::
  typ_cons PDSCH_TimeDomainResourceAllocation_r16__ext1__Type PDSCH_TimeDomainResourceAllocation_r16__ext1__cond ::
  nil).
Definition PDSCH_TimeDomainResourceAllocation_r16__cond (z : PDSCH_TimeDomainResourceAllocation_r16__Type) := 
(  opt_cond PDSCH_TimeDomainResourceAllocation_r16__k0_r16__cond (PDSCH_TimeDomainResourceAllocation_r16__k0_r16 z) /\
  PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__cond (PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16 z) /\
  PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__cond (PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16 z) /\
  opt_cond PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__cond (PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16 z) /\
  True) /\ 
(  opt_cond PDSCH_TimeDomainResourceAllocation_r16__ext0__cond (PDSCH_TimeDomainResourceAllocation_r16__ext0 z) /\
  opt_cond PDSCH_TimeDomainResourceAllocation_r16__ext1__cond (PDSCH_TimeDomainResourceAllocation_r16__ext1 z) /\
  True).


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
Definition PDSCH_TimeDomainResourceAllocation_r16__k0_r16__Format : T_Format Z PDSCH_TimeDomainResourceAllocation_r16__k0_r16__cond :=
 ranged_int_format (0) (32) PDSCH_TimeDomainResourceAllocation_r16__k0_r16__helper1 PDSCH_TimeDomainResourceAllocation_r16__k0_r16__helper2.

Opaque PDSCH_TimeDomainResourceAllocation_r16__k0_r16__cond PDSCH_TimeDomainResourceAllocation_r16__k0_r16__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__nat__Format PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1 PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F2 PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F1F2 PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__F2F1.

Opaque PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__cond PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__Format : T_Format Z PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__cond :=
 ranged_int_format (0) (127) PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__helper1 PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__helper2.

Opaque PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__cond PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__nat__Format PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1 PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F2 PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F1F2 PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__F2F1.

Opaque PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__cond PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__Format : T_Format Z PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__cond :=
 ranged_int_format (33) (128) PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__helper1 PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__helper2.

Opaque PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__cond PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__Format.


Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format_Type := Eval cbn in seq_format_prod PDSCH_TimeDomainResourceAllocation_r16__ext0O__list.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format_list : PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format_Type :=
  (PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710__Format, unit_format).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__list__Format := (*Eval compute in *) seq_format PDSCH_TimeDomainResourceAllocation_r16__ext0O__list PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format_list.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1 z :=
  (PDSCH_TimeDomainResourceAllocation_r16__ext0O__k0_v1710 z, tt).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2 (y : seq_type PDSCH_TimeDomainResourceAllocation_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type i0
  end.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1F2_cond (z : PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type)
  : PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond z ->
  (seq_cond PDSCH_TimeDomainResourceAllocation_r16__ext0O__list (PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1 z)).
intro H. unfold PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1F2_cond2 (z : PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type)
 : PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2 (PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2F1_cond (y : seq_type PDSCH_TimeDomainResourceAllocation_r16__ext0O__list)
  : seq_cond PDSCH_TimeDomainResourceAllocation_r16__ext0O__list y ->
 (PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond (PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2 y)) /\  PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1 (PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond :=
        proj2_format  PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond PDSCH_TimeDomainResourceAllocation_r16__ext0O__list__Format
    PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1 PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2 PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1F2_cond  PDSCH_TimeDomainResourceAllocation_r16__ext0O__F1F2_cond2 PDSCH_TimeDomainResourceAllocation_r16__ext0O__F2F1_cond.
Opaque PDSCH_TimeDomainResourceAllocation_r16__ext0O__cond PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext0__check_all_none (b : PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type) : bool :=
match b with 
  | make__PDSCH_TimeDomainResourceAllocation_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext0__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__ext0__Type PDSCH_TimeDomainResourceAllocation_r16__ext0__cond :=
  restrict_add_format PDSCH_TimeDomainResourceAllocation_r16__ext0__check_all_none PDSCH_TimeDomainResourceAllocation_r16__ext0O__Format.

Opaque PDSCH_TimeDomainResourceAllocation_r16__ext0__cond PDSCH_TimeDomainResourceAllocation_r16__ext0__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__nat__Format PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1 PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F2 PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F1F2 PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__F2F1.

Opaque PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__cond PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Format.


Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format_Type := Eval cbn in seq_format_prod PDSCH_TimeDomainResourceAllocation_r16__ext1O__list.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format_list : PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format_Type :=
  (PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730__Format, unit_format).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__list__Format := (*Eval compute in *) seq_format PDSCH_TimeDomainResourceAllocation_r16__ext1O__list PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format_list.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1 z :=
  (PDSCH_TimeDomainResourceAllocation_r16__ext1O__repetitionNumber_v1730 z, tt).
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2 (y : seq_type PDSCH_TimeDomainResourceAllocation_r16__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type i0
  end.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1F2_cond (z : PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type)
  : PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond z ->
  (seq_cond PDSCH_TimeDomainResourceAllocation_r16__ext1O__list (PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1 z)).
intro H. unfold PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1F2_cond2 (z : PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type)
 : PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2 (PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2F1_cond (y : seq_type PDSCH_TimeDomainResourceAllocation_r16__ext1O__list)
  : seq_cond PDSCH_TimeDomainResourceAllocation_r16__ext1O__list y ->
 (PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond (PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2 y)) /\  PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1 (PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond :=
        proj2_format  PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond PDSCH_TimeDomainResourceAllocation_r16__ext1O__list__Format
    PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1 PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2 PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1F2_cond  PDSCH_TimeDomainResourceAllocation_r16__ext1O__F1F2_cond2 PDSCH_TimeDomainResourceAllocation_r16__ext1O__F2F1_cond.
Opaque PDSCH_TimeDomainResourceAllocation_r16__ext1O__cond PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format.

Definition PDSCH_TimeDomainResourceAllocation_r16__ext1__check_all_none (b : PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type) : bool :=
match b with 
  | make__PDSCH_TimeDomainResourceAllocation_r16__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext1__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__ext1__Type PDSCH_TimeDomainResourceAllocation_r16__ext1__cond :=
  restrict_add_format PDSCH_TimeDomainResourceAllocation_r16__ext1__check_all_none PDSCH_TimeDomainResourceAllocation_r16__ext1O__Format.

Opaque PDSCH_TimeDomainResourceAllocation_r16__ext1__cond PDSCH_TimeDomainResourceAllocation_r16__ext1__Format.


Definition PDSCH_TimeDomainResourceAllocation_r16__root_Format_Type := Eval cbn in seq_format_prod PDSCH_TimeDomainResourceAllocation_r16__root_list.
Definition PDSCH_TimeDomainResourceAllocation_r16__root_Format_list : PDSCH_TimeDomainResourceAllocation_r16__root_Format_Type :=
  (PDSCH_TimeDomainResourceAllocation_r16__k0_r16__Format, (PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16__Format, (PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16__Format, (PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16__Format, unit_format)))).

Definition PDSCH_TimeDomainResourceAllocation_r16__ext_Format_Type := Eval cbn in get_formats PDSCH_TimeDomainResourceAllocation_r16__ext_list.
Definition PDSCH_TimeDomainResourceAllocation_r16__ext_Format_list : PDSCH_TimeDomainResourceAllocation_r16__ext_Format_Type :=
  (PDSCH_TimeDomainResourceAllocation_r16__ext0__Format, (PDSCH_TimeDomainResourceAllocation_r16__ext1__Format, unit__Format)).

Definition PDSCH_TimeDomainResourceAllocation_r16__list_type : Set := (seq_type PDSCH_TimeDomainResourceAllocation_r16__root_list) * (seq_ext_type PDSCH_TimeDomainResourceAllocation_r16__ext_list).
Definition PDSCH_TimeDomainResourceAllocation_r16__list_cond (z : PDSCH_TimeDomainResourceAllocation_r16__list_type) : Prop :=
        (seq_cond PDSCH_TimeDomainResourceAllocation_r16__root_list (fst z)) /\ (seq_ext_cond PDSCH_TimeDomainResourceAllocation_r16__ext_list (snd z)).
Definition PDSCH_TimeDomainResourceAllocation_r16__list_format : T_Format PDSCH_TimeDomainResourceAllocation_r16__list_type PDSCH_TimeDomainResourceAllocation_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PDSCH_TimeDomainResourceAllocation_r16__root_list PDSCH_TimeDomainResourceAllocation_r16__root_Format_list PDSCH_TimeDomainResourceAllocation_r16__ext_list PDSCH_TimeDomainResourceAllocation_r16__ext_Format_list.

Opaque PDSCH_TimeDomainResourceAllocation_r16__list_format.
Definition PDSCH_TimeDomainResourceAllocation_r16__F1 (z : PDSCH_TimeDomainResourceAllocation_r16__Type) : PDSCH_TimeDomainResourceAllocation_r16__list_type :=
  (((PDSCH_TimeDomainResourceAllocation_r16__k0_r16 z, (PDSCH_TimeDomainResourceAllocation_r16__mappingType_r16 z, (PDSCH_TimeDomainResourceAllocation_r16__startSymbolAndLength_r16 z, (PDSCH_TimeDomainResourceAllocation_r16__repetitionNumber_r16 z, tt))))), (
(PDSCH_TimeDomainResourceAllocation_r16__ext0 z, (PDSCH_TimeDomainResourceAllocation_r16__ext1 z, tt)))).
Definition PDSCH_TimeDomainResourceAllocation_r16__F2 (y : PDSCH_TimeDomainResourceAllocation_r16__list_type) : PDSCH_TimeDomainResourceAllocation_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__PDSCH_TimeDomainResourceAllocation_r16__Type j0 j1 j2 j3 i0 i1
  end.
Definition PDSCH_TimeDomainResourceAllocation_r16__helper1 : (forall a : PDSCH_TimeDomainResourceAllocation_r16__Type, PDSCH_TimeDomainResourceAllocation_r16__cond a -> PDSCH_TimeDomainResourceAllocation_r16__list_cond (PDSCH_TimeDomainResourceAllocation_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__helper2 : (forall a : PDSCH_TimeDomainResourceAllocation_r16__Type, PDSCH_TimeDomainResourceAllocation_r16__F2 (PDSCH_TimeDomainResourceAllocation_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__helper3 : (forall b : PDSCH_TimeDomainResourceAllocation_r16__list_type, PDSCH_TimeDomainResourceAllocation_r16__list_cond b -> PDSCH_TimeDomainResourceAllocation_r16__cond (PDSCH_TimeDomainResourceAllocation_r16__F2 b) /\ PDSCH_TimeDomainResourceAllocation_r16__F1 (PDSCH_TimeDomainResourceAllocation_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDSCH_TimeDomainResourceAllocation_r16__cond, PDSCH_TimeDomainResourceAllocation_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDSCH_TimeDomainResourceAllocation_r16__Format : T_Format PDSCH_TimeDomainResourceAllocation_r16__Type PDSCH_TimeDomainResourceAllocation_r16__cond :=
 proj2_format PDSCH_TimeDomainResourceAllocation_r16__cond PDSCH_TimeDomainResourceAllocation_r16__list_format  PDSCH_TimeDomainResourceAllocation_r16__F1 PDSCH_TimeDomainResourceAllocation_r16__F2 PDSCH_TimeDomainResourceAllocation_r16__helper1 PDSCH_TimeDomainResourceAllocation_r16__helper2 PDSCH_TimeDomainResourceAllocation_r16__helper3.

Opaque PDSCH_TimeDomainResourceAllocation_r16__cond PDSCH_TimeDomainResourceAllocation_r16__Format.

