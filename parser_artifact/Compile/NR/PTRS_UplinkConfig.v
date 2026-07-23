Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__Type := Z.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__cond := (fun z => (1 <= z <= 276)%Z).
Definition PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Type := list Z.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__cond (z : PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Type) := (list_and PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__cond z) /\ (length z = Z.to_nat 2).

Lemma PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__Type := Z.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__cond := (fun z => (0 <= z <= 29)%Z).
Definition PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Type := list Z.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__cond (z : PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Type) := (list_and PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__cond z) /\ (length z = Z.to_nat 3).

Inductive PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Type : Set :=
 | PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n1
 | PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n2
.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__cond := (fun (_ : PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Type) => True).
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__nat__helper.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1 t :=
  match t with
  | PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n1 => 0
  | PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n2 => 1
  end.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F2 n :=
  match n with
  | 0 => PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n1
  | 1 => PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n2
  | _ => PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__n1
  end.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1F2 : forall x : PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Type, (PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1 x <= 1) /\ PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F2 (PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1 x) = x. imp_solve. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F2F1 : forall (y : nat) (H : y <= 1), PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1 (PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F2 y) = y. enum_solve H y. Qed.

Inductive PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Type : Set :=
 | PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset01
 | PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset10
 | PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset11
.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__cond := (fun (_ : PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Type) => True).
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__nat__helper.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1 t :=
  match t with
  | PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset01 => 0
  | PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset10 => 1
  | PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset11 => 2
  end.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F2 n :=
  match n with
  | 0 => PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset01
  | 1 => PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset10
  | 2 => PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset11
  | _ => PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__offset01
  end.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1F2 : forall x : PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Type, (PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1 x <= 2) /\ PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F2 (PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1 x) = x. imp_solve. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F2F1 : forall (y : nat) (H : y <= 2), PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1 (PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F2 y) = y. enum_solve H y. Qed.

Inductive PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Type : Set :=
 | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p00
 | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p01
 | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p10
 | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p11
.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__cond := (fun (_ : PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Type) => True).
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__nat__helper.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1 t :=
  match t with
  | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p00 => 0
  | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p01 => 1
  | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p10 => 2
  | PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p11 => 3
  end.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F2 n :=
  match n with
  | 0 => PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p00
  | 1 => PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p01
  | 2 => PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p10
  | 3 => PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p11
  | _ => PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__p00
  end.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1F2 : forall x : PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Type, (PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1 x <= 3) /\ PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F2 (PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1 x) = x. imp_solve. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F2F1 : forall (y : nat) (H : y <= 3), PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1 (PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F2 y) = y. enum_solve H y. Qed.

Record PTRS_UplinkConfig__transformPrecoderDisabled__Type : Set :=
  make__PTRS_UplinkConfig__transformPrecoderDisabled__Type {
    PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity : option PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Type ;
    PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity : option PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Type ;
    PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts : PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Type ;
    PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset : option PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Type ;
    PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power : PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Type ;
}.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__list := (
 Opt PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Type PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__cond ::
 Opt PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Type PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__cond ::
 Nor PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Type PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__cond ::
 Opt PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Type PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__cond ::
 Nor PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Type PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__cond ::
 nil).
Definition PTRS_UplinkConfig__transformPrecoderDisabled__cond z := 
  opt_cond PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__cond (PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity z) /\
  opt_cond PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__cond (PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity z) /\
  PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__cond (PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts z) /\
  opt_cond PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__cond (PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset z) /\
  PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__cond (PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power z) /\
  True.

Lemma PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__Type := Z.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__cond := (fun z => (1 <= z <= 276)%Z).
Definition PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Type := list Z.

Definition PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__cond (z : PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Type) := (list_and PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__cond z) /\ (length z = Z.to_nat 5).

Inductive PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Type : Set :=
 | PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__d2
.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__cond := (fun (_ : PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Type) => True).
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__nat__helper.

Definition PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1 t :=
  match t with
  | PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__d2 => 0
  end.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F2 n :=
  match n with
  | 0 => PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__d2
  | _ => PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__d2
  end.
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1F2 : forall x : PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Type, (PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1 x <= 0) /\ PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F2 (PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1 x) = x. imp_solve. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F2F1 : forall (y : nat) (H : y <= 0), PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1 (PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F2 y) = y. enum_solve H y. Qed.

Record PTRS_UplinkConfig__transformPrecoderEnabled__Type : Set :=
  make__PTRS_UplinkConfig__transformPrecoderEnabled__Type {
    PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity : PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Type ;
    PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding : option PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Type ;
}.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__list := (
 Nor PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Type PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__cond ::
 Opt PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Type PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__cond ::
 nil).
Definition PTRS_UplinkConfig__transformPrecoderEnabled__cond z := 
  PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__cond (PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity z) /\
  opt_cond PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__cond (PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding z) /\
  True.

Record PTRS_UplinkConfig__Type : Set :=
  make__PTRS_UplinkConfig__Type {
    PTRS_UplinkConfig__transformPrecoderDisabled : option PTRS_UplinkConfig__transformPrecoderDisabled__Type ;
    PTRS_UplinkConfig__transformPrecoderEnabled : option PTRS_UplinkConfig__transformPrecoderEnabled__Type ;
}.
Definition PTRS_UplinkConfig__root_list : list seq_elem := (
 Opt PTRS_UplinkConfig__transformPrecoderDisabled__Type PTRS_UplinkConfig__transformPrecoderDisabled__cond ::
 Opt PTRS_UplinkConfig__transformPrecoderEnabled__Type PTRS_UplinkConfig__transformPrecoderEnabled__cond ::
 nil).
Definition PTRS_UplinkConfig__ext_list : list typ := (
  nil).
Definition PTRS_UplinkConfig__cond (z : PTRS_UplinkConfig__Type) := 
(  opt_cond PTRS_UplinkConfig__transformPrecoderDisabled__cond (PTRS_UplinkConfig__transformPrecoderDisabled z) /\
  opt_cond PTRS_UplinkConfig__transformPrecoderEnabled__cond (PTRS_UplinkConfig__transformPrecoderEnabled z) /\
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
Definition PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__Format : T_Format Z PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__cond :=
 ranged_int_format (1) (276) PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__helper1 PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__helper2.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__cond PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__Format.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Format : T_Format PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Type PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__cond := seq_of_fixed_format PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__seq_of__Format 2.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__cond PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Format.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__Format : T_Format Z PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__cond :=
 ranged_int_format (0) (29) PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__helper1 PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__helper2.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__cond PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__Format.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Format : T_Format PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Type PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__cond := seq_of_fixed_format PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__seq_of__Format 3.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__cond PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Format.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Format : T_Format PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__nat__Format PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1 PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F2 PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F1F2 PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__F2F1.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__cond PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Format.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Format : T_Format PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__nat__Format PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1 PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F2 PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F1F2 PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__F2F1.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__cond PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Format.

Definition PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Format : T_Format PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__nat__Format PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1 PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F2 PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F1F2 PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__F2F1.

Opaque PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__cond PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Format.


Definition PTRS_UplinkConfig__transformPrecoderDisabled__Format_Type := Eval cbn in seq_format_prod PTRS_UplinkConfig__transformPrecoderDisabled__list.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__Format_list : PTRS_UplinkConfig__transformPrecoderDisabled__Format_Type :=
  (PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity__Format, (PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity__Format, (PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts__Format, (PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset__Format, (PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power__Format, unit_format))))).
Definition PTRS_UplinkConfig__transformPrecoderDisabled__list__Format := (*Eval compute in *) seq_format PTRS_UplinkConfig__transformPrecoderDisabled__list PTRS_UplinkConfig__transformPrecoderDisabled__Format_list.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__F1 z :=
  (PTRS_UplinkConfig__transformPrecoderDisabled__frequencyDensity z, (PTRS_UplinkConfig__transformPrecoderDisabled__timeDensity z, (PTRS_UplinkConfig__transformPrecoderDisabled__maxNrofPorts z, (PTRS_UplinkConfig__transformPrecoderDisabled__resourceElementOffset z, (PTRS_UplinkConfig__transformPrecoderDisabled__ptrs_Power z, tt))))).
Definition PTRS_UplinkConfig__transformPrecoderDisabled__F2 (y : seq_type PTRS_UplinkConfig__transformPrecoderDisabled__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__PTRS_UplinkConfig__transformPrecoderDisabled__Type i0 i1 i2 i3 i4
  end.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__F1F2_cond (z : PTRS_UplinkConfig__transformPrecoderDisabled__Type)
  : PTRS_UplinkConfig__transformPrecoderDisabled__cond z ->
  (seq_cond PTRS_UplinkConfig__transformPrecoderDisabled__list (PTRS_UplinkConfig__transformPrecoderDisabled__F1 z)).
intro H. unfold PTRS_UplinkConfig__transformPrecoderDisabled__cond in H. simpl. auto. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__F1F2_cond2 (z : PTRS_UplinkConfig__transformPrecoderDisabled__Type)
 : PTRS_UplinkConfig__transformPrecoderDisabled__F2 (PTRS_UplinkConfig__transformPrecoderDisabled__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderDisabled__F2F1_cond (y : seq_type PTRS_UplinkConfig__transformPrecoderDisabled__list)
  : seq_cond PTRS_UplinkConfig__transformPrecoderDisabled__list y ->
 (PTRS_UplinkConfig__transformPrecoderDisabled__cond (PTRS_UplinkConfig__transformPrecoderDisabled__F2 y)) /\  PTRS_UplinkConfig__transformPrecoderDisabled__F1 (PTRS_UplinkConfig__transformPrecoderDisabled__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PTRS_UplinkConfig__transformPrecoderDisabled__cond. simpl in *. auto.
 - simpl. unfold PTRS_UplinkConfig__transformPrecoderDisabled__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PTRS_UplinkConfig__transformPrecoderDisabled__Format : T_Format PTRS_UplinkConfig__transformPrecoderDisabled__Type PTRS_UplinkConfig__transformPrecoderDisabled__cond :=
        proj2_format  PTRS_UplinkConfig__transformPrecoderDisabled__cond PTRS_UplinkConfig__transformPrecoderDisabled__list__Format
    PTRS_UplinkConfig__transformPrecoderDisabled__F1 PTRS_UplinkConfig__transformPrecoderDisabled__F2 PTRS_UplinkConfig__transformPrecoderDisabled__F1F2_cond  PTRS_UplinkConfig__transformPrecoderDisabled__F1F2_cond2 PTRS_UplinkConfig__transformPrecoderDisabled__F2F1_cond.
Opaque PTRS_UplinkConfig__transformPrecoderDisabled__cond PTRS_UplinkConfig__transformPrecoderDisabled__Format.

Definition PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__Format : T_Format Z PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__cond :=
 ranged_int_format (1) (276) PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__helper1 PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__helper2.

Opaque PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__cond PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__Format.

Definition PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Format : T_Format PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Type PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__cond := seq_of_fixed_format PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__seq_of__Format 5.

Opaque PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__cond PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Format.

Definition PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Format : T_Format PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__nat__Format PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1 PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F2 PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F1F2 PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__F2F1.

Opaque PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__cond PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Format.


Definition PTRS_UplinkConfig__transformPrecoderEnabled__Format_Type := Eval cbn in seq_format_prod PTRS_UplinkConfig__transformPrecoderEnabled__list.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__Format_list : PTRS_UplinkConfig__transformPrecoderEnabled__Format_Type :=
  (PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity__Format, (PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding__Format, unit_format)).
Definition PTRS_UplinkConfig__transformPrecoderEnabled__list__Format := (*Eval compute in *) seq_format PTRS_UplinkConfig__transformPrecoderEnabled__list PTRS_UplinkConfig__transformPrecoderEnabled__Format_list.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__F1 z :=
  (PTRS_UplinkConfig__transformPrecoderEnabled__sampleDensity z, (PTRS_UplinkConfig__transformPrecoderEnabled__timeDensityTransformPrecoding z, tt)).
Definition PTRS_UplinkConfig__transformPrecoderEnabled__F2 (y : seq_type PTRS_UplinkConfig__transformPrecoderEnabled__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PTRS_UplinkConfig__transformPrecoderEnabled__Type i0 i1
  end.
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__F1F2_cond (z : PTRS_UplinkConfig__transformPrecoderEnabled__Type)
  : PTRS_UplinkConfig__transformPrecoderEnabled__cond z ->
  (seq_cond PTRS_UplinkConfig__transformPrecoderEnabled__list (PTRS_UplinkConfig__transformPrecoderEnabled__F1 z)).
intro H. unfold PTRS_UplinkConfig__transformPrecoderEnabled__cond in H. simpl. auto. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__F1F2_cond2 (z : PTRS_UplinkConfig__transformPrecoderEnabled__Type)
 : PTRS_UplinkConfig__transformPrecoderEnabled__F2 (PTRS_UplinkConfig__transformPrecoderEnabled__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PTRS_UplinkConfig__transformPrecoderEnabled__F2F1_cond (y : seq_type PTRS_UplinkConfig__transformPrecoderEnabled__list)
  : seq_cond PTRS_UplinkConfig__transformPrecoderEnabled__list y ->
 (PTRS_UplinkConfig__transformPrecoderEnabled__cond (PTRS_UplinkConfig__transformPrecoderEnabled__F2 y)) /\  PTRS_UplinkConfig__transformPrecoderEnabled__F1 (PTRS_UplinkConfig__transformPrecoderEnabled__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PTRS_UplinkConfig__transformPrecoderEnabled__cond. simpl in *. auto.
 - simpl. unfold PTRS_UplinkConfig__transformPrecoderEnabled__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PTRS_UplinkConfig__transformPrecoderEnabled__Format : T_Format PTRS_UplinkConfig__transformPrecoderEnabled__Type PTRS_UplinkConfig__transformPrecoderEnabled__cond :=
        proj2_format  PTRS_UplinkConfig__transformPrecoderEnabled__cond PTRS_UplinkConfig__transformPrecoderEnabled__list__Format
    PTRS_UplinkConfig__transformPrecoderEnabled__F1 PTRS_UplinkConfig__transformPrecoderEnabled__F2 PTRS_UplinkConfig__transformPrecoderEnabled__F1F2_cond  PTRS_UplinkConfig__transformPrecoderEnabled__F1F2_cond2 PTRS_UplinkConfig__transformPrecoderEnabled__F2F1_cond.
Opaque PTRS_UplinkConfig__transformPrecoderEnabled__cond PTRS_UplinkConfig__transformPrecoderEnabled__Format.


Definition PTRS_UplinkConfig__root_Format_Type := Eval cbn in seq_format_prod PTRS_UplinkConfig__root_list.
Definition PTRS_UplinkConfig__root_Format_list : PTRS_UplinkConfig__root_Format_Type :=
  (PTRS_UplinkConfig__transformPrecoderDisabled__Format, (PTRS_UplinkConfig__transformPrecoderEnabled__Format, unit_format)).

Definition PTRS_UplinkConfig__ext_Format_Type := Eval cbn in get_formats PTRS_UplinkConfig__ext_list.
Definition PTRS_UplinkConfig__ext_Format_list : PTRS_UplinkConfig__ext_Format_Type :=
  unit__Format.

Definition PTRS_UplinkConfig__list_type : Set := (seq_type PTRS_UplinkConfig__root_list) * (seq_ext_type PTRS_UplinkConfig__ext_list).
Definition PTRS_UplinkConfig__list_cond (z : PTRS_UplinkConfig__list_type) : Prop :=
        (seq_cond PTRS_UplinkConfig__root_list (fst z)) /\ (seq_ext_cond PTRS_UplinkConfig__ext_list (snd z)).
Definition PTRS_UplinkConfig__list_format : T_Format PTRS_UplinkConfig__list_type PTRS_UplinkConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PTRS_UplinkConfig__root_list PTRS_UplinkConfig__root_Format_list PTRS_UplinkConfig__ext_list PTRS_UplinkConfig__ext_Format_list.

Opaque PTRS_UplinkConfig__list_format.
Definition PTRS_UplinkConfig__F1 (z : PTRS_UplinkConfig__Type) : PTRS_UplinkConfig__list_type :=
  (((PTRS_UplinkConfig__transformPrecoderDisabled z, (PTRS_UplinkConfig__transformPrecoderEnabled z, tt))), (
tt)).
Definition PTRS_UplinkConfig__F2 (y : PTRS_UplinkConfig__list_type) : PTRS_UplinkConfig__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__PTRS_UplinkConfig__Type j0 j1
  end.
Definition PTRS_UplinkConfig__helper1 : (forall a : PTRS_UplinkConfig__Type, PTRS_UplinkConfig__cond a -> PTRS_UplinkConfig__list_cond (PTRS_UplinkConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PTRS_UplinkConfig__helper2 : (forall a : PTRS_UplinkConfig__Type, PTRS_UplinkConfig__F2 (PTRS_UplinkConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PTRS_UplinkConfig__helper3 : (forall b : PTRS_UplinkConfig__list_type, PTRS_UplinkConfig__list_cond b -> PTRS_UplinkConfig__cond (PTRS_UplinkConfig__F2 b) /\ PTRS_UplinkConfig__F1 (PTRS_UplinkConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PTRS_UplinkConfig__cond, PTRS_UplinkConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PTRS_UplinkConfig__Format : T_Format PTRS_UplinkConfig__Type PTRS_UplinkConfig__cond :=
 proj2_format PTRS_UplinkConfig__cond PTRS_UplinkConfig__list_format  PTRS_UplinkConfig__F1 PTRS_UplinkConfig__F2 PTRS_UplinkConfig__helper1 PTRS_UplinkConfig__helper2 PTRS_UplinkConfig__helper3.

Opaque PTRS_UplinkConfig__cond PTRS_UplinkConfig__Format.

