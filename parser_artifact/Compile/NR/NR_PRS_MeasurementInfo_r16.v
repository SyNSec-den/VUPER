Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__Type := Z.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__cond := (fun z => (0 <= z <= 19)%Z).
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__Type := Z.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__cond := (fun z => (0 <= z <= 39)%Z).
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__Type := Z.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__cond := (fun z => (0 <= z <= 79)%Z).
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__Type := Z.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__cond := (fun z => (0 <= z <= 159)%Z).

Inductive NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type : Set :=
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16 : Z -> NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16 : Z -> NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16 : Z -> NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16 : Z -> NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type
.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list : list typ := (
typ_cons Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__cond ::
typ_cons Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__cond ::
typ_cons Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__cond ::
typ_cons Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__cond ::
 nil).
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond (c : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type) := 
  match c with
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16 t => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__cond t 
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16 t => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__cond t 
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16 t => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__cond t 
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16 t => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__cond t 
  end.

Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__len_helper1 : to_bit_sz (length NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__len_helper2 : 2 <= length2 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list.
 simpl. lia. Qed.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type : Set := Empty_set.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__cond (c : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type) := True.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type : Set := NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type + NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__cond :=
  sum_cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__cond.
Inductive NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type : Set :=
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms1dot5
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3dot5
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms4
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms5dot5
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms6
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms10
 | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms20
.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__cond := (fun (_ : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type) => True).
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__nat__helper.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1 t :=
  match t with
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms1dot5 => 0
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3 => 1
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3dot5 => 2
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms4 => 3
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms5dot5 => 4
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms6 => 5
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms10 => 6
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms20 => 7
  end.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2 n :=
  match n with
  | 0 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms1dot5
  | 1 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3
  | 2 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3dot5
  | 3 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms4
  | 4 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms5dot5
  | 5 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms6
  | 6 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms10
  | 7 => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms20
  | _ => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms1dot5
  end.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1F2 : forall x : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1 x <= 7) /\ NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2 (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1 x) = x. imp_solve. Qed.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2F1 : forall (y : nat) (H : y <= 7), NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1 (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2 y) = y. enum_solve H y. Qed.

Record NR_PRS_MeasurementInfo_r16__Type : Set :=
  make__NR_PRS_MeasurementInfo_r16__Type {
    NR_PRS_MeasurementInfo_r16__dl_PRS_PointA_r16 : ARFCN_ValueNR__Type ;
    NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16 : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type ;
    NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16 : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type ;
}.
Definition NR_PRS_MeasurementInfo_r16__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__cond ::
 Nor NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__cond ::
 nil).
Definition NR_PRS_MeasurementInfo_r16__ext_list : list typ := (
  nil).
Definition NR_PRS_MeasurementInfo_r16__cond (z : NR_PRS_MeasurementInfo_r16__Type) := 
(  ARFCN_ValueNR__cond (NR_PRS_MeasurementInfo_r16__dl_PRS_PointA_r16 z) /\
  NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__cond (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16 z) /\
  NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__cond (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16 z) /\
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
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__Format : T_Format Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__cond :=
 ranged_int_format (0) (19) NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__helper1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__helper2.

Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__Format.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__Format : T_Format Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__cond :=
 ranged_int_format (0) (39) NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__helper1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__helper2.

Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__Format.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__Format : T_Format Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__cond :=
 ranged_int_format (0) (79) NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__helper1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__helper2.

Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__Format.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__Format : T_Format Z NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__cond :=
 ranged_int_format (0) (159) NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__helper1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__helper2.

Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__Format.


Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format_Type := Eval cbn in get_formats NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format_list : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format_Type :=
  (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__Format, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__Format, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__Format, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__Format, unit__Format)))).
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list__Format := Eval compute in choice_format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__len_helper1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__len_helper2  NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format_list.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 (z : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type) : (choice NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list) :=
  match z with
   | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16 t => existT _ 0 t
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16 t => existT _ 1 t
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16 t => existT _ 2 t
  | NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16 t => existT _ 3 t
  end.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__g := (fun n => typ_set (get_nth_typ NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list n)).
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2 (y : choice NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list) : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__g n -> NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type) with
    | 0 => fun (t : Z) => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16 t 
    | 1 => fun (t : Z) => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16 t 
    | 2 => fun (t : Z) => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16 t 
    | 3 => fun (t : Z) => NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type with end) n0
           end t0).

Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__helper2 :  forall (y : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type), NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond y -> choice_cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__helper3 :  forall (y : NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type), NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2 (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__helper4 : (forall b : choice NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list, choice_cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list b -> NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2 b) /\ NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2.
Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format : T_Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond :=
  (* Eval compute in *) proj2_format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list__Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__helper2 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__helper3 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__helper4.
Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Format : T_Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__cond := empty_format.
Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Format.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Format : T_Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__cond := sum_format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Format.
Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Format.

Definition NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Format : T_Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__nat__Format NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1F2 NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2F1.

Opaque NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__cond NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Format.


Definition NR_PRS_MeasurementInfo_r16__root_Format_Type := Eval cbn in seq_format_prod NR_PRS_MeasurementInfo_r16__root_list.
Definition NR_PRS_MeasurementInfo_r16__root_Format_list : NR_PRS_MeasurementInfo_r16__root_Format_Type :=
  (ARFCN_ValueNR__Format, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Format, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Format, unit_format))).

Definition NR_PRS_MeasurementInfo_r16__ext_Format_Type := Eval cbn in get_formats NR_PRS_MeasurementInfo_r16__ext_list.
Definition NR_PRS_MeasurementInfo_r16__ext_Format_list : NR_PRS_MeasurementInfo_r16__ext_Format_Type :=
  unit__Format.

Definition NR_PRS_MeasurementInfo_r16__list_type : Set := (seq_type NR_PRS_MeasurementInfo_r16__root_list) * (seq_ext_type NR_PRS_MeasurementInfo_r16__ext_list).
Definition NR_PRS_MeasurementInfo_r16__list_cond (z : NR_PRS_MeasurementInfo_r16__list_type) : Prop :=
        (seq_cond NR_PRS_MeasurementInfo_r16__root_list (fst z)) /\ (seq_ext_cond NR_PRS_MeasurementInfo_r16__ext_list (snd z)).
Definition NR_PRS_MeasurementInfo_r16__list_format : T_Format NR_PRS_MeasurementInfo_r16__list_type NR_PRS_MeasurementInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format NR_PRS_MeasurementInfo_r16__root_list NR_PRS_MeasurementInfo_r16__root_Format_list NR_PRS_MeasurementInfo_r16__ext_list NR_PRS_MeasurementInfo_r16__ext_Format_list.

Opaque NR_PRS_MeasurementInfo_r16__list_format.
Definition NR_PRS_MeasurementInfo_r16__F1 (z : NR_PRS_MeasurementInfo_r16__Type) : NR_PRS_MeasurementInfo_r16__list_type :=
  (((NR_PRS_MeasurementInfo_r16__dl_PRS_PointA_r16 z, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16 z, (NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16 z, tt)))), (
tt)).
Definition NR_PRS_MeasurementInfo_r16__F2 (y : NR_PRS_MeasurementInfo_r16__list_type) : NR_PRS_MeasurementInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__NR_PRS_MeasurementInfo_r16__Type j0 j1 j2
  end.
Definition NR_PRS_MeasurementInfo_r16__helper1 : (forall a : NR_PRS_MeasurementInfo_r16__Type, NR_PRS_MeasurementInfo_r16__cond a -> NR_PRS_MeasurementInfo_r16__list_cond (NR_PRS_MeasurementInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NR_PRS_MeasurementInfo_r16__helper2 : (forall a : NR_PRS_MeasurementInfo_r16__Type, NR_PRS_MeasurementInfo_r16__F2 (NR_PRS_MeasurementInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NR_PRS_MeasurementInfo_r16__helper3 : (forall b : NR_PRS_MeasurementInfo_r16__list_type, NR_PRS_MeasurementInfo_r16__list_cond b -> NR_PRS_MeasurementInfo_r16__cond (NR_PRS_MeasurementInfo_r16__F2 b) /\ NR_PRS_MeasurementInfo_r16__F1 (NR_PRS_MeasurementInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NR_PRS_MeasurementInfo_r16__cond, NR_PRS_MeasurementInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NR_PRS_MeasurementInfo_r16__Format : T_Format NR_PRS_MeasurementInfo_r16__Type NR_PRS_MeasurementInfo_r16__cond :=
 proj2_format NR_PRS_MeasurementInfo_r16__cond NR_PRS_MeasurementInfo_r16__list_format  NR_PRS_MeasurementInfo_r16__F1 NR_PRS_MeasurementInfo_r16__F2 NR_PRS_MeasurementInfo_r16__helper1 NR_PRS_MeasurementInfo_r16__helper2 NR_PRS_MeasurementInfo_r16__helper3.

Opaque NR_PRS_MeasurementInfo_r16__cond NR_PRS_MeasurementInfo_r16__Format.

