Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NZP_CSI_RS_ResourceSetId.

Opaque NZP_CSI_RS_ResourceSetId__cond NZP_CSI_RS_ResourceSetId__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Definition NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Type := list NZP_CSI_RS_ResourceId__Type.

Lemma NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_ResourcesPerSet)%Z. unfold maxNrofNZP_CSI_RS_ResourcesPerSet.
 lia. Qed.
Lemma NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_ResourcesPerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_ResourcesPerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__cond (z : NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_ResourcesPerSet)%Z /\ (list_and NZP_CSI_RS_ResourceId__cond z) .

Inductive NZP_CSI_RS_ResourceSet__repetition__Type : Set :=
 | NZP_CSI_RS_ResourceSet__repetition__on
 | NZP_CSI_RS_ResourceSet__repetition__off
.
Definition NZP_CSI_RS_ResourceSet__repetition__cond := (fun (_ : NZP_CSI_RS_ResourceSet__repetition__Type) => True).
Lemma NZP_CSI_RS_ResourceSet__repetition__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NZP_CSI_RS_ResourceSet__repetition__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 NZP_CSI_RS_ResourceSet__repetition__nat__helper.

Definition NZP_CSI_RS_ResourceSet__repetition__F1 t :=
  match t with
  | NZP_CSI_RS_ResourceSet__repetition__on => 0
  | NZP_CSI_RS_ResourceSet__repetition__off => 1
  end.
Definition NZP_CSI_RS_ResourceSet__repetition__F2 n :=
  match n with
  | 0 => NZP_CSI_RS_ResourceSet__repetition__on
  | 1 => NZP_CSI_RS_ResourceSet__repetition__off
  | _ => NZP_CSI_RS_ResourceSet__repetition__on
  end.
Lemma NZP_CSI_RS_ResourceSet__repetition__F1F2 : forall x : NZP_CSI_RS_ResourceSet__repetition__Type, (NZP_CSI_RS_ResourceSet__repetition__F1 x <= 1) /\ NZP_CSI_RS_ResourceSet__repetition__F2 (NZP_CSI_RS_ResourceSet__repetition__F1 x) = x. imp_solve. Qed.
Lemma NZP_CSI_RS_ResourceSet__repetition__F2F1 : forall (y : nat) (H : y <= 1), NZP_CSI_RS_ResourceSet__repetition__F1 (NZP_CSI_RS_ResourceSet__repetition__F2 y) = y. enum_solve H y. Qed.

Lemma NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__helper1 : (0 <= 6)%Z.  lia. Qed.
Lemma NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__helper2 : to_bit_sz (Z.to_nat (6 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__Type := Z.
Definition NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__cond := (fun z => (0 <= z <= 6)%Z).
Inductive NZP_CSI_RS_ResourceSet__trs_Info__Type : Set :=
 | NZP_CSI_RS_ResourceSet__trs_Info__true
.
Definition NZP_CSI_RS_ResourceSet__trs_Info__cond := (fun (_ : NZP_CSI_RS_ResourceSet__trs_Info__Type) => True).
Lemma NZP_CSI_RS_ResourceSet__trs_Info__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NZP_CSI_RS_ResourceSet__trs_Info__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NZP_CSI_RS_ResourceSet__trs_Info__nat__helper.

Definition NZP_CSI_RS_ResourceSet__trs_Info__F1 t :=
  match t with
  | NZP_CSI_RS_ResourceSet__trs_Info__true => 0
  end.
Definition NZP_CSI_RS_ResourceSet__trs_Info__F2 n :=
  match n with
  | 0 => NZP_CSI_RS_ResourceSet__trs_Info__true
  | _ => NZP_CSI_RS_ResourceSet__trs_Info__true
  end.
Lemma NZP_CSI_RS_ResourceSet__trs_Info__F1F2 : forall x : NZP_CSI_RS_ResourceSet__trs_Info__Type, (NZP_CSI_RS_ResourceSet__trs_Info__F1 x <= 0) /\ NZP_CSI_RS_ResourceSet__trs_Info__F2 (NZP_CSI_RS_ResourceSet__trs_Info__F1 x) = x. imp_solve. Qed.
Lemma NZP_CSI_RS_ResourceSet__trs_Info__F2F1 : forall (y : nat) (H : y <= 0), NZP_CSI_RS_ResourceSet__trs_Info__F1 (NZP_CSI_RS_ResourceSet__trs_Info__F2 y) = y. enum_solve H y. Qed.

Lemma NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__Type := Z.
Definition NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__cond := (fun z => (0 <= z <= 31)%Z).
Record NZP_CSI_RS_ResourceSet__ext0O__Type : Set :=
  make__NZP_CSI_RS_ResourceSet__ext0O__Type {
    NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16 : option Z ;
}.
Definition NZP_CSI_RS_ResourceSet__ext0O__list := (
 Opt Z NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__cond ::
 nil).
Definition NZP_CSI_RS_ResourceSet__ext0O__cond z := 
  opt_cond NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__cond (NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16 z) /\
  True.

Definition NZP_CSI_RS_ResourceSet__ext0__Type := NZP_CSI_RS_ResourceSet__ext0O__Type.
Definition NZP_CSI_RS_ResourceSet__ext0__cond := NZP_CSI_RS_ResourceSet__ext0O__cond.

Inductive NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Type : Set :=
 | NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__true
.
Definition NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__cond := (fun (_ : NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Type) => True).
Lemma NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__nat__helper.

Definition NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1 t :=
  match t with
  | NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__true => 0
  end.
Definition NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F2 n :=
  match n with
  | 0 => NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__true
  | _ => NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__true
  end.
Lemma NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1F2 : forall x : NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Type, (NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1 x <= 0) /\ NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F2 (NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1 x) = x. imp_solve. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F2F1 : forall (y : nat) (H : y <= 0), NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1 (NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CMRGroupingAndPairing_r17.

Opaque CMRGroupingAndPairing_r17__cond CMRGroupingAndPairing_r17__Format.

Lemma NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__helper1 : (0 <= 124)%Z.  lia. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__helper2 : to_bit_sz (Z.to_nat (124 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (124 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__Type := Z.
Definition NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__cond := (fun z => (0 <= z <= 124)%Z).
Lemma NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__Type := Z.
Definition NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__cond := (fun z => (0 <= z <= 31)%Z).
Record NZP_CSI_RS_ResourceSet__ext1O__Type : Set :=
  make__NZP_CSI_RS_ResourceSet__ext1O__Type {
    NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17 : option NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Type ;
    NZP_CSI_RS_ResourceSet__ext1O__cmrGroupingAndPairing_r17 : option CMRGroupingAndPairing_r17__Type ;
    NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17 : option Z ;
    NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17 : option Z ;
}.
Definition NZP_CSI_RS_ResourceSet__ext1O__list := (
 Opt NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Type NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__cond ::
 Opt CMRGroupingAndPairing_r17__Type CMRGroupingAndPairing_r17__cond ::
 Opt Z NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__cond ::
 Opt Z NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__cond ::
 nil).
Definition NZP_CSI_RS_ResourceSet__ext1O__cond z := 
  opt_cond NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__cond (NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17 z) /\
  opt_cond CMRGroupingAndPairing_r17__cond (NZP_CSI_RS_ResourceSet__ext1O__cmrGroupingAndPairing_r17 z) /\
  opt_cond NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__cond (NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17 z) /\
  opt_cond NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__cond (NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17 z) /\
  True.

Definition NZP_CSI_RS_ResourceSet__ext1__Type := NZP_CSI_RS_ResourceSet__ext1O__Type.
Definition NZP_CSI_RS_ResourceSet__ext1__cond := NZP_CSI_RS_ResourceSet__ext1O__cond.

Record NZP_CSI_RS_ResourceSet__Type : Set :=
  make__NZP_CSI_RS_ResourceSet__Type {
    NZP_CSI_RS_ResourceSet__nzp_CSI_ResourceSetId : NZP_CSI_RS_ResourceSetId__Type ;
    NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources : NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Type ;
    NZP_CSI_RS_ResourceSet__repetition : option NZP_CSI_RS_ResourceSet__repetition__Type ;
    NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset : option Z ;
    NZP_CSI_RS_ResourceSet__trs_Info : option NZP_CSI_RS_ResourceSet__trs_Info__Type ;
    NZP_CSI_RS_ResourceSet__ext0 : option NZP_CSI_RS_ResourceSet__ext0__Type ;
    NZP_CSI_RS_ResourceSet__ext1 : option NZP_CSI_RS_ResourceSet__ext1__Type ;
}.
Definition NZP_CSI_RS_ResourceSet__root_list : list seq_elem := (
 Nor NZP_CSI_RS_ResourceSetId__Type NZP_CSI_RS_ResourceSetId__cond ::
 Nor NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Type NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__cond ::
 Opt NZP_CSI_RS_ResourceSet__repetition__Type NZP_CSI_RS_ResourceSet__repetition__cond ::
 Opt Z NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__cond ::
 Opt NZP_CSI_RS_ResourceSet__trs_Info__Type NZP_CSI_RS_ResourceSet__trs_Info__cond ::
 nil).
Definition NZP_CSI_RS_ResourceSet__ext_list : list typ := (
  typ_cons NZP_CSI_RS_ResourceSet__ext0__Type NZP_CSI_RS_ResourceSet__ext0__cond ::
  typ_cons NZP_CSI_RS_ResourceSet__ext1__Type NZP_CSI_RS_ResourceSet__ext1__cond ::
  nil).
Definition NZP_CSI_RS_ResourceSet__cond (z : NZP_CSI_RS_ResourceSet__Type) := 
(  NZP_CSI_RS_ResourceSetId__cond (NZP_CSI_RS_ResourceSet__nzp_CSI_ResourceSetId z) /\
  NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__cond (NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources z) /\
  opt_cond NZP_CSI_RS_ResourceSet__repetition__cond (NZP_CSI_RS_ResourceSet__repetition z) /\
  opt_cond NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__cond (NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset z) /\
  opt_cond NZP_CSI_RS_ResourceSet__trs_Info__cond (NZP_CSI_RS_ResourceSet__trs_Info z) /\
  True) /\ 
(  opt_cond NZP_CSI_RS_ResourceSet__ext0__cond (NZP_CSI_RS_ResourceSet__ext0 z) /\
  opt_cond NZP_CSI_RS_ResourceSet__ext1__cond (NZP_CSI_RS_ResourceSet__ext1 z) /\
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
Definition NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Format : T_Format NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Type NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__cond := seq_of_format NZP_CSI_RS_ResourceId__Format 1 maxNrofNZP_CSI_RS_ResourcesPerSet NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__helper1 NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__helper2.

Opaque NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__cond NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Format.

Definition NZP_CSI_RS_ResourceSet__repetition__Format : T_Format NZP_CSI_RS_ResourceSet__repetition__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NZP_CSI_RS_ResourceSet__repetition__nat__Format NZP_CSI_RS_ResourceSet__repetition__F1 NZP_CSI_RS_ResourceSet__repetition__F2 NZP_CSI_RS_ResourceSet__repetition__F1F2 NZP_CSI_RS_ResourceSet__repetition__F2F1.

Opaque NZP_CSI_RS_ResourceSet__repetition__cond NZP_CSI_RS_ResourceSet__repetition__Format.

Definition NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__Format : T_Format Z NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__cond :=
 ranged_int_format (0) (6) NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__helper1 NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__helper2.

Opaque NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__cond NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__Format.

Definition NZP_CSI_RS_ResourceSet__trs_Info__Format : T_Format NZP_CSI_RS_ResourceSet__trs_Info__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NZP_CSI_RS_ResourceSet__trs_Info__nat__Format NZP_CSI_RS_ResourceSet__trs_Info__F1 NZP_CSI_RS_ResourceSet__trs_Info__F2 NZP_CSI_RS_ResourceSet__trs_Info__F1F2 NZP_CSI_RS_ResourceSet__trs_Info__F2F1.

Opaque NZP_CSI_RS_ResourceSet__trs_Info__cond NZP_CSI_RS_ResourceSet__trs_Info__Format.

Definition NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__Format : T_Format Z NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__cond :=
 ranged_int_format (0) (31) NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__helper1 NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__helper2.

Opaque NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__cond NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__Format.


Definition NZP_CSI_RS_ResourceSet__ext0O__Format_Type := Eval cbn in seq_format_prod NZP_CSI_RS_ResourceSet__ext0O__list.
Definition NZP_CSI_RS_ResourceSet__ext0O__Format_list : NZP_CSI_RS_ResourceSet__ext0O__Format_Type :=
  (NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16__Format, unit_format).
Definition NZP_CSI_RS_ResourceSet__ext0O__list__Format := (*Eval compute in *) seq_format NZP_CSI_RS_ResourceSet__ext0O__list NZP_CSI_RS_ResourceSet__ext0O__Format_list.
Definition NZP_CSI_RS_ResourceSet__ext0O__F1 z :=
  (NZP_CSI_RS_ResourceSet__ext0O__aperiodicTriggeringOffset_r16 z, tt).
Definition NZP_CSI_RS_ResourceSet__ext0O__F2 (y : seq_type NZP_CSI_RS_ResourceSet__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__NZP_CSI_RS_ResourceSet__ext0O__Type i0
  end.
Lemma NZP_CSI_RS_ResourceSet__ext0O__F1F2_cond (z : NZP_CSI_RS_ResourceSet__ext0O__Type)
  : NZP_CSI_RS_ResourceSet__ext0O__cond z ->
  (seq_cond NZP_CSI_RS_ResourceSet__ext0O__list (NZP_CSI_RS_ResourceSet__ext0O__F1 z)).
intro H. unfold NZP_CSI_RS_ResourceSet__ext0O__cond in H. simpl. auto. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext0O__F1F2_cond2 (z : NZP_CSI_RS_ResourceSet__ext0O__Type)
 : NZP_CSI_RS_ResourceSet__ext0O__F2 (NZP_CSI_RS_ResourceSet__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext0O__F2F1_cond (y : seq_type NZP_CSI_RS_ResourceSet__ext0O__list)
  : seq_cond NZP_CSI_RS_ResourceSet__ext0O__list y ->
 (NZP_CSI_RS_ResourceSet__ext0O__cond (NZP_CSI_RS_ResourceSet__ext0O__F2 y)) /\  NZP_CSI_RS_ResourceSet__ext0O__F1 (NZP_CSI_RS_ResourceSet__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NZP_CSI_RS_ResourceSet__ext0O__cond. simpl in *. auto.
 - simpl. unfold NZP_CSI_RS_ResourceSet__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NZP_CSI_RS_ResourceSet__ext0O__Format : T_Format NZP_CSI_RS_ResourceSet__ext0O__Type NZP_CSI_RS_ResourceSet__ext0O__cond :=
        proj2_format  NZP_CSI_RS_ResourceSet__ext0O__cond NZP_CSI_RS_ResourceSet__ext0O__list__Format
    NZP_CSI_RS_ResourceSet__ext0O__F1 NZP_CSI_RS_ResourceSet__ext0O__F2 NZP_CSI_RS_ResourceSet__ext0O__F1F2_cond  NZP_CSI_RS_ResourceSet__ext0O__F1F2_cond2 NZP_CSI_RS_ResourceSet__ext0O__F2F1_cond.
Opaque NZP_CSI_RS_ResourceSet__ext0O__cond NZP_CSI_RS_ResourceSet__ext0O__Format.

Definition NZP_CSI_RS_ResourceSet__ext0__check_all_none (b : NZP_CSI_RS_ResourceSet__ext0O__Type) : bool :=
match b with 
  | make__NZP_CSI_RS_ResourceSet__ext0O__Type None  => false 
  | _ => true 
 end.
Definition NZP_CSI_RS_ResourceSet__ext0__Format : T_Format NZP_CSI_RS_ResourceSet__ext0__Type NZP_CSI_RS_ResourceSet__ext0__cond :=
  restrict_add_format NZP_CSI_RS_ResourceSet__ext0__check_all_none NZP_CSI_RS_ResourceSet__ext0O__Format.

Opaque NZP_CSI_RS_ResourceSet__ext0__cond NZP_CSI_RS_ResourceSet__ext0__Format.

Definition NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Format : T_Format NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__nat__Format NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1 NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F2 NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F1F2 NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__F2F1.

Opaque NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__cond NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Format.

Definition NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__Format : T_Format Z NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__cond :=
 ranged_int_format (0) (124) NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__helper1 NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__helper2.

Opaque NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__cond NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__Format.

Definition NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__Format : T_Format Z NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__cond :=
 ranged_int_format (0) (31) NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__helper1 NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__helper2.

Opaque NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__cond NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__Format.


Definition NZP_CSI_RS_ResourceSet__ext1O__Format_Type := Eval cbn in seq_format_prod NZP_CSI_RS_ResourceSet__ext1O__list.
Definition NZP_CSI_RS_ResourceSet__ext1O__Format_list : NZP_CSI_RS_ResourceSet__ext1O__Format_Type :=
  (NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17__Format, (CMRGroupingAndPairing_r17__Format, (NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17__Format, (NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17__Format, unit_format)))).
Definition NZP_CSI_RS_ResourceSet__ext1O__list__Format := (*Eval compute in *) seq_format NZP_CSI_RS_ResourceSet__ext1O__list NZP_CSI_RS_ResourceSet__ext1O__Format_list.
Definition NZP_CSI_RS_ResourceSet__ext1O__F1 z :=
  (NZP_CSI_RS_ResourceSet__ext1O__pdc_Info_r17 z, (NZP_CSI_RS_ResourceSet__ext1O__cmrGroupingAndPairing_r17 z, (NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffset_r17 z, (NZP_CSI_RS_ResourceSet__ext1O__aperiodicTriggeringOffsetL2_r17 z, tt)))).
Definition NZP_CSI_RS_ResourceSet__ext1O__F2 (y : seq_type NZP_CSI_RS_ResourceSet__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__NZP_CSI_RS_ResourceSet__ext1O__Type i0 i1 i2 i3
  end.
Lemma NZP_CSI_RS_ResourceSet__ext1O__F1F2_cond (z : NZP_CSI_RS_ResourceSet__ext1O__Type)
  : NZP_CSI_RS_ResourceSet__ext1O__cond z ->
  (seq_cond NZP_CSI_RS_ResourceSet__ext1O__list (NZP_CSI_RS_ResourceSet__ext1O__F1 z)).
intro H. unfold NZP_CSI_RS_ResourceSet__ext1O__cond in H. simpl. auto. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext1O__F1F2_cond2 (z : NZP_CSI_RS_ResourceSet__ext1O__Type)
 : NZP_CSI_RS_ResourceSet__ext1O__F2 (NZP_CSI_RS_ResourceSet__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NZP_CSI_RS_ResourceSet__ext1O__F2F1_cond (y : seq_type NZP_CSI_RS_ResourceSet__ext1O__list)
  : seq_cond NZP_CSI_RS_ResourceSet__ext1O__list y ->
 (NZP_CSI_RS_ResourceSet__ext1O__cond (NZP_CSI_RS_ResourceSet__ext1O__F2 y)) /\  NZP_CSI_RS_ResourceSet__ext1O__F1 (NZP_CSI_RS_ResourceSet__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NZP_CSI_RS_ResourceSet__ext1O__cond. simpl in *. auto.
 - simpl. unfold NZP_CSI_RS_ResourceSet__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NZP_CSI_RS_ResourceSet__ext1O__Format : T_Format NZP_CSI_RS_ResourceSet__ext1O__Type NZP_CSI_RS_ResourceSet__ext1O__cond :=
        proj2_format  NZP_CSI_RS_ResourceSet__ext1O__cond NZP_CSI_RS_ResourceSet__ext1O__list__Format
    NZP_CSI_RS_ResourceSet__ext1O__F1 NZP_CSI_RS_ResourceSet__ext1O__F2 NZP_CSI_RS_ResourceSet__ext1O__F1F2_cond  NZP_CSI_RS_ResourceSet__ext1O__F1F2_cond2 NZP_CSI_RS_ResourceSet__ext1O__F2F1_cond.
Opaque NZP_CSI_RS_ResourceSet__ext1O__cond NZP_CSI_RS_ResourceSet__ext1O__Format.

Definition NZP_CSI_RS_ResourceSet__ext1__check_all_none (b : NZP_CSI_RS_ResourceSet__ext1O__Type) : bool :=
match b with 
  | make__NZP_CSI_RS_ResourceSet__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition NZP_CSI_RS_ResourceSet__ext1__Format : T_Format NZP_CSI_RS_ResourceSet__ext1__Type NZP_CSI_RS_ResourceSet__ext1__cond :=
  restrict_add_format NZP_CSI_RS_ResourceSet__ext1__check_all_none NZP_CSI_RS_ResourceSet__ext1O__Format.

Opaque NZP_CSI_RS_ResourceSet__ext1__cond NZP_CSI_RS_ResourceSet__ext1__Format.


Definition NZP_CSI_RS_ResourceSet__root_Format_Type := Eval cbn in seq_format_prod NZP_CSI_RS_ResourceSet__root_list.
Definition NZP_CSI_RS_ResourceSet__root_Format_list : NZP_CSI_RS_ResourceSet__root_Format_Type :=
  (NZP_CSI_RS_ResourceSetId__Format, (NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources__Format, (NZP_CSI_RS_ResourceSet__repetition__Format, (NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset__Format, (NZP_CSI_RS_ResourceSet__trs_Info__Format, unit_format))))).

Definition NZP_CSI_RS_ResourceSet__ext_Format_Type := Eval cbn in get_formats NZP_CSI_RS_ResourceSet__ext_list.
Definition NZP_CSI_RS_ResourceSet__ext_Format_list : NZP_CSI_RS_ResourceSet__ext_Format_Type :=
  (NZP_CSI_RS_ResourceSet__ext0__Format, (NZP_CSI_RS_ResourceSet__ext1__Format, unit__Format)).

Definition NZP_CSI_RS_ResourceSet__list_type : Set := (seq_type NZP_CSI_RS_ResourceSet__root_list) * (seq_ext_type NZP_CSI_RS_ResourceSet__ext_list).
Definition NZP_CSI_RS_ResourceSet__list_cond (z : NZP_CSI_RS_ResourceSet__list_type) : Prop :=
        (seq_cond NZP_CSI_RS_ResourceSet__root_list (fst z)) /\ (seq_ext_cond NZP_CSI_RS_ResourceSet__ext_list (snd z)).
Definition NZP_CSI_RS_ResourceSet__list_format : T_Format NZP_CSI_RS_ResourceSet__list_type NZP_CSI_RS_ResourceSet__list_cond :=
 (* Eval compute in *) seq_ext_format NZP_CSI_RS_ResourceSet__root_list NZP_CSI_RS_ResourceSet__root_Format_list NZP_CSI_RS_ResourceSet__ext_list NZP_CSI_RS_ResourceSet__ext_Format_list.

Opaque NZP_CSI_RS_ResourceSet__list_format.
Definition NZP_CSI_RS_ResourceSet__F1 (z : NZP_CSI_RS_ResourceSet__Type) : NZP_CSI_RS_ResourceSet__list_type :=
  (((NZP_CSI_RS_ResourceSet__nzp_CSI_ResourceSetId z, (NZP_CSI_RS_ResourceSet__nzp_CSI_RS_Resources z, (NZP_CSI_RS_ResourceSet__repetition z, (NZP_CSI_RS_ResourceSet__aperiodicTriggeringOffset z, (NZP_CSI_RS_ResourceSet__trs_Info z, tt)))))), (
(NZP_CSI_RS_ResourceSet__ext0 z, (NZP_CSI_RS_ResourceSet__ext1 z, tt)))).
Definition NZP_CSI_RS_ResourceSet__F2 (y : NZP_CSI_RS_ResourceSet__list_type) : NZP_CSI_RS_ResourceSet__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, _)))=>
    make__NZP_CSI_RS_ResourceSet__Type j0 j1 j2 j3 j4 i0 i1
  end.
Definition NZP_CSI_RS_ResourceSet__helper1 : (forall a : NZP_CSI_RS_ResourceSet__Type, NZP_CSI_RS_ResourceSet__cond a -> NZP_CSI_RS_ResourceSet__list_cond (NZP_CSI_RS_ResourceSet__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NZP_CSI_RS_ResourceSet__helper2 : (forall a : NZP_CSI_RS_ResourceSet__Type, NZP_CSI_RS_ResourceSet__F2 (NZP_CSI_RS_ResourceSet__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NZP_CSI_RS_ResourceSet__helper3 : (forall b : NZP_CSI_RS_ResourceSet__list_type, NZP_CSI_RS_ResourceSet__list_cond b -> NZP_CSI_RS_ResourceSet__cond (NZP_CSI_RS_ResourceSet__F2 b) /\ NZP_CSI_RS_ResourceSet__F1 (NZP_CSI_RS_ResourceSet__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NZP_CSI_RS_ResourceSet__cond, NZP_CSI_RS_ResourceSet__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NZP_CSI_RS_ResourceSet__Format : T_Format NZP_CSI_RS_ResourceSet__Type NZP_CSI_RS_ResourceSet__cond :=
 proj2_format NZP_CSI_RS_ResourceSet__cond NZP_CSI_RS_ResourceSet__list_format  NZP_CSI_RS_ResourceSet__F1 NZP_CSI_RS_ResourceSet__F2 NZP_CSI_RS_ResourceSet__helper1 NZP_CSI_RS_ResourceSet__helper2 NZP_CSI_RS_ResourceSet__helper3.

Opaque NZP_CSI_RS_ResourceSet__cond NZP_CSI_RS_ResourceSet__Format.

