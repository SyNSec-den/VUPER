Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__Type := Z.
Definition CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__cond := (fun z => (1 <= z <= 64)%Z).
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Type := bit_string_fixed.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Type := bit_string_fixed.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Type := bit_string_fixed.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 64 /\ bit_string_len_prop (fst z) (snd z)).

Inductive CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type : Set :=
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17 : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Type -> CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17 : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Type -> CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17 : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Type -> CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type
.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list : list typ := (
typ_cons CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__cond ::
typ_cons CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__cond ::
typ_cons CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__cond ::
 nil).
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond (c : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type) := 
  match c with
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17 t => CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__cond t 
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17 t => CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__cond t 
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17 t => CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__cond t 
  end.

Lemma CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__len_helper1 : to_bit_sz (length CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__len_helper2 : 2 <= length2 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list.
 simpl. lia. Qed.
Inductive CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Type : Set :=
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneEighth
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneFourth
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__half
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__one
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__two
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__four
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__eight
 | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__sixteen
.
Definition CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__cond := (fun (_ : CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Type) => True).
Lemma CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__nat__helper.

Definition CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1 t :=
  match t with
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneEighth => 0
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneFourth => 1
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__half => 2
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__one => 3
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__two => 4
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__four => 5
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__eight => 6
  | CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__sixteen => 7
  end.
Definition CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F2 n :=
  match n with
  | 0 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneEighth
  | 1 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneFourth
  | 2 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__half
  | 3 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__one
  | 4 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__two
  | 5 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__four
  | 6 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__eight
  | 7 => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__sixteen
  | _ => CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__oneEighth
  end.
Lemma CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1F2 : forall x : CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Type, (CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1 x <= 7) /\ CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F2 (CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F2F1 : forall (y : nat) (H : y <= 7), CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1 (CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Lemma CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__Type := Z.
Definition CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__cond := (fun z => (-16 <= z <= 15)%Z).
Inductive CG_SDT_Configuration_r17__sdt_Alpha_r17__Type : Set :=
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha0
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha04
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha05
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha06
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha07
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha08
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha09
 | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha1
.
Definition CG_SDT_Configuration_r17__sdt_Alpha_r17__cond := (fun (_ : CG_SDT_Configuration_r17__sdt_Alpha_r17__Type) => True).
Lemma CG_SDT_Configuration_r17__sdt_Alpha_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_SDT_Configuration_r17__sdt_Alpha_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CG_SDT_Configuration_r17__sdt_Alpha_r17__nat__helper.

Definition CG_SDT_Configuration_r17__sdt_Alpha_r17__F1 t :=
  match t with
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha0 => 0
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha04 => 1
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha05 => 2
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha06 => 3
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha07 => 4
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha08 => 5
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha09 => 6
  | CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha1 => 7
  end.
Definition CG_SDT_Configuration_r17__sdt_Alpha_r17__F2 n :=
  match n with
  | 0 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha0
  | 1 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha04
  | 2 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha05
  | 3 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha06
  | 4 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha07
  | 5 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha08
  | 6 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha09
  | 7 => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha1
  | _ => CG_SDT_Configuration_r17__sdt_Alpha_r17__alpha0
  end.
Lemma CG_SDT_Configuration_r17__sdt_Alpha_r17__F1F2 : forall x : CG_SDT_Configuration_r17__sdt_Alpha_r17__Type, (CG_SDT_Configuration_r17__sdt_Alpha_r17__F1 x <= 7) /\ CG_SDT_Configuration_r17__sdt_Alpha_r17__F2 (CG_SDT_Configuration_r17__sdt_Alpha_r17__F1 x) = x. imp_solve. Qed.
Lemma CG_SDT_Configuration_r17__sdt_Alpha_r17__F2F1 : forall (y : nat) (H : y <= 7), CG_SDT_Configuration_r17__sdt_Alpha_r17__F1 (CG_SDT_Configuration_r17__sdt_Alpha_r17__F2 y) = y. enum_solve H y. Qed.

Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Type := bit_string_fixed.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Type := bit_string_fixed.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 12 /\ bit_string_len_prop (fst z) (snd z)).

Inductive CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type : Set :=
  | CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17 : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Type -> CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type
  | CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17 : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Type -> CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type
.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list : list typ := (
typ_cons CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Type CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__cond ::
typ_cons CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Type CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__cond ::
 nil).
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond (c : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type) := 
  match c with
  | CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17 t => CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__cond t 
  | CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17 t => CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__cond t 
  end.

Lemma CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__len_helper1 : to_bit_sz (length CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__len_helper2 : 2 <= length2 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list.
 simpl. lia. Qed.
Lemma CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__Type := Z.
Definition CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__cond := (fun z => (1 <= z <= 2)%Z).
Record CG_SDT_Configuration_r17__Type : Set :=
  make__CG_SDT_Configuration_r17__Type {
    CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer : option Z ;
    CG_SDT_Configuration_r17__sdt_SSB_Subset_r17 : option CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type ;
    CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17 : option CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Type ;
    CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17 : option Z ;
    CG_SDT_Configuration_r17__sdt_Alpha_r17 : option CG_SDT_Configuration_r17__sdt_Alpha_r17__Type ;
    CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17 : option CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type ;
    CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17 : option Z ;
}.
Definition CG_SDT_Configuration_r17__list := (
 Opt Z CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__cond ::
 Opt CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond ::
 Opt CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Type CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__cond ::
 Opt Z CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__cond ::
 Opt CG_SDT_Configuration_r17__sdt_Alpha_r17__Type CG_SDT_Configuration_r17__sdt_Alpha_r17__cond ::
 Opt CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond ::
 Opt Z CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__cond ::
 nil).
Definition CG_SDT_Configuration_r17__cond z := 
  opt_cond CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__cond (CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer z) /\
  opt_cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17 z) /\
  opt_cond CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__cond (CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17 z) /\
  opt_cond CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__cond (CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17 z) /\
  opt_cond CG_SDT_Configuration_r17__sdt_Alpha_r17__cond (CG_SDT_Configuration_r17__sdt_Alpha_r17 z) /\
  opt_cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17 z) /\
  opt_cond CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__cond (CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17 z) /\
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
Definition CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__Format : T_Format Z CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__cond :=
 ranged_int_format (1) (64) CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__helper1 CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__helper2.

Opaque CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__cond CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__Format.

Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__cond := (* Eval compute in *) bit_string_fixed_format 64.
Opaque CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Format.


Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format_Type := Eval cbn in get_formats CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format_list : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format_Type :=
  (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Format, (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Format, (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Format, unit__Format))).
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list__Format := Eval compute in choice_format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__len_helper1 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__len_helper2  CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format_list.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F1 (z : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type) : (choice CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list) :=
  match z with
   | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17 t => existT _ 0 t
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17 t => existT _ 1 t
  | CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17 t => existT _ 2 t
  end.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__g := (fun n => typ_set (get_nth_typ CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list n)).
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F2 (y : choice CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list) : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__g n -> CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type) with
    | 0 => fun (t : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17__Type) => CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__shortBitmap_r17 t 
    | 1 => fun (t : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17__Type) => CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__mediumBitmap_r17 t 
    | 2 => fun (t : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17__Type) => CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__longBitmap_r17 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type with end) n0
           end t0).

Lemma CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__helper2 :  forall (y : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type), CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond y -> choice_cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__helper3 :  forall (y : CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type), CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F2 (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__helper4 : (forall b : choice CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list, choice_cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list b -> CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F2 b) /\ CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F1 (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F1 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F2.
Definition CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Type CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond :=
  (* Eval compute in *) proj2_format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__list__Format CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F1 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__F2 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__helper2 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__helper3 CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__helper4.
Opaque CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__cond CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__nat__Format CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1 CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F2 CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F1F2 CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__F2F1.

Opaque CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__cond CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__Format : T_Format Z CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__cond :=
 ranged_int_format (-16) (15) CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__helper1 CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__helper2.

Opaque CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__cond CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_Alpha_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_Alpha_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_SDT_Configuration_r17__sdt_Alpha_r17__nat__Format CG_SDT_Configuration_r17__sdt_Alpha_r17__F1 CG_SDT_Configuration_r17__sdt_Alpha_r17__F2 CG_SDT_Configuration_r17__sdt_Alpha_r17__F1F2 CG_SDT_Configuration_r17__sdt_Alpha_r17__F2F1.

Opaque CG_SDT_Configuration_r17__sdt_Alpha_r17__cond CG_SDT_Configuration_r17__sdt_Alpha_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Type CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Type CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__cond := (* Eval compute in *) bit_string_fixed_format 12.
Opaque CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Format.


Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format_Type := Eval cbn in get_formats CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format_list : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format_Type :=
  (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Format, (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Format, unit__Format)).
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list__Format := Eval compute in choice_format CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__len_helper1 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__len_helper2  CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format_list.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F1 (z : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type) : (choice CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list) :=
  match z with
   | CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17 t => existT _ 0 t
  | CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17 t => existT _ 1 t
  end.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__g := (fun n => typ_set (get_nth_typ CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list n)).
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F2 (y : choice CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list) : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__g n -> CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type) with
    | 0 => fun (t : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17__Type) => CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType1_r17 t 
    | 1 => fun (t : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17__Type) => CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__dmrsType2_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type with end) n0
           end t0).

Lemma CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__helper2 :  forall (y : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type), CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond y -> choice_cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__helper3 :  forall (y : CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type), CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F2 (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__helper4 : (forall b : choice CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list, choice_cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list b -> CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F2 b) /\ CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F1 (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F1 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F2.
Definition CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format : T_Format CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Type CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond :=
  (* Eval compute in *) proj2_format CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__list__Format CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F1 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__F2 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__helper2 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__helper3 CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__helper4.
Opaque CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__cond CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format.

Definition CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__Format : T_Format Z CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__cond :=
 ranged_int_format (1) (2) CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__helper1 CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__helper2.

Opaque CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__cond CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__Format.


Definition CG_SDT_Configuration_r17__Format_Type := Eval cbn in seq_format_prod CG_SDT_Configuration_r17__list.
Definition CG_SDT_Configuration_r17__Format_list : CG_SDT_Configuration_r17__Format_Type :=
  (CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer__Format, (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17__Format, (CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17__Format, (CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17__Format, (CG_SDT_Configuration_r17__sdt_Alpha_r17__Format, (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17__Format, (CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17__Format, unit_format))))))).
Definition CG_SDT_Configuration_r17__list__Format := (*Eval compute in *) seq_format CG_SDT_Configuration_r17__list CG_SDT_Configuration_r17__Format_list.
Definition CG_SDT_Configuration_r17__F1 z :=
  (CG_SDT_Configuration_r17__cg_SDT_RetransmissionTimer z, (CG_SDT_Configuration_r17__sdt_SSB_Subset_r17 z, (CG_SDT_Configuration_r17__sdt_SSB_PerCG_PUSCH_r17 z, (CG_SDT_Configuration_r17__sdt_P0_PUSCH_r17 z, (CG_SDT_Configuration_r17__sdt_Alpha_r17 z, (CG_SDT_Configuration_r17__sdt_DMRS_Ports_r17 z, (CG_SDT_Configuration_r17__sdt_NrofDMRS_Sequences_r17 z, tt))))))).
Definition CG_SDT_Configuration_r17__F2 (y : seq_type CG_SDT_Configuration_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__CG_SDT_Configuration_r17__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma CG_SDT_Configuration_r17__F1F2_cond (z : CG_SDT_Configuration_r17__Type)
  : CG_SDT_Configuration_r17__cond z ->
  (seq_cond CG_SDT_Configuration_r17__list (CG_SDT_Configuration_r17__F1 z)).
intro H. unfold CG_SDT_Configuration_r17__cond in H. simpl. auto. Qed.
Lemma CG_SDT_Configuration_r17__F1F2_cond2 (z : CG_SDT_Configuration_r17__Type)
 : CG_SDT_Configuration_r17__F2 (CG_SDT_Configuration_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_SDT_Configuration_r17__F2F1_cond (y : seq_type CG_SDT_Configuration_r17__list)
  : seq_cond CG_SDT_Configuration_r17__list y ->
 (CG_SDT_Configuration_r17__cond (CG_SDT_Configuration_r17__F2 y)) /\  CG_SDT_Configuration_r17__F1 (CG_SDT_Configuration_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_SDT_Configuration_r17__cond. simpl in *. auto.
 - simpl. unfold CG_SDT_Configuration_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_SDT_Configuration_r17__Format : T_Format CG_SDT_Configuration_r17__Type CG_SDT_Configuration_r17__cond :=
        proj2_format  CG_SDT_Configuration_r17__cond CG_SDT_Configuration_r17__list__Format
    CG_SDT_Configuration_r17__F1 CG_SDT_Configuration_r17__F2 CG_SDT_Configuration_r17__F1F2_cond  CG_SDT_Configuration_r17__F1F2_cond2 CG_SDT_Configuration_r17__F2F1_cond.
Opaque CG_SDT_Configuration_r17__cond CG_SDT_Configuration_r17__Format.

