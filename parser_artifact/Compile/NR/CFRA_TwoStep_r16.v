Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RACH_ConfigGenericTwoStepRA_r16.

Opaque RACH_ConfigGenericTwoStepRA_r16__cond RACH_ConfigGenericTwoStepRA_r16__Format.

Inductive CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Type : Set :=
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneEighth
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneFourth
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneHalf
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__one
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__two
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__four
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__eight
 | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__sixteen
.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__cond := (fun (_ : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Type) => True).
Lemma CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__nat__helper.

Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1 t :=
  match t with
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneEighth => 0
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneFourth => 1
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneHalf => 2
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__one => 3
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__two => 4
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__four => 5
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__eight => 6
  | CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__sixteen => 7
  end.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F2 n :=
  match n with
  | 0 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneEighth
  | 1 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneFourth
  | 2 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneHalf
  | 3 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__one
  | 4 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__two
  | 5 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__four
  | 6 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__eight
  | 7 => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__sixteen
  | _ => CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__oneEighth
  end.
Lemma CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1F2 : forall x : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Type, (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1 x <= 7) /\ CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F2 (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1 x) = x. imp_solve. Qed.
Lemma CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F2F1 : forall (y : nat) (H : y <= 7), CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1 (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F2 y) = y. enum_solve H y. Qed.

Record CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type : Set :=
  make__CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type {
    CFRA_TwoStep_r16__occasionsTwoStepRA_r16__rach_ConfigGenericTwoStepRA_r16 : RACH_ConfigGenericTwoStepRA_r16__Type ;
    CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16 : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Type ;
}.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list := (
 Nor RACH_ConfigGenericTwoStepRA_r16__Type RACH_ConfigGenericTwoStepRA_r16__cond ::
 Nor CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Type CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__cond ::
 nil).
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond z := 
  RACH_ConfigGenericTwoStepRA_r16__cond (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__rach_ConfigGenericTwoStepRA_r16 z) /\
  CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__cond (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16 z) /\
  True.

Require Import NR.MsgA_PUSCH_Resource_r16.

Opaque MsgA_PUSCH_Resource_r16__cond MsgA_PUSCH_Resource_r16__Format.

Inductive CFRA_TwoStep_r16__msgA_TransMax_r16__Type : Set :=
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n1
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n2
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n4
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n6
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n8
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n10
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n20
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n50
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n100
 | CFRA_TwoStep_r16__msgA_TransMax_r16__n200
.
Definition CFRA_TwoStep_r16__msgA_TransMax_r16__cond := (fun (_ : CFRA_TwoStep_r16__msgA_TransMax_r16__Type) => True).
Lemma CFRA_TwoStep_r16__msgA_TransMax_r16__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CFRA_TwoStep_r16__msgA_TransMax_r16__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 CFRA_TwoStep_r16__msgA_TransMax_r16__nat__helper.

Definition CFRA_TwoStep_r16__msgA_TransMax_r16__F1 t :=
  match t with
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n1 => 0
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n2 => 1
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n4 => 2
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n6 => 3
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n8 => 4
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n10 => 5
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n20 => 6
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n50 => 7
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n100 => 8
  | CFRA_TwoStep_r16__msgA_TransMax_r16__n200 => 9
  end.
Definition CFRA_TwoStep_r16__msgA_TransMax_r16__F2 n :=
  match n with
  | 0 => CFRA_TwoStep_r16__msgA_TransMax_r16__n1
  | 1 => CFRA_TwoStep_r16__msgA_TransMax_r16__n2
  | 2 => CFRA_TwoStep_r16__msgA_TransMax_r16__n4
  | 3 => CFRA_TwoStep_r16__msgA_TransMax_r16__n6
  | 4 => CFRA_TwoStep_r16__msgA_TransMax_r16__n8
  | 5 => CFRA_TwoStep_r16__msgA_TransMax_r16__n10
  | 6 => CFRA_TwoStep_r16__msgA_TransMax_r16__n20
  | 7 => CFRA_TwoStep_r16__msgA_TransMax_r16__n50
  | 8 => CFRA_TwoStep_r16__msgA_TransMax_r16__n100
  | 9 => CFRA_TwoStep_r16__msgA_TransMax_r16__n200
  | _ => CFRA_TwoStep_r16__msgA_TransMax_r16__n1
  end.
Lemma CFRA_TwoStep_r16__msgA_TransMax_r16__F1F2 : forall x : CFRA_TwoStep_r16__msgA_TransMax_r16__Type, (CFRA_TwoStep_r16__msgA_TransMax_r16__F1 x <= 9) /\ CFRA_TwoStep_r16__msgA_TransMax_r16__F2 (CFRA_TwoStep_r16__msgA_TransMax_r16__F1 x) = x. imp_solve. Qed.
Lemma CFRA_TwoStep_r16__msgA_TransMax_r16__F2F1 : forall (y : nat) (H : y <= 9), CFRA_TwoStep_r16__msgA_TransMax_r16__F1 (CFRA_TwoStep_r16__msgA_TransMax_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CFRA_SSB_Resource.

Opaque CFRA_SSB_Resource__cond CFRA_SSB_Resource__Format.

Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Type := list CFRA_SSB_Resource__Type.

Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__helper1 : (0 <= 1 <= maxRA_SSB_Resources)%Z. unfold maxRA_SSB_Resources.
 lia. Qed.
Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxRA_SSB_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxRA_SSB_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__cond (z : CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxRA_SSB_Resources)%Z /\ (list_and CFRA_SSB_Resource__cond z) .

Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__Type := Z.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__cond := (fun z => (0 <= z <= 15)%Z).
Record CFRA_TwoStep_r16__resourcesTwoStep_r16__Type : Set :=
  make__CFRA_TwoStep_r16__resourcesTwoStep_r16__Type {
    CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList : CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Type ;
    CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex : Z ;
}.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__list := (
 Nor CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Type CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__cond ::
 Nor Z CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__cond ::
 nil).
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__cond z := 
  CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__cond (CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList z) /\
  CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__cond (CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex z) /\
  True.

Record CFRA_TwoStep_r16__Type : Set :=
  make__CFRA_TwoStep_r16__Type {
    CFRA_TwoStep_r16__occasionsTwoStepRA_r16 : option CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type ;
    CFRA_TwoStep_r16__msgA_CFRA_PUSCH_r16 : MsgA_PUSCH_Resource_r16__Type ;
    CFRA_TwoStep_r16__msgA_TransMax_r16 : option CFRA_TwoStep_r16__msgA_TransMax_r16__Type ;
    CFRA_TwoStep_r16__resourcesTwoStep_r16 : CFRA_TwoStep_r16__resourcesTwoStep_r16__Type ;
}.
Definition CFRA_TwoStep_r16__root_list : list seq_elem := (
 Opt CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond ::
 Nor MsgA_PUSCH_Resource_r16__Type MsgA_PUSCH_Resource_r16__cond ::
 Opt CFRA_TwoStep_r16__msgA_TransMax_r16__Type CFRA_TwoStep_r16__msgA_TransMax_r16__cond ::
 Nor CFRA_TwoStep_r16__resourcesTwoStep_r16__Type CFRA_TwoStep_r16__resourcesTwoStep_r16__cond ::
 nil).
Definition CFRA_TwoStep_r16__ext_list : list typ := (
  nil).
Definition CFRA_TwoStep_r16__cond (z : CFRA_TwoStep_r16__Type) := 
(  opt_cond CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond (CFRA_TwoStep_r16__occasionsTwoStepRA_r16 z) /\
  MsgA_PUSCH_Resource_r16__cond (CFRA_TwoStep_r16__msgA_CFRA_PUSCH_r16 z) /\
  opt_cond CFRA_TwoStep_r16__msgA_TransMax_r16__cond (CFRA_TwoStep_r16__msgA_TransMax_r16 z) /\
  CFRA_TwoStep_r16__resourcesTwoStep_r16__cond (CFRA_TwoStep_r16__resourcesTwoStep_r16 z) /\
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
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Format : T_Format CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__nat__Format CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F2 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F1F2 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__F2F1.

Opaque CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__cond CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Format.


Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format_Type := Eval cbn in seq_format_prod CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format_list : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format_Type :=
  (RACH_ConfigGenericTwoStepRA_r16__Format, (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16__Format, unit_format)).
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list__Format := (*Eval compute in *) seq_format CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format_list.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1 z :=
  (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__rach_ConfigGenericTwoStepRA_r16 z, (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__ssb_PerRACH_OccasionTwoStepRA_r16 z, tt)).
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2 (y : seq_type CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type i0 i1
  end.
Lemma CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1F2_cond (z : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type)
  : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond z ->
  (seq_cond CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1 z)).
intro H. unfold CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond in H. simpl. auto. Qed.
Lemma CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1F2_cond2 (z : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type)
 : CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2 (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2F1_cond (y : seq_type CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list)
  : seq_cond CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list y ->
 (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2 y)) /\  CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1 (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond. simpl in *. auto.
 - simpl. unfold CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format : T_Format CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Type CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond :=
        proj2_format  CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond CFRA_TwoStep_r16__occasionsTwoStepRA_r16__list__Format
    CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1F2_cond  CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F1F2_cond2 CFRA_TwoStep_r16__occasionsTwoStepRA_r16__F2F1_cond.
Opaque CFRA_TwoStep_r16__occasionsTwoStepRA_r16__cond CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format.

Definition CFRA_TwoStep_r16__msgA_TransMax_r16__Format : T_Format CFRA_TwoStep_r16__msgA_TransMax_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CFRA_TwoStep_r16__msgA_TransMax_r16__nat__Format CFRA_TwoStep_r16__msgA_TransMax_r16__F1 CFRA_TwoStep_r16__msgA_TransMax_r16__F2 CFRA_TwoStep_r16__msgA_TransMax_r16__F1F2 CFRA_TwoStep_r16__msgA_TransMax_r16__F2F1.

Opaque CFRA_TwoStep_r16__msgA_TransMax_r16__cond CFRA_TwoStep_r16__msgA_TransMax_r16__Format.

Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Format : T_Format CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Type CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__cond := seq_of_format CFRA_SSB_Resource__Format 1 maxRA_SSB_Resources CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__helper1 CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__helper2.

Opaque CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__cond CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Format.

Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__Format : T_Format Z CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__cond :=
 ranged_int_format (0) (15) CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__helper1 CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__helper2.

Opaque CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__cond CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__Format.


Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__Format_Type := Eval cbn in seq_format_prod CFRA_TwoStep_r16__resourcesTwoStep_r16__list.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__Format_list : CFRA_TwoStep_r16__resourcesTwoStep_r16__Format_Type :=
  (CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList__Format, (CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex__Format, unit_format)).
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__list__Format := (*Eval compute in *) seq_format CFRA_TwoStep_r16__resourcesTwoStep_r16__list CFRA_TwoStep_r16__resourcesTwoStep_r16__Format_list.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__F1 z :=
  (CFRA_TwoStep_r16__resourcesTwoStep_r16__ssb_ResourceList z, (CFRA_TwoStep_r16__resourcesTwoStep_r16__ra_ssb_OccasionMaskIndex z, tt)).
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__F2 (y : seq_type CFRA_TwoStep_r16__resourcesTwoStep_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CFRA_TwoStep_r16__resourcesTwoStep_r16__Type i0 i1
  end.
Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__F1F2_cond (z : CFRA_TwoStep_r16__resourcesTwoStep_r16__Type)
  : CFRA_TwoStep_r16__resourcesTwoStep_r16__cond z ->
  (seq_cond CFRA_TwoStep_r16__resourcesTwoStep_r16__list (CFRA_TwoStep_r16__resourcesTwoStep_r16__F1 z)).
intro H. unfold CFRA_TwoStep_r16__resourcesTwoStep_r16__cond in H. simpl. auto. Qed.
Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__F1F2_cond2 (z : CFRA_TwoStep_r16__resourcesTwoStep_r16__Type)
 : CFRA_TwoStep_r16__resourcesTwoStep_r16__F2 (CFRA_TwoStep_r16__resourcesTwoStep_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA_TwoStep_r16__resourcesTwoStep_r16__F2F1_cond (y : seq_type CFRA_TwoStep_r16__resourcesTwoStep_r16__list)
  : seq_cond CFRA_TwoStep_r16__resourcesTwoStep_r16__list y ->
 (CFRA_TwoStep_r16__resourcesTwoStep_r16__cond (CFRA_TwoStep_r16__resourcesTwoStep_r16__F2 y)) /\  CFRA_TwoStep_r16__resourcesTwoStep_r16__F1 (CFRA_TwoStep_r16__resourcesTwoStep_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA_TwoStep_r16__resourcesTwoStep_r16__cond. simpl in *. auto.
 - simpl. unfold CFRA_TwoStep_r16__resourcesTwoStep_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA_TwoStep_r16__resourcesTwoStep_r16__Format : T_Format CFRA_TwoStep_r16__resourcesTwoStep_r16__Type CFRA_TwoStep_r16__resourcesTwoStep_r16__cond :=
        proj2_format  CFRA_TwoStep_r16__resourcesTwoStep_r16__cond CFRA_TwoStep_r16__resourcesTwoStep_r16__list__Format
    CFRA_TwoStep_r16__resourcesTwoStep_r16__F1 CFRA_TwoStep_r16__resourcesTwoStep_r16__F2 CFRA_TwoStep_r16__resourcesTwoStep_r16__F1F2_cond  CFRA_TwoStep_r16__resourcesTwoStep_r16__F1F2_cond2 CFRA_TwoStep_r16__resourcesTwoStep_r16__F2F1_cond.
Opaque CFRA_TwoStep_r16__resourcesTwoStep_r16__cond CFRA_TwoStep_r16__resourcesTwoStep_r16__Format.


Definition CFRA_TwoStep_r16__root_Format_Type := Eval cbn in seq_format_prod CFRA_TwoStep_r16__root_list.
Definition CFRA_TwoStep_r16__root_Format_list : CFRA_TwoStep_r16__root_Format_Type :=
  (CFRA_TwoStep_r16__occasionsTwoStepRA_r16__Format, (MsgA_PUSCH_Resource_r16__Format, (CFRA_TwoStep_r16__msgA_TransMax_r16__Format, (CFRA_TwoStep_r16__resourcesTwoStep_r16__Format, unit_format)))).

Definition CFRA_TwoStep_r16__ext_Format_Type := Eval cbn in get_formats CFRA_TwoStep_r16__ext_list.
Definition CFRA_TwoStep_r16__ext_Format_list : CFRA_TwoStep_r16__ext_Format_Type :=
  unit__Format.

Definition CFRA_TwoStep_r16__list_type : Set := (seq_type CFRA_TwoStep_r16__root_list) * (seq_ext_type CFRA_TwoStep_r16__ext_list).
Definition CFRA_TwoStep_r16__list_cond (z : CFRA_TwoStep_r16__list_type) : Prop :=
        (seq_cond CFRA_TwoStep_r16__root_list (fst z)) /\ (seq_ext_cond CFRA_TwoStep_r16__ext_list (snd z)).
Definition CFRA_TwoStep_r16__list_format : T_Format CFRA_TwoStep_r16__list_type CFRA_TwoStep_r16__list_cond :=
 (* Eval compute in *) seq_ext_format CFRA_TwoStep_r16__root_list CFRA_TwoStep_r16__root_Format_list CFRA_TwoStep_r16__ext_list CFRA_TwoStep_r16__ext_Format_list.

Opaque CFRA_TwoStep_r16__list_format.
Definition CFRA_TwoStep_r16__F1 (z : CFRA_TwoStep_r16__Type) : CFRA_TwoStep_r16__list_type :=
  (((CFRA_TwoStep_r16__occasionsTwoStepRA_r16 z, (CFRA_TwoStep_r16__msgA_CFRA_PUSCH_r16 z, (CFRA_TwoStep_r16__msgA_TransMax_r16 z, (CFRA_TwoStep_r16__resourcesTwoStep_r16 z, tt))))), (
tt)).
Definition CFRA_TwoStep_r16__F2 (y : CFRA_TwoStep_r16__list_type) : CFRA_TwoStep_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__CFRA_TwoStep_r16__Type j0 j1 j2 j3
  end.
Definition CFRA_TwoStep_r16__helper1 : (forall a : CFRA_TwoStep_r16__Type, CFRA_TwoStep_r16__cond a -> CFRA_TwoStep_r16__list_cond (CFRA_TwoStep_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CFRA_TwoStep_r16__helper2 : (forall a : CFRA_TwoStep_r16__Type, CFRA_TwoStep_r16__F2 (CFRA_TwoStep_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CFRA_TwoStep_r16__helper3 : (forall b : CFRA_TwoStep_r16__list_type, CFRA_TwoStep_r16__list_cond b -> CFRA_TwoStep_r16__cond (CFRA_TwoStep_r16__F2 b) /\ CFRA_TwoStep_r16__F1 (CFRA_TwoStep_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CFRA_TwoStep_r16__cond, CFRA_TwoStep_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CFRA_TwoStep_r16__Format : T_Format CFRA_TwoStep_r16__Type CFRA_TwoStep_r16__cond :=
 proj2_format CFRA_TwoStep_r16__cond CFRA_TwoStep_r16__list_format  CFRA_TwoStep_r16__F1 CFRA_TwoStep_r16__F2 CFRA_TwoStep_r16__helper1 CFRA_TwoStep_r16__helper2 CFRA_TwoStep_r16__helper3.

Opaque CFRA_TwoStep_r16__cond CFRA_TwoStep_r16__Format.

