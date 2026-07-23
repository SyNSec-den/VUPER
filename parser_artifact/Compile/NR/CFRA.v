Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RACH_ConfigGeneric.

Opaque RACH_ConfigGeneric__cond RACH_ConfigGeneric__Format.

Inductive CFRA__occasions__ssb_perRACH_Occasion__Type : Set :=
 | CFRA__occasions__ssb_perRACH_Occasion__oneEighth
 | CFRA__occasions__ssb_perRACH_Occasion__oneFourth
 | CFRA__occasions__ssb_perRACH_Occasion__oneHalf
 | CFRA__occasions__ssb_perRACH_Occasion__one
 | CFRA__occasions__ssb_perRACH_Occasion__two
 | CFRA__occasions__ssb_perRACH_Occasion__four
 | CFRA__occasions__ssb_perRACH_Occasion__eight
 | CFRA__occasions__ssb_perRACH_Occasion__sixteen
.
Definition CFRA__occasions__ssb_perRACH_Occasion__cond := (fun (_ : CFRA__occasions__ssb_perRACH_Occasion__Type) => True).
Lemma CFRA__occasions__ssb_perRACH_Occasion__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CFRA__occasions__ssb_perRACH_Occasion__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CFRA__occasions__ssb_perRACH_Occasion__nat__helper.

Definition CFRA__occasions__ssb_perRACH_Occasion__F1 t :=
  match t with
  | CFRA__occasions__ssb_perRACH_Occasion__oneEighth => 0
  | CFRA__occasions__ssb_perRACH_Occasion__oneFourth => 1
  | CFRA__occasions__ssb_perRACH_Occasion__oneHalf => 2
  | CFRA__occasions__ssb_perRACH_Occasion__one => 3
  | CFRA__occasions__ssb_perRACH_Occasion__two => 4
  | CFRA__occasions__ssb_perRACH_Occasion__four => 5
  | CFRA__occasions__ssb_perRACH_Occasion__eight => 6
  | CFRA__occasions__ssb_perRACH_Occasion__sixteen => 7
  end.
Definition CFRA__occasions__ssb_perRACH_Occasion__F2 n :=
  match n with
  | 0 => CFRA__occasions__ssb_perRACH_Occasion__oneEighth
  | 1 => CFRA__occasions__ssb_perRACH_Occasion__oneFourth
  | 2 => CFRA__occasions__ssb_perRACH_Occasion__oneHalf
  | 3 => CFRA__occasions__ssb_perRACH_Occasion__one
  | 4 => CFRA__occasions__ssb_perRACH_Occasion__two
  | 5 => CFRA__occasions__ssb_perRACH_Occasion__four
  | 6 => CFRA__occasions__ssb_perRACH_Occasion__eight
  | 7 => CFRA__occasions__ssb_perRACH_Occasion__sixteen
  | _ => CFRA__occasions__ssb_perRACH_Occasion__oneEighth
  end.
Lemma CFRA__occasions__ssb_perRACH_Occasion__F1F2 : forall x : CFRA__occasions__ssb_perRACH_Occasion__Type, (CFRA__occasions__ssb_perRACH_Occasion__F1 x <= 7) /\ CFRA__occasions__ssb_perRACH_Occasion__F2 (CFRA__occasions__ssb_perRACH_Occasion__F1 x) = x. imp_solve. Qed.
Lemma CFRA__occasions__ssb_perRACH_Occasion__F2F1 : forall (y : nat) (H : y <= 7), CFRA__occasions__ssb_perRACH_Occasion__F1 (CFRA__occasions__ssb_perRACH_Occasion__F2 y) = y. enum_solve H y. Qed.

Record CFRA__occasions__Type : Set :=
  make__CFRA__occasions__Type {
    CFRA__occasions__rach_ConfigGeneric : RACH_ConfigGeneric__Type ;
    CFRA__occasions__ssb_perRACH_Occasion : option CFRA__occasions__ssb_perRACH_Occasion__Type ;
}.
Definition CFRA__occasions__list := (
 Nor RACH_ConfigGeneric__Type RACH_ConfigGeneric__cond ::
 Opt CFRA__occasions__ssb_perRACH_Occasion__Type CFRA__occasions__ssb_perRACH_Occasion__cond ::
 nil).
Definition CFRA__occasions__cond z := 
  RACH_ConfigGeneric__cond (CFRA__occasions__rach_ConfigGeneric z) /\
  opt_cond CFRA__occasions__ssb_perRACH_Occasion__cond (CFRA__occasions__ssb_perRACH_Occasion z) /\
  True.

Require Import NR.CFRA_SSB_Resource.

Opaque CFRA_SSB_Resource__cond CFRA_SSB_Resource__Format.

Definition CFRA__resources__ssb__ssb_ResourceList__Type := list CFRA_SSB_Resource__Type.

Lemma CFRA__resources__ssb__ssb_ResourceList__helper1 : (0 <= 1 <= maxRA_SSB_Resources)%Z. unfold maxRA_SSB_Resources.
 lia. Qed.
Lemma CFRA__resources__ssb__ssb_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxRA_SSB_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxRA_SSB_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA__resources__ssb__ssb_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA__resources__ssb__ssb_ResourceList__cond (z : CFRA__resources__ssb__ssb_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxRA_SSB_Resources)%Z /\ (list_and CFRA_SSB_Resource__cond z) .

Lemma CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__Type := Z.
Definition CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__cond := (fun z => (0 <= z <= 15)%Z).
Record CFRA__resources__ssb__Type : Set :=
  make__CFRA__resources__ssb__Type {
    CFRA__resources__ssb__ssb_ResourceList : CFRA__resources__ssb__ssb_ResourceList__Type ;
    CFRA__resources__ssb__ra_ssb_OccasionMaskIndex : Z ;
}.
Definition CFRA__resources__ssb__list := (
 Nor CFRA__resources__ssb__ssb_ResourceList__Type CFRA__resources__ssb__ssb_ResourceList__cond ::
 Nor Z CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__cond ::
 nil).
Definition CFRA__resources__ssb__cond z := 
  CFRA__resources__ssb__ssb_ResourceList__cond (CFRA__resources__ssb__ssb_ResourceList z) /\
  CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__cond (CFRA__resources__ssb__ra_ssb_OccasionMaskIndex z) /\
  True.

Require Import NR.CFRA_CSIRS_Resource.

Opaque CFRA_CSIRS_Resource__cond CFRA_CSIRS_Resource__Format.

Definition CFRA__resources__csirs__csirs_ResourceList__Type := list CFRA_CSIRS_Resource__Type.

Lemma CFRA__resources__csirs__csirs_ResourceList__helper1 : (0 <= 1 <= maxRA_CSIRS_Resources)%Z. unfold maxRA_CSIRS_Resources.
 lia. Qed.
Lemma CFRA__resources__csirs__csirs_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxRA_CSIRS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxRA_CSIRS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA__resources__csirs__csirs_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA__resources__csirs__csirs_ResourceList__cond (z : CFRA__resources__csirs__csirs_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxRA_CSIRS_Resources)%Z /\ (list_and CFRA_CSIRS_Resource__cond z) .

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Record CFRA__resources__csirs__Type : Set :=
  make__CFRA__resources__csirs__Type {
    CFRA__resources__csirs__csirs_ResourceList : CFRA__resources__csirs__csirs_ResourceList__Type ;
    CFRA__resources__csirs__rsrp_ThresholdCSI_RS : RSRP_Range__Type ;
}.
Definition CFRA__resources__csirs__list := (
 Nor CFRA__resources__csirs__csirs_ResourceList__Type CFRA__resources__csirs__csirs_ResourceList__cond ::
 Nor RSRP_Range__Type RSRP_Range__cond ::
 nil).
Definition CFRA__resources__csirs__cond z := 
  CFRA__resources__csirs__csirs_ResourceList__cond (CFRA__resources__csirs__csirs_ResourceList z) /\
  RSRP_Range__cond (CFRA__resources__csirs__rsrp_ThresholdCSI_RS z) /\
  True.


Inductive CFRA__resources__Type : Set :=
  | CFRA__resources__ssb : CFRA__resources__ssb__Type -> CFRA__resources__Type
  | CFRA__resources__csirs : CFRA__resources__csirs__Type -> CFRA__resources__Type
.
Definition CFRA__resources__list : list typ := (
typ_cons CFRA__resources__ssb__Type CFRA__resources__ssb__cond ::
typ_cons CFRA__resources__csirs__Type CFRA__resources__csirs__cond ::
 nil).
Definition CFRA__resources__cond (c : CFRA__resources__Type) := 
  match c with
  | CFRA__resources__ssb t => CFRA__resources__ssb__cond t 
  | CFRA__resources__csirs t => CFRA__resources__csirs__cond t 
  end.

Lemma CFRA__resources__len_helper1 : to_bit_sz (length CFRA__resources__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CFRA__resources__len_helper2 : 2 <= length2 CFRA__resources__list.
 simpl. lia. Qed.
Lemma CFRA__ext0O__totalNumberOfRA_Preambles__helper1 : (1 <= 63)%Z.  lia. Qed.
Lemma CFRA__ext0O__totalNumberOfRA_Preambles__helper2 : to_bit_sz (Z.to_nat (63 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA__ext0O__totalNumberOfRA_Preambles__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA__ext0O__totalNumberOfRA_Preambles__Type := Z.
Definition CFRA__ext0O__totalNumberOfRA_Preambles__cond := (fun z => (1 <= z <= 63)%Z).
Record CFRA__ext0O__Type : Set :=
  make__CFRA__ext0O__Type {
    CFRA__ext0O__totalNumberOfRA_Preambles : option Z ;
}.
Definition CFRA__ext0O__list := (
 Opt Z CFRA__ext0O__totalNumberOfRA_Preambles__cond ::
 nil).
Definition CFRA__ext0O__cond z := 
  opt_cond CFRA__ext0O__totalNumberOfRA_Preambles__cond (CFRA__ext0O__totalNumberOfRA_Preambles z) /\
  True.

Definition CFRA__ext0__Type := CFRA__ext0O__Type.
Definition CFRA__ext0__cond := CFRA__ext0O__cond.

Record CFRA__Type : Set :=
  make__CFRA__Type {
    CFRA__occasions : option CFRA__occasions__Type ;
    CFRA__resources : CFRA__resources__Type ;
    CFRA__ext0 : option CFRA__ext0__Type ;
}.
Definition CFRA__root_list : list seq_elem := (
 Opt CFRA__occasions__Type CFRA__occasions__cond ::
 Nor CFRA__resources__Type CFRA__resources__cond ::
 nil).
Definition CFRA__ext_list : list typ := (
  typ_cons CFRA__ext0__Type CFRA__ext0__cond ::
  nil).
Definition CFRA__cond (z : CFRA__Type) := 
(  opt_cond CFRA__occasions__cond (CFRA__occasions z) /\
  CFRA__resources__cond (CFRA__resources z) /\
  True) /\ 
(  opt_cond CFRA__ext0__cond (CFRA__ext0 z) /\
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
Definition CFRA__occasions__ssb_perRACH_Occasion__Format : T_Format CFRA__occasions__ssb_perRACH_Occasion__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CFRA__occasions__ssb_perRACH_Occasion__nat__Format CFRA__occasions__ssb_perRACH_Occasion__F1 CFRA__occasions__ssb_perRACH_Occasion__F2 CFRA__occasions__ssb_perRACH_Occasion__F1F2 CFRA__occasions__ssb_perRACH_Occasion__F2F1.

Opaque CFRA__occasions__ssb_perRACH_Occasion__cond CFRA__occasions__ssb_perRACH_Occasion__Format.


Definition CFRA__occasions__Format_Type := Eval cbn in seq_format_prod CFRA__occasions__list.
Definition CFRA__occasions__Format_list : CFRA__occasions__Format_Type :=
  (RACH_ConfigGeneric__Format, (CFRA__occasions__ssb_perRACH_Occasion__Format, unit_format)).
Definition CFRA__occasions__list__Format := (*Eval compute in *) seq_format CFRA__occasions__list CFRA__occasions__Format_list.
Definition CFRA__occasions__F1 z :=
  (CFRA__occasions__rach_ConfigGeneric z, (CFRA__occasions__ssb_perRACH_Occasion z, tt)).
Definition CFRA__occasions__F2 (y : seq_type CFRA__occasions__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CFRA__occasions__Type i0 i1
  end.
Lemma CFRA__occasions__F1F2_cond (z : CFRA__occasions__Type)
  : CFRA__occasions__cond z ->
  (seq_cond CFRA__occasions__list (CFRA__occasions__F1 z)).
intro H. unfold CFRA__occasions__cond in H. simpl. auto. Qed.
Lemma CFRA__occasions__F1F2_cond2 (z : CFRA__occasions__Type)
 : CFRA__occasions__F2 (CFRA__occasions__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA__occasions__F2F1_cond (y : seq_type CFRA__occasions__list)
  : seq_cond CFRA__occasions__list y ->
 (CFRA__occasions__cond (CFRA__occasions__F2 y)) /\  CFRA__occasions__F1 (CFRA__occasions__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA__occasions__cond. simpl in *. auto.
 - simpl. unfold CFRA__occasions__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA__occasions__Format : T_Format CFRA__occasions__Type CFRA__occasions__cond :=
        proj2_format  CFRA__occasions__cond CFRA__occasions__list__Format
    CFRA__occasions__F1 CFRA__occasions__F2 CFRA__occasions__F1F2_cond  CFRA__occasions__F1F2_cond2 CFRA__occasions__F2F1_cond.
Opaque CFRA__occasions__cond CFRA__occasions__Format.

Definition CFRA__resources__ssb__ssb_ResourceList__Format : T_Format CFRA__resources__ssb__ssb_ResourceList__Type CFRA__resources__ssb__ssb_ResourceList__cond := seq_of_format CFRA_SSB_Resource__Format 1 maxRA_SSB_Resources CFRA__resources__ssb__ssb_ResourceList__helper1 CFRA__resources__ssb__ssb_ResourceList__helper2.

Opaque CFRA__resources__ssb__ssb_ResourceList__cond CFRA__resources__ssb__ssb_ResourceList__Format.

Definition CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__Format : T_Format Z CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__cond :=
 ranged_int_format (0) (15) CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__helper1 CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__helper2.

Opaque CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__cond CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__Format.


Definition CFRA__resources__ssb__Format_Type := Eval cbn in seq_format_prod CFRA__resources__ssb__list.
Definition CFRA__resources__ssb__Format_list : CFRA__resources__ssb__Format_Type :=
  (CFRA__resources__ssb__ssb_ResourceList__Format, (CFRA__resources__ssb__ra_ssb_OccasionMaskIndex__Format, unit_format)).
Definition CFRA__resources__ssb__list__Format := (*Eval compute in *) seq_format CFRA__resources__ssb__list CFRA__resources__ssb__Format_list.
Definition CFRA__resources__ssb__F1 z :=
  (CFRA__resources__ssb__ssb_ResourceList z, (CFRA__resources__ssb__ra_ssb_OccasionMaskIndex z, tt)).
Definition CFRA__resources__ssb__F2 (y : seq_type CFRA__resources__ssb__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CFRA__resources__ssb__Type i0 i1
  end.
Lemma CFRA__resources__ssb__F1F2_cond (z : CFRA__resources__ssb__Type)
  : CFRA__resources__ssb__cond z ->
  (seq_cond CFRA__resources__ssb__list (CFRA__resources__ssb__F1 z)).
intro H. unfold CFRA__resources__ssb__cond in H. simpl. auto. Qed.
Lemma CFRA__resources__ssb__F1F2_cond2 (z : CFRA__resources__ssb__Type)
 : CFRA__resources__ssb__F2 (CFRA__resources__ssb__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA__resources__ssb__F2F1_cond (y : seq_type CFRA__resources__ssb__list)
  : seq_cond CFRA__resources__ssb__list y ->
 (CFRA__resources__ssb__cond (CFRA__resources__ssb__F2 y)) /\  CFRA__resources__ssb__F1 (CFRA__resources__ssb__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA__resources__ssb__cond. simpl in *. auto.
 - simpl. unfold CFRA__resources__ssb__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA__resources__ssb__Format : T_Format CFRA__resources__ssb__Type CFRA__resources__ssb__cond :=
        proj2_format  CFRA__resources__ssb__cond CFRA__resources__ssb__list__Format
    CFRA__resources__ssb__F1 CFRA__resources__ssb__F2 CFRA__resources__ssb__F1F2_cond  CFRA__resources__ssb__F1F2_cond2 CFRA__resources__ssb__F2F1_cond.
Opaque CFRA__resources__ssb__cond CFRA__resources__ssb__Format.

Definition CFRA__resources__csirs__csirs_ResourceList__Format : T_Format CFRA__resources__csirs__csirs_ResourceList__Type CFRA__resources__csirs__csirs_ResourceList__cond := seq_of_format CFRA_CSIRS_Resource__Format 1 maxRA_CSIRS_Resources CFRA__resources__csirs__csirs_ResourceList__helper1 CFRA__resources__csirs__csirs_ResourceList__helper2.

Opaque CFRA__resources__csirs__csirs_ResourceList__cond CFRA__resources__csirs__csirs_ResourceList__Format.


Definition CFRA__resources__csirs__Format_Type := Eval cbn in seq_format_prod CFRA__resources__csirs__list.
Definition CFRA__resources__csirs__Format_list : CFRA__resources__csirs__Format_Type :=
  (CFRA__resources__csirs__csirs_ResourceList__Format, (RSRP_Range__Format, unit_format)).
Definition CFRA__resources__csirs__list__Format := (*Eval compute in *) seq_format CFRA__resources__csirs__list CFRA__resources__csirs__Format_list.
Definition CFRA__resources__csirs__F1 z :=
  (CFRA__resources__csirs__csirs_ResourceList z, (CFRA__resources__csirs__rsrp_ThresholdCSI_RS z, tt)).
Definition CFRA__resources__csirs__F2 (y : seq_type CFRA__resources__csirs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CFRA__resources__csirs__Type i0 i1
  end.
Lemma CFRA__resources__csirs__F1F2_cond (z : CFRA__resources__csirs__Type)
  : CFRA__resources__csirs__cond z ->
  (seq_cond CFRA__resources__csirs__list (CFRA__resources__csirs__F1 z)).
intro H. unfold CFRA__resources__csirs__cond in H. simpl. auto. Qed.
Lemma CFRA__resources__csirs__F1F2_cond2 (z : CFRA__resources__csirs__Type)
 : CFRA__resources__csirs__F2 (CFRA__resources__csirs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA__resources__csirs__F2F1_cond (y : seq_type CFRA__resources__csirs__list)
  : seq_cond CFRA__resources__csirs__list y ->
 (CFRA__resources__csirs__cond (CFRA__resources__csirs__F2 y)) /\  CFRA__resources__csirs__F1 (CFRA__resources__csirs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA__resources__csirs__cond. simpl in *. auto.
 - simpl. unfold CFRA__resources__csirs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA__resources__csirs__Format : T_Format CFRA__resources__csirs__Type CFRA__resources__csirs__cond :=
        proj2_format  CFRA__resources__csirs__cond CFRA__resources__csirs__list__Format
    CFRA__resources__csirs__F1 CFRA__resources__csirs__F2 CFRA__resources__csirs__F1F2_cond  CFRA__resources__csirs__F1F2_cond2 CFRA__resources__csirs__F2F1_cond.
Opaque CFRA__resources__csirs__cond CFRA__resources__csirs__Format.


Definition CFRA__resources__Format_Type := Eval cbn in get_formats CFRA__resources__list.
Definition CFRA__resources__Format_list : CFRA__resources__Format_Type :=
  (CFRA__resources__ssb__Format, (CFRA__resources__csirs__Format, unit__Format)).
Definition CFRA__resources__list__Format := Eval compute in choice_format CFRA__resources__list CFRA__resources__len_helper1 CFRA__resources__len_helper2  CFRA__resources__Format_list.
Definition CFRA__resources__F1 (z : CFRA__resources__Type) : (choice CFRA__resources__list) :=
  match z with
   | CFRA__resources__ssb t => existT _ 0 t
  | CFRA__resources__csirs t => existT _ 1 t
  end.
Definition CFRA__resources__g := (fun n => typ_set (get_nth_typ CFRA__resources__list n)).
Definition CFRA__resources__F2 (y : choice CFRA__resources__list) : CFRA__resources__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CFRA__resources__g n -> CFRA__resources__Type) with
    | 0 => fun (t : CFRA__resources__ssb__Type) => CFRA__resources__ssb t 
    | 1 => fun (t : CFRA__resources__csirs__Type) => CFRA__resources__csirs t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CFRA__resources__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CFRA__resources__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CFRA__resources__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CFRA__resources__Type with end) n0
           end t0).

Lemma CFRA__resources__helper2 :  forall (y : CFRA__resources__Type), CFRA__resources__cond y -> choice_cond CFRA__resources__list (CFRA__resources__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CFRA__resources__helper3 :  forall (y : CFRA__resources__Type), CFRA__resources__F2 (CFRA__resources__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CFRA__resources__helper4 : (forall b : choice CFRA__resources__list, choice_cond CFRA__resources__list b -> CFRA__resources__cond (CFRA__resources__F2 b) /\ CFRA__resources__F1 (CFRA__resources__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CFRA__resources__F1 CFRA__resources__F2.
Definition CFRA__resources__Format : T_Format CFRA__resources__Type CFRA__resources__cond :=
  (* Eval compute in *) proj2_format CFRA__resources__cond CFRA__resources__list__Format CFRA__resources__F1 CFRA__resources__F2 CFRA__resources__helper2 CFRA__resources__helper3 CFRA__resources__helper4.
Opaque CFRA__resources__cond CFRA__resources__Format.

Definition CFRA__ext0O__totalNumberOfRA_Preambles__Format : T_Format Z CFRA__ext0O__totalNumberOfRA_Preambles__cond :=
 ranged_int_format (1) (63) CFRA__ext0O__totalNumberOfRA_Preambles__helper1 CFRA__ext0O__totalNumberOfRA_Preambles__helper2.

Opaque CFRA__ext0O__totalNumberOfRA_Preambles__cond CFRA__ext0O__totalNumberOfRA_Preambles__Format.


Definition CFRA__ext0O__Format_Type := Eval cbn in seq_format_prod CFRA__ext0O__list.
Definition CFRA__ext0O__Format_list : CFRA__ext0O__Format_Type :=
  (CFRA__ext0O__totalNumberOfRA_Preambles__Format, unit_format).
Definition CFRA__ext0O__list__Format := (*Eval compute in *) seq_format CFRA__ext0O__list CFRA__ext0O__Format_list.
Definition CFRA__ext0O__F1 z :=
  (CFRA__ext0O__totalNumberOfRA_Preambles z, tt).
Definition CFRA__ext0O__F2 (y : seq_type CFRA__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CFRA__ext0O__Type i0
  end.
Lemma CFRA__ext0O__F1F2_cond (z : CFRA__ext0O__Type)
  : CFRA__ext0O__cond z ->
  (seq_cond CFRA__ext0O__list (CFRA__ext0O__F1 z)).
intro H. unfold CFRA__ext0O__cond in H. simpl. auto. Qed.
Lemma CFRA__ext0O__F1F2_cond2 (z : CFRA__ext0O__Type)
 : CFRA__ext0O__F2 (CFRA__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA__ext0O__F2F1_cond (y : seq_type CFRA__ext0O__list)
  : seq_cond CFRA__ext0O__list y ->
 (CFRA__ext0O__cond (CFRA__ext0O__F2 y)) /\  CFRA__ext0O__F1 (CFRA__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA__ext0O__cond. simpl in *. auto.
 - simpl. unfold CFRA__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA__ext0O__Format : T_Format CFRA__ext0O__Type CFRA__ext0O__cond :=
        proj2_format  CFRA__ext0O__cond CFRA__ext0O__list__Format
    CFRA__ext0O__F1 CFRA__ext0O__F2 CFRA__ext0O__F1F2_cond  CFRA__ext0O__F1F2_cond2 CFRA__ext0O__F2F1_cond.
Opaque CFRA__ext0O__cond CFRA__ext0O__Format.

Definition CFRA__ext0__check_all_none (b : CFRA__ext0O__Type) : bool :=
match b with 
  | make__CFRA__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CFRA__ext0__Format : T_Format CFRA__ext0__Type CFRA__ext0__cond :=
  restrict_add_format CFRA__ext0__check_all_none CFRA__ext0O__Format.

Opaque CFRA__ext0__cond CFRA__ext0__Format.


Definition CFRA__root_Format_Type := Eval cbn in seq_format_prod CFRA__root_list.
Definition CFRA__root_Format_list : CFRA__root_Format_Type :=
  (CFRA__occasions__Format, (CFRA__resources__Format, unit_format)).

Definition CFRA__ext_Format_Type := Eval cbn in get_formats CFRA__ext_list.
Definition CFRA__ext_Format_list : CFRA__ext_Format_Type :=
  (CFRA__ext0__Format, unit__Format).

Definition CFRA__list_type : Set := (seq_type CFRA__root_list) * (seq_ext_type CFRA__ext_list).
Definition CFRA__list_cond (z : CFRA__list_type) : Prop :=
        (seq_cond CFRA__root_list (fst z)) /\ (seq_ext_cond CFRA__ext_list (snd z)).
Definition CFRA__list_format : T_Format CFRA__list_type CFRA__list_cond :=
 (* Eval compute in *) seq_ext_format CFRA__root_list CFRA__root_Format_list CFRA__ext_list CFRA__ext_Format_list.

Opaque CFRA__list_format.
Definition CFRA__F1 (z : CFRA__Type) : CFRA__list_type :=
  (((CFRA__occasions z, (CFRA__resources z, tt))), (
(CFRA__ext0 z, tt))).
Definition CFRA__F2 (y : CFRA__list_type) : CFRA__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__CFRA__Type j0 j1 i0
  end.
Definition CFRA__helper1 : (forall a : CFRA__Type, CFRA__cond a -> CFRA__list_cond (CFRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CFRA__helper2 : (forall a : CFRA__Type, CFRA__F2 (CFRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CFRA__helper3 : (forall b : CFRA__list_type, CFRA__list_cond b -> CFRA__cond (CFRA__F2 b) /\ CFRA__F1 (CFRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CFRA__cond, CFRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CFRA__Format : T_Format CFRA__Type CFRA__cond :=
 proj2_format CFRA__cond CFRA__list_format  CFRA__F1 CFRA__F2 CFRA__helper1 CFRA__helper2 CFRA__helper3.

Opaque CFRA__cond CFRA__Format.

