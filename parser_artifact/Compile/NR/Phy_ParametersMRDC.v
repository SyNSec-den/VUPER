Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NAICS_Capability_Entry.

Opaque NAICS_Capability_Entry__cond NAICS_Capability_Entry__Format.

Definition Phy_ParametersMRDC__naics_Capability_List__Type := list NAICS_Capability_Entry__Type.

Lemma Phy_ParametersMRDC__naics_Capability_List__helper1 : (0 <= 1 <= maxNrofNAICS_Entries)%Z. unfold maxNrofNAICS_Entries.
 lia. Qed.
Lemma Phy_ParametersMRDC__naics_Capability_List__helper2 : to_bit_sz (Z.to_nat (maxNrofNAICS_Entries - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNAICS_Entries - 1))%Z). { apply Zorder.Zle_minus_le_0. apply Phy_ParametersMRDC__naics_Capability_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Phy_ParametersMRDC__naics_Capability_List__cond (z : Phy_ParametersMRDC__naics_Capability_List__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNAICS_Entries)%Z /\ (list_and NAICS_Capability_Entry__cond z) .

Require Import NR.CarrierAggregationVariant.

Opaque CarrierAggregationVariant__cond CarrierAggregationVariant__Format.

Record Phy_ParametersMRDC__ext0O__Type : Set :=
  make__Phy_ParametersMRDC__ext0O__Type {
    Phy_ParametersMRDC__ext0O__spCellPlacement : option CarrierAggregationVariant__Type ;
}.
Definition Phy_ParametersMRDC__ext0O__list := (
 Opt CarrierAggregationVariant__Type CarrierAggregationVariant__cond ::
 nil).
Definition Phy_ParametersMRDC__ext0O__cond z := 
  opt_cond CarrierAggregationVariant__cond (Phy_ParametersMRDC__ext0O__spCellPlacement z) /\
  True.

Definition Phy_ParametersMRDC__ext0__Type := Phy_ParametersMRDC__ext0O__Type.
Definition Phy_ParametersMRDC__ext0__cond := Phy_ParametersMRDC__ext0O__cond.

Inductive Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Type : Set :=
 | Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__supported
.
Definition Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__cond := (fun (_ : Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Type) => True).
Lemma Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__nat__helper.

Definition Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1 t :=
  match t with
  | Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__supported => 0
  end.
Definition Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__supported
  | _ => Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__supported
  end.
Lemma Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1F2 : forall x : Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Type, (Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1 x <= 0) /\ Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F2 (Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1 (Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Type : Set :=
 | Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__supported
.
Definition Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__cond := (fun (_ : Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Type) => True).
Lemma Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__nat__helper.

Definition Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1 t :=
  match t with
  | Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__supported => 0
  end.
Definition Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__supported
  | _ => Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__supported
  end.
Lemma Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1F2 : forall x : Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Type, (Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1 x <= 0) /\ Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F2 (Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1 (Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersMRDC__ext1O__Type : Set :=
  make__Phy_ParametersMRDC__ext1O__Type {
    Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16 : option Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Type ;
    Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16 : option Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Type ;
}.
Definition Phy_ParametersMRDC__ext1O__list := (
 Opt Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Type Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__cond ::
 Opt Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Type Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__cond ::
 nil).
Definition Phy_ParametersMRDC__ext1O__cond z := 
  opt_cond Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__cond (Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16 z) /\
  opt_cond Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__cond (Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16 z) /\
  True.

Definition Phy_ParametersMRDC__ext1__Type := Phy_ParametersMRDC__ext1O__Type.
Definition Phy_ParametersMRDC__ext1__cond := Phy_ParametersMRDC__ext1O__cond.

Record Phy_ParametersMRDC__Type : Set :=
  make__Phy_ParametersMRDC__Type {
    Phy_ParametersMRDC__naics_Capability_List : option Phy_ParametersMRDC__naics_Capability_List__Type ;
    Phy_ParametersMRDC__ext0 : option Phy_ParametersMRDC__ext0__Type ;
    Phy_ParametersMRDC__ext1 : option Phy_ParametersMRDC__ext1__Type ;
}.
Definition Phy_ParametersMRDC__root_list : list seq_elem := (
 Opt Phy_ParametersMRDC__naics_Capability_List__Type Phy_ParametersMRDC__naics_Capability_List__cond ::
 nil).
Definition Phy_ParametersMRDC__ext_list : list typ := (
  typ_cons Phy_ParametersMRDC__ext0__Type Phy_ParametersMRDC__ext0__cond ::
  typ_cons Phy_ParametersMRDC__ext1__Type Phy_ParametersMRDC__ext1__cond ::
  nil).
Definition Phy_ParametersMRDC__cond (z : Phy_ParametersMRDC__Type) := 
(  opt_cond Phy_ParametersMRDC__naics_Capability_List__cond (Phy_ParametersMRDC__naics_Capability_List z) /\
  True) /\ 
(  opt_cond Phy_ParametersMRDC__ext0__cond (Phy_ParametersMRDC__ext0 z) /\
  opt_cond Phy_ParametersMRDC__ext1__cond (Phy_ParametersMRDC__ext1 z) /\
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
Definition Phy_ParametersMRDC__naics_Capability_List__Format : T_Format Phy_ParametersMRDC__naics_Capability_List__Type Phy_ParametersMRDC__naics_Capability_List__cond := seq_of_format NAICS_Capability_Entry__Format 1 maxNrofNAICS_Entries Phy_ParametersMRDC__naics_Capability_List__helper1 Phy_ParametersMRDC__naics_Capability_List__helper2.

Opaque Phy_ParametersMRDC__naics_Capability_List__cond Phy_ParametersMRDC__naics_Capability_List__Format.


Definition Phy_ParametersMRDC__ext0O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersMRDC__ext0O__list.
Definition Phy_ParametersMRDC__ext0O__Format_list : Phy_ParametersMRDC__ext0O__Format_Type :=
  (CarrierAggregationVariant__Format, unit_format).
Definition Phy_ParametersMRDC__ext0O__list__Format := (*Eval compute in *) seq_format Phy_ParametersMRDC__ext0O__list Phy_ParametersMRDC__ext0O__Format_list.
Definition Phy_ParametersMRDC__ext0O__F1 z :=
  (Phy_ParametersMRDC__ext0O__spCellPlacement z, tt).
Definition Phy_ParametersMRDC__ext0O__F2 (y : seq_type Phy_ParametersMRDC__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersMRDC__ext0O__Type i0
  end.
Lemma Phy_ParametersMRDC__ext0O__F1F2_cond (z : Phy_ParametersMRDC__ext0O__Type)
  : Phy_ParametersMRDC__ext0O__cond z ->
  (seq_cond Phy_ParametersMRDC__ext0O__list (Phy_ParametersMRDC__ext0O__F1 z)).
intro H. unfold Phy_ParametersMRDC__ext0O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersMRDC__ext0O__F1F2_cond2 (z : Phy_ParametersMRDC__ext0O__Type)
 : Phy_ParametersMRDC__ext0O__F2 (Phy_ParametersMRDC__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersMRDC__ext0O__F2F1_cond (y : seq_type Phy_ParametersMRDC__ext0O__list)
  : seq_cond Phy_ParametersMRDC__ext0O__list y ->
 (Phy_ParametersMRDC__ext0O__cond (Phy_ParametersMRDC__ext0O__F2 y)) /\  Phy_ParametersMRDC__ext0O__F1 (Phy_ParametersMRDC__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersMRDC__ext0O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersMRDC__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersMRDC__ext0O__Format : T_Format Phy_ParametersMRDC__ext0O__Type Phy_ParametersMRDC__ext0O__cond :=
        proj2_format  Phy_ParametersMRDC__ext0O__cond Phy_ParametersMRDC__ext0O__list__Format
    Phy_ParametersMRDC__ext0O__F1 Phy_ParametersMRDC__ext0O__F2 Phy_ParametersMRDC__ext0O__F1F2_cond  Phy_ParametersMRDC__ext0O__F1F2_cond2 Phy_ParametersMRDC__ext0O__F2F1_cond.
Opaque Phy_ParametersMRDC__ext0O__cond Phy_ParametersMRDC__ext0O__Format.

Definition Phy_ParametersMRDC__ext0__check_all_none (b : Phy_ParametersMRDC__ext0O__Type) : bool :=
match b with 
  | make__Phy_ParametersMRDC__ext0O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersMRDC__ext0__Format : T_Format Phy_ParametersMRDC__ext0__Type Phy_ParametersMRDC__ext0__cond :=
  restrict_add_format Phy_ParametersMRDC__ext0__check_all_none Phy_ParametersMRDC__ext0O__Format.

Opaque Phy_ParametersMRDC__ext0__cond Phy_ParametersMRDC__ext0__Format.

Definition Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Format : T_Format Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__nat__Format Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1 Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F2 Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F1F2 Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__F2F1.

Opaque Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__cond Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Format.

Definition Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Format : T_Format Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__nat__Format Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1 Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F2 Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F1F2 Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__F2F1.

Opaque Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__cond Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Format.


Definition Phy_ParametersMRDC__ext1O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersMRDC__ext1O__list.
Definition Phy_ParametersMRDC__ext1O__Format_list : Phy_ParametersMRDC__ext1O__Format_Type :=
  (Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16__Format, (Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16__Format, unit_format)).
Definition Phy_ParametersMRDC__ext1O__list__Format := (*Eval compute in *) seq_format Phy_ParametersMRDC__ext1O__list Phy_ParametersMRDC__ext1O__Format_list.
Definition Phy_ParametersMRDC__ext1O__F1 z :=
  (Phy_ParametersMRDC__ext1O__tdd_PCellUL_TX_AllUL_Subframe_r16 z, (Phy_ParametersMRDC__ext1O__fdd_PCellUL_TX_AllUL_Subframe_r16 z, tt)).
Definition Phy_ParametersMRDC__ext1O__F2 (y : seq_type Phy_ParametersMRDC__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersMRDC__ext1O__Type i0 i1
  end.
Lemma Phy_ParametersMRDC__ext1O__F1F2_cond (z : Phy_ParametersMRDC__ext1O__Type)
  : Phy_ParametersMRDC__ext1O__cond z ->
  (seq_cond Phy_ParametersMRDC__ext1O__list (Phy_ParametersMRDC__ext1O__F1 z)).
intro H. unfold Phy_ParametersMRDC__ext1O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersMRDC__ext1O__F1F2_cond2 (z : Phy_ParametersMRDC__ext1O__Type)
 : Phy_ParametersMRDC__ext1O__F2 (Phy_ParametersMRDC__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersMRDC__ext1O__F2F1_cond (y : seq_type Phy_ParametersMRDC__ext1O__list)
  : seq_cond Phy_ParametersMRDC__ext1O__list y ->
 (Phy_ParametersMRDC__ext1O__cond (Phy_ParametersMRDC__ext1O__F2 y)) /\  Phy_ParametersMRDC__ext1O__F1 (Phy_ParametersMRDC__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersMRDC__ext1O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersMRDC__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersMRDC__ext1O__Format : T_Format Phy_ParametersMRDC__ext1O__Type Phy_ParametersMRDC__ext1O__cond :=
        proj2_format  Phy_ParametersMRDC__ext1O__cond Phy_ParametersMRDC__ext1O__list__Format
    Phy_ParametersMRDC__ext1O__F1 Phy_ParametersMRDC__ext1O__F2 Phy_ParametersMRDC__ext1O__F1F2_cond  Phy_ParametersMRDC__ext1O__F1F2_cond2 Phy_ParametersMRDC__ext1O__F2F1_cond.
Opaque Phy_ParametersMRDC__ext1O__cond Phy_ParametersMRDC__ext1O__Format.

Definition Phy_ParametersMRDC__ext1__check_all_none (b : Phy_ParametersMRDC__ext1O__Type) : bool :=
match b with 
  | make__Phy_ParametersMRDC__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersMRDC__ext1__Format : T_Format Phy_ParametersMRDC__ext1__Type Phy_ParametersMRDC__ext1__cond :=
  restrict_add_format Phy_ParametersMRDC__ext1__check_all_none Phy_ParametersMRDC__ext1O__Format.

Opaque Phy_ParametersMRDC__ext1__cond Phy_ParametersMRDC__ext1__Format.


Definition Phy_ParametersMRDC__root_Format_Type := Eval cbn in seq_format_prod Phy_ParametersMRDC__root_list.
Definition Phy_ParametersMRDC__root_Format_list : Phy_ParametersMRDC__root_Format_Type :=
  (Phy_ParametersMRDC__naics_Capability_List__Format, unit_format).

Definition Phy_ParametersMRDC__ext_Format_Type := Eval cbn in get_formats Phy_ParametersMRDC__ext_list.
Definition Phy_ParametersMRDC__ext_Format_list : Phy_ParametersMRDC__ext_Format_Type :=
  (Phy_ParametersMRDC__ext0__Format, (Phy_ParametersMRDC__ext1__Format, unit__Format)).

Definition Phy_ParametersMRDC__list_type : Set := (seq_type Phy_ParametersMRDC__root_list) * (seq_ext_type Phy_ParametersMRDC__ext_list).
Definition Phy_ParametersMRDC__list_cond (z : Phy_ParametersMRDC__list_type) : Prop :=
        (seq_cond Phy_ParametersMRDC__root_list (fst z)) /\ (seq_ext_cond Phy_ParametersMRDC__ext_list (snd z)).
Definition Phy_ParametersMRDC__list_format : T_Format Phy_ParametersMRDC__list_type Phy_ParametersMRDC__list_cond :=
 (* Eval compute in *) seq_ext_format Phy_ParametersMRDC__root_list Phy_ParametersMRDC__root_Format_list Phy_ParametersMRDC__ext_list Phy_ParametersMRDC__ext_Format_list.

Opaque Phy_ParametersMRDC__list_format.
Definition Phy_ParametersMRDC__F1 (z : Phy_ParametersMRDC__Type) : Phy_ParametersMRDC__list_type :=
  (((Phy_ParametersMRDC__naics_Capability_List z, tt)), (
(Phy_ParametersMRDC__ext0 z, (Phy_ParametersMRDC__ext1 z, tt)))).
Definition Phy_ParametersMRDC__F2 (y : Phy_ParametersMRDC__list_type) : Phy_ParametersMRDC__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__Phy_ParametersMRDC__Type j0 i0 i1
  end.
Definition Phy_ParametersMRDC__helper1 : (forall a : Phy_ParametersMRDC__Type, Phy_ParametersMRDC__cond a -> Phy_ParametersMRDC__list_cond (Phy_ParametersMRDC__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersMRDC__helper2 : (forall a : Phy_ParametersMRDC__Type, Phy_ParametersMRDC__F2 (Phy_ParametersMRDC__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersMRDC__helper3 : (forall b : Phy_ParametersMRDC__list_type, Phy_ParametersMRDC__list_cond b -> Phy_ParametersMRDC__cond (Phy_ParametersMRDC__F2 b) /\ Phy_ParametersMRDC__F1 (Phy_ParametersMRDC__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Phy_ParametersMRDC__cond, Phy_ParametersMRDC__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Phy_ParametersMRDC__Format : T_Format Phy_ParametersMRDC__Type Phy_ParametersMRDC__cond :=
 proj2_format Phy_ParametersMRDC__cond Phy_ParametersMRDC__list_format  Phy_ParametersMRDC__F1 Phy_ParametersMRDC__F2 Phy_ParametersMRDC__helper1 Phy_ParametersMRDC__helper2 Phy_ParametersMRDC__helper3.

Opaque Phy_ParametersMRDC__cond Phy_ParametersMRDC__Format.

