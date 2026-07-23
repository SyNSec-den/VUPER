Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SupportedCSI_RS_Resource.

Opaque SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__Format.

Definition CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Type := list SupportedCSI_RS_Resource__Type.

Lemma CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__helper1 : (0 <= 1 <= maxNrofCSI_RS_Resources)%Z. unfold maxNrofCSI_RS_Resources.
 lia. Qed.
Lemma CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__cond (z : CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_Resources)%Z /\ (list_and SupportedCSI_RS_Resource__cond z) .

Inductive CodebookParameters__type1__singlePanel__modes__Type : Set :=
 | CodebookParameters__type1__singlePanel__modes__mode1
 | CodebookParameters__type1__singlePanel__modes__mode1andMode2
.
Definition CodebookParameters__type1__singlePanel__modes__cond := (fun (_ : CodebookParameters__type1__singlePanel__modes__Type) => True).
Lemma CodebookParameters__type1__singlePanel__modes__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CodebookParameters__type1__singlePanel__modes__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CodebookParameters__type1__singlePanel__modes__nat__helper.

Definition CodebookParameters__type1__singlePanel__modes__F1 t :=
  match t with
  | CodebookParameters__type1__singlePanel__modes__mode1 => 0
  | CodebookParameters__type1__singlePanel__modes__mode1andMode2 => 1
  end.
Definition CodebookParameters__type1__singlePanel__modes__F2 n :=
  match n with
  | 0 => CodebookParameters__type1__singlePanel__modes__mode1
  | 1 => CodebookParameters__type1__singlePanel__modes__mode1andMode2
  | _ => CodebookParameters__type1__singlePanel__modes__mode1
  end.
Lemma CodebookParameters__type1__singlePanel__modes__F1F2 : forall x : CodebookParameters__type1__singlePanel__modes__Type, (CodebookParameters__type1__singlePanel__modes__F1 x <= 1) /\ CodebookParameters__type1__singlePanel__modes__F2 (CodebookParameters__type1__singlePanel__modes__F1 x) = x. imp_solve. Qed.
Lemma CodebookParameters__type1__singlePanel__modes__F2F1 : forall (y : nat) (H : y <= 1), CodebookParameters__type1__singlePanel__modes__F1 (CodebookParameters__type1__singlePanel__modes__F2 y) = y. enum_solve H y. Qed.

Lemma CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__Type := Z.
Definition CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record CodebookParameters__type1__singlePanel__Type : Set :=
  make__CodebookParameters__type1__singlePanel__Type {
    CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList : CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Type ;
    CodebookParameters__type1__singlePanel__modes : CodebookParameters__type1__singlePanel__modes__Type ;
    CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet : Z ;
}.
Definition CodebookParameters__type1__singlePanel__list := (
 Nor CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Type CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__cond ::
 Nor CodebookParameters__type1__singlePanel__modes__Type CodebookParameters__type1__singlePanel__modes__cond ::
 Nor Z CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__cond ::
 nil).
Definition CodebookParameters__type1__singlePanel__cond z := 
  CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__cond (CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList z) /\
  CodebookParameters__type1__singlePanel__modes__cond (CodebookParameters__type1__singlePanel__modes z) /\
  CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__cond (CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet z) /\
  True.

Require Import NR.SupportedCSI_RS_Resource.

Opaque SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__Format.

Definition CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Type := list SupportedCSI_RS_Resource__Type.

Lemma CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__helper1 : (0 <= 1 <= maxNrofCSI_RS_Resources)%Z. unfold maxNrofCSI_RS_Resources.
 lia. Qed.
Lemma CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__cond (z : CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_Resources)%Z /\ (list_and SupportedCSI_RS_Resource__cond z) .

Inductive CodebookParameters__type1__multiPanel__modes__Type : Set :=
 | CodebookParameters__type1__multiPanel__modes__mode1
 | CodebookParameters__type1__multiPanel__modes__mode2
 | CodebookParameters__type1__multiPanel__modes__both
.
Definition CodebookParameters__type1__multiPanel__modes__cond := (fun (_ : CodebookParameters__type1__multiPanel__modes__Type) => True).
Lemma CodebookParameters__type1__multiPanel__modes__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CodebookParameters__type1__multiPanel__modes__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CodebookParameters__type1__multiPanel__modes__nat__helper.

Definition CodebookParameters__type1__multiPanel__modes__F1 t :=
  match t with
  | CodebookParameters__type1__multiPanel__modes__mode1 => 0
  | CodebookParameters__type1__multiPanel__modes__mode2 => 1
  | CodebookParameters__type1__multiPanel__modes__both => 2
  end.
Definition CodebookParameters__type1__multiPanel__modes__F2 n :=
  match n with
  | 0 => CodebookParameters__type1__multiPanel__modes__mode1
  | 1 => CodebookParameters__type1__multiPanel__modes__mode2
  | 2 => CodebookParameters__type1__multiPanel__modes__both
  | _ => CodebookParameters__type1__multiPanel__modes__mode1
  end.
Lemma CodebookParameters__type1__multiPanel__modes__F1F2 : forall x : CodebookParameters__type1__multiPanel__modes__Type, (CodebookParameters__type1__multiPanel__modes__F1 x <= 2) /\ CodebookParameters__type1__multiPanel__modes__F2 (CodebookParameters__type1__multiPanel__modes__F1 x) = x. imp_solve. Qed.
Lemma CodebookParameters__type1__multiPanel__modes__F2F1 : forall (y : nat) (H : y <= 2), CodebookParameters__type1__multiPanel__modes__F1 (CodebookParameters__type1__multiPanel__modes__F2 y) = y. enum_solve H y. Qed.

Inductive CodebookParameters__type1__multiPanel__nrofPanels__Type : Set :=
 | CodebookParameters__type1__multiPanel__nrofPanels__n2
 | CodebookParameters__type1__multiPanel__nrofPanels__n4
.
Definition CodebookParameters__type1__multiPanel__nrofPanels__cond := (fun (_ : CodebookParameters__type1__multiPanel__nrofPanels__Type) => True).
Lemma CodebookParameters__type1__multiPanel__nrofPanels__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CodebookParameters__type1__multiPanel__nrofPanels__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CodebookParameters__type1__multiPanel__nrofPanels__nat__helper.

Definition CodebookParameters__type1__multiPanel__nrofPanels__F1 t :=
  match t with
  | CodebookParameters__type1__multiPanel__nrofPanels__n2 => 0
  | CodebookParameters__type1__multiPanel__nrofPanels__n4 => 1
  end.
Definition CodebookParameters__type1__multiPanel__nrofPanels__F2 n :=
  match n with
  | 0 => CodebookParameters__type1__multiPanel__nrofPanels__n2
  | 1 => CodebookParameters__type1__multiPanel__nrofPanels__n4
  | _ => CodebookParameters__type1__multiPanel__nrofPanels__n2
  end.
Lemma CodebookParameters__type1__multiPanel__nrofPanels__F1F2 : forall x : CodebookParameters__type1__multiPanel__nrofPanels__Type, (CodebookParameters__type1__multiPanel__nrofPanels__F1 x <= 1) /\ CodebookParameters__type1__multiPanel__nrofPanels__F2 (CodebookParameters__type1__multiPanel__nrofPanels__F1 x) = x. imp_solve. Qed.
Lemma CodebookParameters__type1__multiPanel__nrofPanels__F2F1 : forall (y : nat) (H : y <= 1), CodebookParameters__type1__multiPanel__nrofPanels__F1 (CodebookParameters__type1__multiPanel__nrofPanels__F2 y) = y. enum_solve H y. Qed.

Lemma CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__Type := Z.
Definition CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record CodebookParameters__type1__multiPanel__Type : Set :=
  make__CodebookParameters__type1__multiPanel__Type {
    CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList : CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Type ;
    CodebookParameters__type1__multiPanel__modes : CodebookParameters__type1__multiPanel__modes__Type ;
    CodebookParameters__type1__multiPanel__nrofPanels : CodebookParameters__type1__multiPanel__nrofPanels__Type ;
    CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet : Z ;
}.
Definition CodebookParameters__type1__multiPanel__list := (
 Nor CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Type CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__cond ::
 Nor CodebookParameters__type1__multiPanel__modes__Type CodebookParameters__type1__multiPanel__modes__cond ::
 Nor CodebookParameters__type1__multiPanel__nrofPanels__Type CodebookParameters__type1__multiPanel__nrofPanels__cond ::
 Nor Z CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__cond ::
 nil).
Definition CodebookParameters__type1__multiPanel__cond z := 
  CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__cond (CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList z) /\
  CodebookParameters__type1__multiPanel__modes__cond (CodebookParameters__type1__multiPanel__modes z) /\
  CodebookParameters__type1__multiPanel__nrofPanels__cond (CodebookParameters__type1__multiPanel__nrofPanels z) /\
  CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__cond (CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet z) /\
  True.

Record CodebookParameters__type1__Type : Set :=
  make__CodebookParameters__type1__Type {
    CodebookParameters__type1__singlePanel : CodebookParameters__type1__singlePanel__Type ;
    CodebookParameters__type1__multiPanel : option CodebookParameters__type1__multiPanel__Type ;
}.
Definition CodebookParameters__type1__list := (
 Nor CodebookParameters__type1__singlePanel__Type CodebookParameters__type1__singlePanel__cond ::
 Opt CodebookParameters__type1__multiPanel__Type CodebookParameters__type1__multiPanel__cond ::
 nil).
Definition CodebookParameters__type1__cond z := 
  CodebookParameters__type1__singlePanel__cond (CodebookParameters__type1__singlePanel z) /\
  opt_cond CodebookParameters__type1__multiPanel__cond (CodebookParameters__type1__multiPanel z) /\
  True.

Require Import NR.SupportedCSI_RS_Resource.

Opaque SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__Format.

Definition CodebookParameters__type2__supportedCSI_RS_ResourceList__Type := list SupportedCSI_RS_Resource__Type.

Lemma CodebookParameters__type2__supportedCSI_RS_ResourceList__helper1 : (0 <= 1 <= maxNrofCSI_RS_Resources)%Z. unfold maxNrofCSI_RS_Resources.
 lia. Qed.
Lemma CodebookParameters__type2__supportedCSI_RS_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type2__supportedCSI_RS_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type2__supportedCSI_RS_ResourceList__cond (z : CodebookParameters__type2__supportedCSI_RS_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_Resources)%Z /\ (list_and SupportedCSI_RS_Resource__cond z) .

Lemma CodebookParameters__type2__parameterLx__helper1 : (2 <= 4)%Z.  lia. Qed.
Lemma CodebookParameters__type2__parameterLx__helper2 : to_bit_sz (Z.to_nat (4 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type2__parameterLx__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type2__parameterLx__Type := Z.
Definition CodebookParameters__type2__parameterLx__cond := (fun z => (2 <= z <= 4)%Z).
Inductive CodebookParameters__type2__amplitudeScalingType__Type : Set :=
 | CodebookParameters__type2__amplitudeScalingType__wideband
 | CodebookParameters__type2__amplitudeScalingType__widebandAndSubband
.
Definition CodebookParameters__type2__amplitudeScalingType__cond := (fun (_ : CodebookParameters__type2__amplitudeScalingType__Type) => True).
Lemma CodebookParameters__type2__amplitudeScalingType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CodebookParameters__type2__amplitudeScalingType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CodebookParameters__type2__amplitudeScalingType__nat__helper.

Definition CodebookParameters__type2__amplitudeScalingType__F1 t :=
  match t with
  | CodebookParameters__type2__amplitudeScalingType__wideband => 0
  | CodebookParameters__type2__amplitudeScalingType__widebandAndSubband => 1
  end.
Definition CodebookParameters__type2__amplitudeScalingType__F2 n :=
  match n with
  | 0 => CodebookParameters__type2__amplitudeScalingType__wideband
  | 1 => CodebookParameters__type2__amplitudeScalingType__widebandAndSubband
  | _ => CodebookParameters__type2__amplitudeScalingType__wideband
  end.
Lemma CodebookParameters__type2__amplitudeScalingType__F1F2 : forall x : CodebookParameters__type2__amplitudeScalingType__Type, (CodebookParameters__type2__amplitudeScalingType__F1 x <= 1) /\ CodebookParameters__type2__amplitudeScalingType__F2 (CodebookParameters__type2__amplitudeScalingType__F1 x) = x. imp_solve. Qed.
Lemma CodebookParameters__type2__amplitudeScalingType__F2F1 : forall (y : nat) (H : y <= 1), CodebookParameters__type2__amplitudeScalingType__F1 (CodebookParameters__type2__amplitudeScalingType__F2 y) = y. enum_solve H y. Qed.

Inductive CodebookParameters__type2__amplitudeSubsetRestriction__Type : Set :=
 | CodebookParameters__type2__amplitudeSubsetRestriction__supported
.
Definition CodebookParameters__type2__amplitudeSubsetRestriction__cond := (fun (_ : CodebookParameters__type2__amplitudeSubsetRestriction__Type) => True).
Lemma CodebookParameters__type2__amplitudeSubsetRestriction__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CodebookParameters__type2__amplitudeSubsetRestriction__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CodebookParameters__type2__amplitudeSubsetRestriction__nat__helper.

Definition CodebookParameters__type2__amplitudeSubsetRestriction__F1 t :=
  match t with
  | CodebookParameters__type2__amplitudeSubsetRestriction__supported => 0
  end.
Definition CodebookParameters__type2__amplitudeSubsetRestriction__F2 n :=
  match n with
  | 0 => CodebookParameters__type2__amplitudeSubsetRestriction__supported
  | _ => CodebookParameters__type2__amplitudeSubsetRestriction__supported
  end.
Lemma CodebookParameters__type2__amplitudeSubsetRestriction__F1F2 : forall x : CodebookParameters__type2__amplitudeSubsetRestriction__Type, (CodebookParameters__type2__amplitudeSubsetRestriction__F1 x <= 0) /\ CodebookParameters__type2__amplitudeSubsetRestriction__F2 (CodebookParameters__type2__amplitudeSubsetRestriction__F1 x) = x. imp_solve. Qed.
Lemma CodebookParameters__type2__amplitudeSubsetRestriction__F2F1 : forall (y : nat) (H : y <= 0), CodebookParameters__type2__amplitudeSubsetRestriction__F1 (CodebookParameters__type2__amplitudeSubsetRestriction__F2 y) = y. enum_solve H y. Qed.

Record CodebookParameters__type2__Type : Set :=
  make__CodebookParameters__type2__Type {
    CodebookParameters__type2__supportedCSI_RS_ResourceList : CodebookParameters__type2__supportedCSI_RS_ResourceList__Type ;
    CodebookParameters__type2__parameterLx : Z ;
    CodebookParameters__type2__amplitudeScalingType : CodebookParameters__type2__amplitudeScalingType__Type ;
    CodebookParameters__type2__amplitudeSubsetRestriction : option CodebookParameters__type2__amplitudeSubsetRestriction__Type ;
}.
Definition CodebookParameters__type2__list := (
 Nor CodebookParameters__type2__supportedCSI_RS_ResourceList__Type CodebookParameters__type2__supportedCSI_RS_ResourceList__cond ::
 Nor Z CodebookParameters__type2__parameterLx__cond ::
 Nor CodebookParameters__type2__amplitudeScalingType__Type CodebookParameters__type2__amplitudeScalingType__cond ::
 Opt CodebookParameters__type2__amplitudeSubsetRestriction__Type CodebookParameters__type2__amplitudeSubsetRestriction__cond ::
 nil).
Definition CodebookParameters__type2__cond z := 
  CodebookParameters__type2__supportedCSI_RS_ResourceList__cond (CodebookParameters__type2__supportedCSI_RS_ResourceList z) /\
  CodebookParameters__type2__parameterLx__cond (CodebookParameters__type2__parameterLx z) /\
  CodebookParameters__type2__amplitudeScalingType__cond (CodebookParameters__type2__amplitudeScalingType z) /\
  opt_cond CodebookParameters__type2__amplitudeSubsetRestriction__cond (CodebookParameters__type2__amplitudeSubsetRestriction z) /\
  True.

Require Import NR.SupportedCSI_RS_Resource.

Opaque SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__Format.

Definition CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Type := list SupportedCSI_RS_Resource__Type.

Lemma CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__helper1 : (0 <= 1 <= maxNrofCSI_RS_Resources)%Z. unfold maxNrofCSI_RS_Resources.
 lia. Qed.
Lemma CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__cond (z : CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_Resources)%Z /\ (list_and SupportedCSI_RS_Resource__cond z) .

Lemma CodebookParameters__type2_PortSelection__parameterLx__helper1 : (2 <= 4)%Z.  lia. Qed.
Lemma CodebookParameters__type2_PortSelection__parameterLx__helper2 : to_bit_sz (Z.to_nat (4 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookParameters__type2_PortSelection__parameterLx__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookParameters__type2_PortSelection__parameterLx__Type := Z.
Definition CodebookParameters__type2_PortSelection__parameterLx__cond := (fun z => (2 <= z <= 4)%Z).
Inductive CodebookParameters__type2_PortSelection__amplitudeScalingType__Type : Set :=
 | CodebookParameters__type2_PortSelection__amplitudeScalingType__wideband
 | CodebookParameters__type2_PortSelection__amplitudeScalingType__widebandAndSubband
.
Definition CodebookParameters__type2_PortSelection__amplitudeScalingType__cond := (fun (_ : CodebookParameters__type2_PortSelection__amplitudeScalingType__Type) => True).
Lemma CodebookParameters__type2_PortSelection__amplitudeScalingType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CodebookParameters__type2_PortSelection__amplitudeScalingType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CodebookParameters__type2_PortSelection__amplitudeScalingType__nat__helper.

Definition CodebookParameters__type2_PortSelection__amplitudeScalingType__F1 t :=
  match t with
  | CodebookParameters__type2_PortSelection__amplitudeScalingType__wideband => 0
  | CodebookParameters__type2_PortSelection__amplitudeScalingType__widebandAndSubband => 1
  end.
Definition CodebookParameters__type2_PortSelection__amplitudeScalingType__F2 n :=
  match n with
  | 0 => CodebookParameters__type2_PortSelection__amplitudeScalingType__wideband
  | 1 => CodebookParameters__type2_PortSelection__amplitudeScalingType__widebandAndSubband
  | _ => CodebookParameters__type2_PortSelection__amplitudeScalingType__wideband
  end.
Lemma CodebookParameters__type2_PortSelection__amplitudeScalingType__F1F2 : forall x : CodebookParameters__type2_PortSelection__amplitudeScalingType__Type, (CodebookParameters__type2_PortSelection__amplitudeScalingType__F1 x <= 1) /\ CodebookParameters__type2_PortSelection__amplitudeScalingType__F2 (CodebookParameters__type2_PortSelection__amplitudeScalingType__F1 x) = x. imp_solve. Qed.
Lemma CodebookParameters__type2_PortSelection__amplitudeScalingType__F2F1 : forall (y : nat) (H : y <= 1), CodebookParameters__type2_PortSelection__amplitudeScalingType__F1 (CodebookParameters__type2_PortSelection__amplitudeScalingType__F2 y) = y. enum_solve H y. Qed.

Record CodebookParameters__type2_PortSelection__Type : Set :=
  make__CodebookParameters__type2_PortSelection__Type {
    CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList : CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Type ;
    CodebookParameters__type2_PortSelection__parameterLx : Z ;
    CodebookParameters__type2_PortSelection__amplitudeScalingType : CodebookParameters__type2_PortSelection__amplitudeScalingType__Type ;
}.
Definition CodebookParameters__type2_PortSelection__list := (
 Nor CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Type CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__cond ::
 Nor Z CodebookParameters__type2_PortSelection__parameterLx__cond ::
 Nor CodebookParameters__type2_PortSelection__amplitudeScalingType__Type CodebookParameters__type2_PortSelection__amplitudeScalingType__cond ::
 nil).
Definition CodebookParameters__type2_PortSelection__cond z := 
  CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__cond (CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList z) /\
  CodebookParameters__type2_PortSelection__parameterLx__cond (CodebookParameters__type2_PortSelection__parameterLx z) /\
  CodebookParameters__type2_PortSelection__amplitudeScalingType__cond (CodebookParameters__type2_PortSelection__amplitudeScalingType z) /\
  True.

Record CodebookParameters__Type : Set :=
  make__CodebookParameters__Type {
    CodebookParameters__type1 : CodebookParameters__type1__Type ;
    CodebookParameters__type2 : option CodebookParameters__type2__Type ;
    CodebookParameters__type2_PortSelection : option CodebookParameters__type2_PortSelection__Type ;
}.
Definition CodebookParameters__list := (
 Nor CodebookParameters__type1__Type CodebookParameters__type1__cond ::
 Opt CodebookParameters__type2__Type CodebookParameters__type2__cond ::
 Opt CodebookParameters__type2_PortSelection__Type CodebookParameters__type2_PortSelection__cond ::
 nil).
Definition CodebookParameters__cond z := 
  CodebookParameters__type1__cond (CodebookParameters__type1 z) /\
  opt_cond CodebookParameters__type2__cond (CodebookParameters__type2 z) /\
  opt_cond CodebookParameters__type2_PortSelection__cond (CodebookParameters__type2_PortSelection z) /\
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
Definition CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Format : T_Format CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Type CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__cond := seq_of_format SupportedCSI_RS_Resource__Format 1 maxNrofCSI_RS_Resources CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__helper1 CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__helper2.

Opaque CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__cond CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Format.

Definition CodebookParameters__type1__singlePanel__modes__Format : T_Format CodebookParameters__type1__singlePanel__modes__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CodebookParameters__type1__singlePanel__modes__nat__Format CodebookParameters__type1__singlePanel__modes__F1 CodebookParameters__type1__singlePanel__modes__F2 CodebookParameters__type1__singlePanel__modes__F1F2 CodebookParameters__type1__singlePanel__modes__F2F1.

Opaque CodebookParameters__type1__singlePanel__modes__cond CodebookParameters__type1__singlePanel__modes__Format.

Definition CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__Format : T_Format Z CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__cond :=
 ranged_int_format (1) (8) CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__helper1 CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__helper2.

Opaque CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__cond CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__Format.


Definition CodebookParameters__type1__singlePanel__Format_Type := Eval cbn in seq_format_prod CodebookParameters__type1__singlePanel__list.
Definition CodebookParameters__type1__singlePanel__Format_list : CodebookParameters__type1__singlePanel__Format_Type :=
  (CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList__Format, (CodebookParameters__type1__singlePanel__modes__Format, (CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet__Format, unit_format))).
Definition CodebookParameters__type1__singlePanel__list__Format := (*Eval compute in *) seq_format CodebookParameters__type1__singlePanel__list CodebookParameters__type1__singlePanel__Format_list.
Definition CodebookParameters__type1__singlePanel__F1 z :=
  (CodebookParameters__type1__singlePanel__supportedCSI_RS_ResourceList z, (CodebookParameters__type1__singlePanel__modes z, (CodebookParameters__type1__singlePanel__maxNumberCSI_RS_PerResourceSet z, tt))).
Definition CodebookParameters__type1__singlePanel__F2 (y : seq_type CodebookParameters__type1__singlePanel__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CodebookParameters__type1__singlePanel__Type i0 i1 i2
  end.
Lemma CodebookParameters__type1__singlePanel__F1F2_cond (z : CodebookParameters__type1__singlePanel__Type)
  : CodebookParameters__type1__singlePanel__cond z ->
  (seq_cond CodebookParameters__type1__singlePanel__list (CodebookParameters__type1__singlePanel__F1 z)).
intro H. unfold CodebookParameters__type1__singlePanel__cond in H. simpl. auto. Qed.
Lemma CodebookParameters__type1__singlePanel__F1F2_cond2 (z : CodebookParameters__type1__singlePanel__Type)
 : CodebookParameters__type1__singlePanel__F2 (CodebookParameters__type1__singlePanel__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParameters__type1__singlePanel__F2F1_cond (y : seq_type CodebookParameters__type1__singlePanel__list)
  : seq_cond CodebookParameters__type1__singlePanel__list y ->
 (CodebookParameters__type1__singlePanel__cond (CodebookParameters__type1__singlePanel__F2 y)) /\  CodebookParameters__type1__singlePanel__F1 (CodebookParameters__type1__singlePanel__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParameters__type1__singlePanel__cond. simpl in *. auto.
 - simpl. unfold CodebookParameters__type1__singlePanel__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParameters__type1__singlePanel__Format : T_Format CodebookParameters__type1__singlePanel__Type CodebookParameters__type1__singlePanel__cond :=
        proj2_format  CodebookParameters__type1__singlePanel__cond CodebookParameters__type1__singlePanel__list__Format
    CodebookParameters__type1__singlePanel__F1 CodebookParameters__type1__singlePanel__F2 CodebookParameters__type1__singlePanel__F1F2_cond  CodebookParameters__type1__singlePanel__F1F2_cond2 CodebookParameters__type1__singlePanel__F2F1_cond.
Opaque CodebookParameters__type1__singlePanel__cond CodebookParameters__type1__singlePanel__Format.

Definition CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Format : T_Format CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Type CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__cond := seq_of_format SupportedCSI_RS_Resource__Format 1 maxNrofCSI_RS_Resources CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__helper1 CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__helper2.

Opaque CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__cond CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Format.

Definition CodebookParameters__type1__multiPanel__modes__Format : T_Format CodebookParameters__type1__multiPanel__modes__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CodebookParameters__type1__multiPanel__modes__nat__Format CodebookParameters__type1__multiPanel__modes__F1 CodebookParameters__type1__multiPanel__modes__F2 CodebookParameters__type1__multiPanel__modes__F1F2 CodebookParameters__type1__multiPanel__modes__F2F1.

Opaque CodebookParameters__type1__multiPanel__modes__cond CodebookParameters__type1__multiPanel__modes__Format.

Definition CodebookParameters__type1__multiPanel__nrofPanels__Format : T_Format CodebookParameters__type1__multiPanel__nrofPanels__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CodebookParameters__type1__multiPanel__nrofPanels__nat__Format CodebookParameters__type1__multiPanel__nrofPanels__F1 CodebookParameters__type1__multiPanel__nrofPanels__F2 CodebookParameters__type1__multiPanel__nrofPanels__F1F2 CodebookParameters__type1__multiPanel__nrofPanels__F2F1.

Opaque CodebookParameters__type1__multiPanel__nrofPanels__cond CodebookParameters__type1__multiPanel__nrofPanels__Format.

Definition CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__Format : T_Format Z CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__cond :=
 ranged_int_format (1) (8) CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__helper1 CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__helper2.

Opaque CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__cond CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__Format.


Definition CodebookParameters__type1__multiPanel__Format_Type := Eval cbn in seq_format_prod CodebookParameters__type1__multiPanel__list.
Definition CodebookParameters__type1__multiPanel__Format_list : CodebookParameters__type1__multiPanel__Format_Type :=
  (CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList__Format, (CodebookParameters__type1__multiPanel__modes__Format, (CodebookParameters__type1__multiPanel__nrofPanels__Format, (CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet__Format, unit_format)))).
Definition CodebookParameters__type1__multiPanel__list__Format := (*Eval compute in *) seq_format CodebookParameters__type1__multiPanel__list CodebookParameters__type1__multiPanel__Format_list.
Definition CodebookParameters__type1__multiPanel__F1 z :=
  (CodebookParameters__type1__multiPanel__supportedCSI_RS_ResourceList z, (CodebookParameters__type1__multiPanel__modes z, (CodebookParameters__type1__multiPanel__nrofPanels z, (CodebookParameters__type1__multiPanel__maxNumberCSI_RS_PerResourceSet z, tt)))).
Definition CodebookParameters__type1__multiPanel__F2 (y : seq_type CodebookParameters__type1__multiPanel__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CodebookParameters__type1__multiPanel__Type i0 i1 i2 i3
  end.
Lemma CodebookParameters__type1__multiPanel__F1F2_cond (z : CodebookParameters__type1__multiPanel__Type)
  : CodebookParameters__type1__multiPanel__cond z ->
  (seq_cond CodebookParameters__type1__multiPanel__list (CodebookParameters__type1__multiPanel__F1 z)).
intro H. unfold CodebookParameters__type1__multiPanel__cond in H. simpl. auto. Qed.
Lemma CodebookParameters__type1__multiPanel__F1F2_cond2 (z : CodebookParameters__type1__multiPanel__Type)
 : CodebookParameters__type1__multiPanel__F2 (CodebookParameters__type1__multiPanel__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParameters__type1__multiPanel__F2F1_cond (y : seq_type CodebookParameters__type1__multiPanel__list)
  : seq_cond CodebookParameters__type1__multiPanel__list y ->
 (CodebookParameters__type1__multiPanel__cond (CodebookParameters__type1__multiPanel__F2 y)) /\  CodebookParameters__type1__multiPanel__F1 (CodebookParameters__type1__multiPanel__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParameters__type1__multiPanel__cond. simpl in *. auto.
 - simpl. unfold CodebookParameters__type1__multiPanel__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParameters__type1__multiPanel__Format : T_Format CodebookParameters__type1__multiPanel__Type CodebookParameters__type1__multiPanel__cond :=
        proj2_format  CodebookParameters__type1__multiPanel__cond CodebookParameters__type1__multiPanel__list__Format
    CodebookParameters__type1__multiPanel__F1 CodebookParameters__type1__multiPanel__F2 CodebookParameters__type1__multiPanel__F1F2_cond  CodebookParameters__type1__multiPanel__F1F2_cond2 CodebookParameters__type1__multiPanel__F2F1_cond.
Opaque CodebookParameters__type1__multiPanel__cond CodebookParameters__type1__multiPanel__Format.


Definition CodebookParameters__type1__Format_Type := Eval cbn in seq_format_prod CodebookParameters__type1__list.
Definition CodebookParameters__type1__Format_list : CodebookParameters__type1__Format_Type :=
  (CodebookParameters__type1__singlePanel__Format, (CodebookParameters__type1__multiPanel__Format, unit_format)).
Definition CodebookParameters__type1__list__Format := (*Eval compute in *) seq_format CodebookParameters__type1__list CodebookParameters__type1__Format_list.
Definition CodebookParameters__type1__F1 z :=
  (CodebookParameters__type1__singlePanel z, (CodebookParameters__type1__multiPanel z, tt)).
Definition CodebookParameters__type1__F2 (y : seq_type CodebookParameters__type1__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CodebookParameters__type1__Type i0 i1
  end.
Lemma CodebookParameters__type1__F1F2_cond (z : CodebookParameters__type1__Type)
  : CodebookParameters__type1__cond z ->
  (seq_cond CodebookParameters__type1__list (CodebookParameters__type1__F1 z)).
intro H. unfold CodebookParameters__type1__cond in H. simpl. auto. Qed.
Lemma CodebookParameters__type1__F1F2_cond2 (z : CodebookParameters__type1__Type)
 : CodebookParameters__type1__F2 (CodebookParameters__type1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParameters__type1__F2F1_cond (y : seq_type CodebookParameters__type1__list)
  : seq_cond CodebookParameters__type1__list y ->
 (CodebookParameters__type1__cond (CodebookParameters__type1__F2 y)) /\  CodebookParameters__type1__F1 (CodebookParameters__type1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParameters__type1__cond. simpl in *. auto.
 - simpl. unfold CodebookParameters__type1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParameters__type1__Format : T_Format CodebookParameters__type1__Type CodebookParameters__type1__cond :=
        proj2_format  CodebookParameters__type1__cond CodebookParameters__type1__list__Format
    CodebookParameters__type1__F1 CodebookParameters__type1__F2 CodebookParameters__type1__F1F2_cond  CodebookParameters__type1__F1F2_cond2 CodebookParameters__type1__F2F1_cond.
Opaque CodebookParameters__type1__cond CodebookParameters__type1__Format.

Definition CodebookParameters__type2__supportedCSI_RS_ResourceList__Format : T_Format CodebookParameters__type2__supportedCSI_RS_ResourceList__Type CodebookParameters__type2__supportedCSI_RS_ResourceList__cond := seq_of_format SupportedCSI_RS_Resource__Format 1 maxNrofCSI_RS_Resources CodebookParameters__type2__supportedCSI_RS_ResourceList__helper1 CodebookParameters__type2__supportedCSI_RS_ResourceList__helper2.

Opaque CodebookParameters__type2__supportedCSI_RS_ResourceList__cond CodebookParameters__type2__supportedCSI_RS_ResourceList__Format.

Definition CodebookParameters__type2__parameterLx__Format : T_Format Z CodebookParameters__type2__parameterLx__cond :=
 ranged_int_format (2) (4) CodebookParameters__type2__parameterLx__helper1 CodebookParameters__type2__parameterLx__helper2.

Opaque CodebookParameters__type2__parameterLx__cond CodebookParameters__type2__parameterLx__Format.

Definition CodebookParameters__type2__amplitudeScalingType__Format : T_Format CodebookParameters__type2__amplitudeScalingType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CodebookParameters__type2__amplitudeScalingType__nat__Format CodebookParameters__type2__amplitudeScalingType__F1 CodebookParameters__type2__amplitudeScalingType__F2 CodebookParameters__type2__amplitudeScalingType__F1F2 CodebookParameters__type2__amplitudeScalingType__F2F1.

Opaque CodebookParameters__type2__amplitudeScalingType__cond CodebookParameters__type2__amplitudeScalingType__Format.

Definition CodebookParameters__type2__amplitudeSubsetRestriction__Format : T_Format CodebookParameters__type2__amplitudeSubsetRestriction__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CodebookParameters__type2__amplitudeSubsetRestriction__nat__Format CodebookParameters__type2__amplitudeSubsetRestriction__F1 CodebookParameters__type2__amplitudeSubsetRestriction__F2 CodebookParameters__type2__amplitudeSubsetRestriction__F1F2 CodebookParameters__type2__amplitudeSubsetRestriction__F2F1.

Opaque CodebookParameters__type2__amplitudeSubsetRestriction__cond CodebookParameters__type2__amplitudeSubsetRestriction__Format.


Definition CodebookParameters__type2__Format_Type := Eval cbn in seq_format_prod CodebookParameters__type2__list.
Definition CodebookParameters__type2__Format_list : CodebookParameters__type2__Format_Type :=
  (CodebookParameters__type2__supportedCSI_RS_ResourceList__Format, (CodebookParameters__type2__parameterLx__Format, (CodebookParameters__type2__amplitudeScalingType__Format, (CodebookParameters__type2__amplitudeSubsetRestriction__Format, unit_format)))).
Definition CodebookParameters__type2__list__Format := (*Eval compute in *) seq_format CodebookParameters__type2__list CodebookParameters__type2__Format_list.
Definition CodebookParameters__type2__F1 z :=
  (CodebookParameters__type2__supportedCSI_RS_ResourceList z, (CodebookParameters__type2__parameterLx z, (CodebookParameters__type2__amplitudeScalingType z, (CodebookParameters__type2__amplitudeSubsetRestriction z, tt)))).
Definition CodebookParameters__type2__F2 (y : seq_type CodebookParameters__type2__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CodebookParameters__type2__Type i0 i1 i2 i3
  end.
Lemma CodebookParameters__type2__F1F2_cond (z : CodebookParameters__type2__Type)
  : CodebookParameters__type2__cond z ->
  (seq_cond CodebookParameters__type2__list (CodebookParameters__type2__F1 z)).
intro H. unfold CodebookParameters__type2__cond in H. simpl. auto. Qed.
Lemma CodebookParameters__type2__F1F2_cond2 (z : CodebookParameters__type2__Type)
 : CodebookParameters__type2__F2 (CodebookParameters__type2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParameters__type2__F2F1_cond (y : seq_type CodebookParameters__type2__list)
  : seq_cond CodebookParameters__type2__list y ->
 (CodebookParameters__type2__cond (CodebookParameters__type2__F2 y)) /\  CodebookParameters__type2__F1 (CodebookParameters__type2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParameters__type2__cond. simpl in *. auto.
 - simpl. unfold CodebookParameters__type2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParameters__type2__Format : T_Format CodebookParameters__type2__Type CodebookParameters__type2__cond :=
        proj2_format  CodebookParameters__type2__cond CodebookParameters__type2__list__Format
    CodebookParameters__type2__F1 CodebookParameters__type2__F2 CodebookParameters__type2__F1F2_cond  CodebookParameters__type2__F1F2_cond2 CodebookParameters__type2__F2F1_cond.
Opaque CodebookParameters__type2__cond CodebookParameters__type2__Format.

Definition CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Format : T_Format CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Type CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__cond := seq_of_format SupportedCSI_RS_Resource__Format 1 maxNrofCSI_RS_Resources CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__helper1 CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__helper2.

Opaque CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__cond CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Format.

Definition CodebookParameters__type2_PortSelection__parameterLx__Format : T_Format Z CodebookParameters__type2_PortSelection__parameterLx__cond :=
 ranged_int_format (2) (4) CodebookParameters__type2_PortSelection__parameterLx__helper1 CodebookParameters__type2_PortSelection__parameterLx__helper2.

Opaque CodebookParameters__type2_PortSelection__parameterLx__cond CodebookParameters__type2_PortSelection__parameterLx__Format.

Definition CodebookParameters__type2_PortSelection__amplitudeScalingType__Format : T_Format CodebookParameters__type2_PortSelection__amplitudeScalingType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CodebookParameters__type2_PortSelection__amplitudeScalingType__nat__Format CodebookParameters__type2_PortSelection__amplitudeScalingType__F1 CodebookParameters__type2_PortSelection__amplitudeScalingType__F2 CodebookParameters__type2_PortSelection__amplitudeScalingType__F1F2 CodebookParameters__type2_PortSelection__amplitudeScalingType__F2F1.

Opaque CodebookParameters__type2_PortSelection__amplitudeScalingType__cond CodebookParameters__type2_PortSelection__amplitudeScalingType__Format.


Definition CodebookParameters__type2_PortSelection__Format_Type := Eval cbn in seq_format_prod CodebookParameters__type2_PortSelection__list.
Definition CodebookParameters__type2_PortSelection__Format_list : CodebookParameters__type2_PortSelection__Format_Type :=
  (CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList__Format, (CodebookParameters__type2_PortSelection__parameterLx__Format, (CodebookParameters__type2_PortSelection__amplitudeScalingType__Format, unit_format))).
Definition CodebookParameters__type2_PortSelection__list__Format := (*Eval compute in *) seq_format CodebookParameters__type2_PortSelection__list CodebookParameters__type2_PortSelection__Format_list.
Definition CodebookParameters__type2_PortSelection__F1 z :=
  (CodebookParameters__type2_PortSelection__supportedCSI_RS_ResourceList z, (CodebookParameters__type2_PortSelection__parameterLx z, (CodebookParameters__type2_PortSelection__amplitudeScalingType z, tt))).
Definition CodebookParameters__type2_PortSelection__F2 (y : seq_type CodebookParameters__type2_PortSelection__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CodebookParameters__type2_PortSelection__Type i0 i1 i2
  end.
Lemma CodebookParameters__type2_PortSelection__F1F2_cond (z : CodebookParameters__type2_PortSelection__Type)
  : CodebookParameters__type2_PortSelection__cond z ->
  (seq_cond CodebookParameters__type2_PortSelection__list (CodebookParameters__type2_PortSelection__F1 z)).
intro H. unfold CodebookParameters__type2_PortSelection__cond in H. simpl. auto. Qed.
Lemma CodebookParameters__type2_PortSelection__F1F2_cond2 (z : CodebookParameters__type2_PortSelection__Type)
 : CodebookParameters__type2_PortSelection__F2 (CodebookParameters__type2_PortSelection__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParameters__type2_PortSelection__F2F1_cond (y : seq_type CodebookParameters__type2_PortSelection__list)
  : seq_cond CodebookParameters__type2_PortSelection__list y ->
 (CodebookParameters__type2_PortSelection__cond (CodebookParameters__type2_PortSelection__F2 y)) /\  CodebookParameters__type2_PortSelection__F1 (CodebookParameters__type2_PortSelection__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParameters__type2_PortSelection__cond. simpl in *. auto.
 - simpl. unfold CodebookParameters__type2_PortSelection__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParameters__type2_PortSelection__Format : T_Format CodebookParameters__type2_PortSelection__Type CodebookParameters__type2_PortSelection__cond :=
        proj2_format  CodebookParameters__type2_PortSelection__cond CodebookParameters__type2_PortSelection__list__Format
    CodebookParameters__type2_PortSelection__F1 CodebookParameters__type2_PortSelection__F2 CodebookParameters__type2_PortSelection__F1F2_cond  CodebookParameters__type2_PortSelection__F1F2_cond2 CodebookParameters__type2_PortSelection__F2F1_cond.
Opaque CodebookParameters__type2_PortSelection__cond CodebookParameters__type2_PortSelection__Format.


Definition CodebookParameters__Format_Type := Eval cbn in seq_format_prod CodebookParameters__list.
Definition CodebookParameters__Format_list : CodebookParameters__Format_Type :=
  (CodebookParameters__type1__Format, (CodebookParameters__type2__Format, (CodebookParameters__type2_PortSelection__Format, unit_format))).
Definition CodebookParameters__list__Format := (*Eval compute in *) seq_format CodebookParameters__list CodebookParameters__Format_list.
Definition CodebookParameters__F1 z :=
  (CodebookParameters__type1 z, (CodebookParameters__type2 z, (CodebookParameters__type2_PortSelection z, tt))).
Definition CodebookParameters__F2 (y : seq_type CodebookParameters__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CodebookParameters__Type i0 i1 i2
  end.
Lemma CodebookParameters__F1F2_cond (z : CodebookParameters__Type)
  : CodebookParameters__cond z ->
  (seq_cond CodebookParameters__list (CodebookParameters__F1 z)).
intro H. unfold CodebookParameters__cond in H. simpl. auto. Qed.
Lemma CodebookParameters__F1F2_cond2 (z : CodebookParameters__Type)
 : CodebookParameters__F2 (CodebookParameters__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookParameters__F2F1_cond (y : seq_type CodebookParameters__list)
  : seq_cond CodebookParameters__list y ->
 (CodebookParameters__cond (CodebookParameters__F2 y)) /\  CodebookParameters__F1 (CodebookParameters__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookParameters__cond. simpl in *. auto.
 - simpl. unfold CodebookParameters__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookParameters__Format : T_Format CodebookParameters__Type CodebookParameters__cond :=
        proj2_format  CodebookParameters__cond CodebookParameters__list__Format
    CodebookParameters__F1 CodebookParameters__F2 CodebookParameters__F1F2_cond  CodebookParameters__F1F2_cond2 CodebookParameters__F2F1_cond.
Opaque CodebookParameters__cond CodebookParameters__Format.

