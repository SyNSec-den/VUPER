Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Type : Set :=
 | MAC_ParametersXDD_Diff__skipUplinkTxDynamic__supported
.
Definition MAC_ParametersXDD_Diff__skipUplinkTxDynamic__cond := (fun (_ : MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Type) => True).
Lemma MAC_ParametersXDD_Diff__skipUplinkTxDynamic__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__skipUplinkTxDynamic__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__skipUplinkTxDynamic__nat__helper.

Definition MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__skipUplinkTxDynamic__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__skipUplinkTxDynamic__supported
  | _ => MAC_ParametersXDD_Diff__skipUplinkTxDynamic__supported
  end.
Lemma MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1F2 : forall x : MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Type, (MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1 x <= 0) /\ MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F2 (MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1 (MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Type : Set :=
 | MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__supported
.
Definition MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__cond := (fun (_ : MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Type) => True).
Lemma MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__nat__helper.

Definition MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__supported
  | _ => MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__supported
  end.
Lemma MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1F2 : forall x : MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Type, (MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1 x <= 0) /\ MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F2 (MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1 (MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__longDRX_Cycle__Type : Set :=
 | MAC_ParametersXDD_Diff__longDRX_Cycle__supported
.
Definition MAC_ParametersXDD_Diff__longDRX_Cycle__cond := (fun (_ : MAC_ParametersXDD_Diff__longDRX_Cycle__Type) => True).
Lemma MAC_ParametersXDD_Diff__longDRX_Cycle__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__longDRX_Cycle__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__longDRX_Cycle__nat__helper.

Definition MAC_ParametersXDD_Diff__longDRX_Cycle__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__longDRX_Cycle__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__longDRX_Cycle__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__longDRX_Cycle__supported
  | _ => MAC_ParametersXDD_Diff__longDRX_Cycle__supported
  end.
Lemma MAC_ParametersXDD_Diff__longDRX_Cycle__F1F2 : forall x : MAC_ParametersXDD_Diff__longDRX_Cycle__Type, (MAC_ParametersXDD_Diff__longDRX_Cycle__F1 x <= 0) /\ MAC_ParametersXDD_Diff__longDRX_Cycle__F2 (MAC_ParametersXDD_Diff__longDRX_Cycle__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__longDRX_Cycle__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__longDRX_Cycle__F1 (MAC_ParametersXDD_Diff__longDRX_Cycle__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__shortDRX_Cycle__Type : Set :=
 | MAC_ParametersXDD_Diff__shortDRX_Cycle__supported
.
Definition MAC_ParametersXDD_Diff__shortDRX_Cycle__cond := (fun (_ : MAC_ParametersXDD_Diff__shortDRX_Cycle__Type) => True).
Lemma MAC_ParametersXDD_Diff__shortDRX_Cycle__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__shortDRX_Cycle__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__shortDRX_Cycle__nat__helper.

Definition MAC_ParametersXDD_Diff__shortDRX_Cycle__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__shortDRX_Cycle__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__shortDRX_Cycle__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__shortDRX_Cycle__supported
  | _ => MAC_ParametersXDD_Diff__shortDRX_Cycle__supported
  end.
Lemma MAC_ParametersXDD_Diff__shortDRX_Cycle__F1F2 : forall x : MAC_ParametersXDD_Diff__shortDRX_Cycle__Type, (MAC_ParametersXDD_Diff__shortDRX_Cycle__F1 x <= 0) /\ MAC_ParametersXDD_Diff__shortDRX_Cycle__F2 (MAC_ParametersXDD_Diff__shortDRX_Cycle__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__shortDRX_Cycle__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__shortDRX_Cycle__F1 (MAC_ParametersXDD_Diff__shortDRX_Cycle__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__multipleSR_Configurations__Type : Set :=
 | MAC_ParametersXDD_Diff__multipleSR_Configurations__supported
.
Definition MAC_ParametersXDD_Diff__multipleSR_Configurations__cond := (fun (_ : MAC_ParametersXDD_Diff__multipleSR_Configurations__Type) => True).
Lemma MAC_ParametersXDD_Diff__multipleSR_Configurations__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__multipleSR_Configurations__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__multipleSR_Configurations__nat__helper.

Definition MAC_ParametersXDD_Diff__multipleSR_Configurations__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__multipleSR_Configurations__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__multipleSR_Configurations__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__multipleSR_Configurations__supported
  | _ => MAC_ParametersXDD_Diff__multipleSR_Configurations__supported
  end.
Lemma MAC_ParametersXDD_Diff__multipleSR_Configurations__F1F2 : forall x : MAC_ParametersXDD_Diff__multipleSR_Configurations__Type, (MAC_ParametersXDD_Diff__multipleSR_Configurations__F1 x <= 0) /\ MAC_ParametersXDD_Diff__multipleSR_Configurations__F2 (MAC_ParametersXDD_Diff__multipleSR_Configurations__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__multipleSR_Configurations__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__multipleSR_Configurations__F1 (MAC_ParametersXDD_Diff__multipleSR_Configurations__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__multipleConfiguredGrants__Type : Set :=
 | MAC_ParametersXDD_Diff__multipleConfiguredGrants__supported
.
Definition MAC_ParametersXDD_Diff__multipleConfiguredGrants__cond := (fun (_ : MAC_ParametersXDD_Diff__multipleConfiguredGrants__Type) => True).
Lemma MAC_ParametersXDD_Diff__multipleConfiguredGrants__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__multipleConfiguredGrants__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__multipleConfiguredGrants__nat__helper.

Definition MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__multipleConfiguredGrants__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__multipleConfiguredGrants__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__multipleConfiguredGrants__supported
  | _ => MAC_ParametersXDD_Diff__multipleConfiguredGrants__supported
  end.
Lemma MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1F2 : forall x : MAC_ParametersXDD_Diff__multipleConfiguredGrants__Type, (MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1 x <= 0) /\ MAC_ParametersXDD_Diff__multipleConfiguredGrants__F2 (MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__multipleConfiguredGrants__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1 (MAC_ParametersXDD_Diff__multipleConfiguredGrants__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Type : Set :=
 | MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__supported
.
Definition MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__cond := (fun (_ : MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Type) => True).
Lemma MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__nat__helper.

Definition MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__supported
  | _ => MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__supported
  end.
Lemma MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1F2 : forall x : MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Type, (MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1 x <= 0) /\ MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F2 (MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1 (MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersXDD_Diff__ext0O__Type : Set :=
  make__MAC_ParametersXDD_Diff__ext0O__Type {
    MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16 : option MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Type ;
}.
Definition MAC_ParametersXDD_Diff__ext0O__list := (
 Opt MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Type MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__cond ::
 nil).
Definition MAC_ParametersXDD_Diff__ext0O__cond z := 
  opt_cond MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__cond (MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16 z) /\
  True.

Definition MAC_ParametersXDD_Diff__ext0__Type := MAC_ParametersXDD_Diff__ext0O__Type.
Definition MAC_ParametersXDD_Diff__ext0__cond := MAC_ParametersXDD_Diff__ext0O__cond.

Inductive MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Type : Set :=
 | MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__supported
.
Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__cond := (fun (_ : MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Type) => True).
Lemma MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__nat__helper.

Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__supported
  | _ => MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__supported
  end.
Lemma MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1F2 : forall x : MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Type, (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1 x <= 0) /\ MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F2 (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1 (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Type : Set :=
 | MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__supported
.
Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__cond := (fun (_ : MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Type) => True).
Lemma MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__nat__helper.

Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1 t :=
  match t with
  | MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__supported => 0
  end.
Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__supported
  | _ => MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__supported
  end.
Lemma MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1F2 : forall x : MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Type, (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1 x <= 0) /\ MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F2 (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1 (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersXDD_Diff__ext1O__Type : Set :=
  make__MAC_ParametersXDD_Diff__ext1O__Type {
    MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16 : option MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Type ;
    MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16 : option MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Type ;
}.
Definition MAC_ParametersXDD_Diff__ext1O__list := (
 Opt MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Type MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__cond ::
 Opt MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Type MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__cond ::
 nil).
Definition MAC_ParametersXDD_Diff__ext1O__cond z := 
  opt_cond MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__cond (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16 z) /\
  opt_cond MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__cond (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16 z) /\
  True.

Definition MAC_ParametersXDD_Diff__ext1__Type := MAC_ParametersXDD_Diff__ext1O__Type.
Definition MAC_ParametersXDD_Diff__ext1__cond := MAC_ParametersXDD_Diff__ext1O__cond.

Record MAC_ParametersXDD_Diff__Type : Set :=
  make__MAC_ParametersXDD_Diff__Type {
    MAC_ParametersXDD_Diff__skipUplinkTxDynamic : option MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Type ;
    MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer : option MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Type ;
    MAC_ParametersXDD_Diff__longDRX_Cycle : option MAC_ParametersXDD_Diff__longDRX_Cycle__Type ;
    MAC_ParametersXDD_Diff__shortDRX_Cycle : option MAC_ParametersXDD_Diff__shortDRX_Cycle__Type ;
    MAC_ParametersXDD_Diff__multipleSR_Configurations : option MAC_ParametersXDD_Diff__multipleSR_Configurations__Type ;
    MAC_ParametersXDD_Diff__multipleConfiguredGrants : option MAC_ParametersXDD_Diff__multipleConfiguredGrants__Type ;
    MAC_ParametersXDD_Diff__ext0 : option MAC_ParametersXDD_Diff__ext0__Type ;
    MAC_ParametersXDD_Diff__ext1 : option MAC_ParametersXDD_Diff__ext1__Type ;
}.
Definition MAC_ParametersXDD_Diff__root_list : list seq_elem := (
 Opt MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Type MAC_ParametersXDD_Diff__skipUplinkTxDynamic__cond ::
 Opt MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Type MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__cond ::
 Opt MAC_ParametersXDD_Diff__longDRX_Cycle__Type MAC_ParametersXDD_Diff__longDRX_Cycle__cond ::
 Opt MAC_ParametersXDD_Diff__shortDRX_Cycle__Type MAC_ParametersXDD_Diff__shortDRX_Cycle__cond ::
 Opt MAC_ParametersXDD_Diff__multipleSR_Configurations__Type MAC_ParametersXDD_Diff__multipleSR_Configurations__cond ::
 Opt MAC_ParametersXDD_Diff__multipleConfiguredGrants__Type MAC_ParametersXDD_Diff__multipleConfiguredGrants__cond ::
 nil).
Definition MAC_ParametersXDD_Diff__ext_list : list typ := (
  typ_cons MAC_ParametersXDD_Diff__ext0__Type MAC_ParametersXDD_Diff__ext0__cond ::
  typ_cons MAC_ParametersXDD_Diff__ext1__Type MAC_ParametersXDD_Diff__ext1__cond ::
  nil).
Definition MAC_ParametersXDD_Diff__cond (z : MAC_ParametersXDD_Diff__Type) := 
(  opt_cond MAC_ParametersXDD_Diff__skipUplinkTxDynamic__cond (MAC_ParametersXDD_Diff__skipUplinkTxDynamic z) /\
  opt_cond MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__cond (MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer z) /\
  opt_cond MAC_ParametersXDD_Diff__longDRX_Cycle__cond (MAC_ParametersXDD_Diff__longDRX_Cycle z) /\
  opt_cond MAC_ParametersXDD_Diff__shortDRX_Cycle__cond (MAC_ParametersXDD_Diff__shortDRX_Cycle z) /\
  opt_cond MAC_ParametersXDD_Diff__multipleSR_Configurations__cond (MAC_ParametersXDD_Diff__multipleSR_Configurations z) /\
  opt_cond MAC_ParametersXDD_Diff__multipleConfiguredGrants__cond (MAC_ParametersXDD_Diff__multipleConfiguredGrants z) /\
  True) /\ 
(  opt_cond MAC_ParametersXDD_Diff__ext0__cond (MAC_ParametersXDD_Diff__ext0 z) /\
  opt_cond MAC_ParametersXDD_Diff__ext1__cond (MAC_ParametersXDD_Diff__ext1 z) /\
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
Definition MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Format : T_Format MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__skipUplinkTxDynamic__nat__Format MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1 MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F2 MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F1F2 MAC_ParametersXDD_Diff__skipUplinkTxDynamic__F2F1.

Opaque MAC_ParametersXDD_Diff__skipUplinkTxDynamic__cond MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Format.

Definition MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Format : T_Format MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__nat__Format MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1 MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F2 MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F1F2 MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__F2F1.

Opaque MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__cond MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Format.

Definition MAC_ParametersXDD_Diff__longDRX_Cycle__Format : T_Format MAC_ParametersXDD_Diff__longDRX_Cycle__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__longDRX_Cycle__nat__Format MAC_ParametersXDD_Diff__longDRX_Cycle__F1 MAC_ParametersXDD_Diff__longDRX_Cycle__F2 MAC_ParametersXDD_Diff__longDRX_Cycle__F1F2 MAC_ParametersXDD_Diff__longDRX_Cycle__F2F1.

Opaque MAC_ParametersXDD_Diff__longDRX_Cycle__cond MAC_ParametersXDD_Diff__longDRX_Cycle__Format.

Definition MAC_ParametersXDD_Diff__shortDRX_Cycle__Format : T_Format MAC_ParametersXDD_Diff__shortDRX_Cycle__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__shortDRX_Cycle__nat__Format MAC_ParametersXDD_Diff__shortDRX_Cycle__F1 MAC_ParametersXDD_Diff__shortDRX_Cycle__F2 MAC_ParametersXDD_Diff__shortDRX_Cycle__F1F2 MAC_ParametersXDD_Diff__shortDRX_Cycle__F2F1.

Opaque MAC_ParametersXDD_Diff__shortDRX_Cycle__cond MAC_ParametersXDD_Diff__shortDRX_Cycle__Format.

Definition MAC_ParametersXDD_Diff__multipleSR_Configurations__Format : T_Format MAC_ParametersXDD_Diff__multipleSR_Configurations__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__multipleSR_Configurations__nat__Format MAC_ParametersXDD_Diff__multipleSR_Configurations__F1 MAC_ParametersXDD_Diff__multipleSR_Configurations__F2 MAC_ParametersXDD_Diff__multipleSR_Configurations__F1F2 MAC_ParametersXDD_Diff__multipleSR_Configurations__F2F1.

Opaque MAC_ParametersXDD_Diff__multipleSR_Configurations__cond MAC_ParametersXDD_Diff__multipleSR_Configurations__Format.

Definition MAC_ParametersXDD_Diff__multipleConfiguredGrants__Format : T_Format MAC_ParametersXDD_Diff__multipleConfiguredGrants__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__multipleConfiguredGrants__nat__Format MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1 MAC_ParametersXDD_Diff__multipleConfiguredGrants__F2 MAC_ParametersXDD_Diff__multipleConfiguredGrants__F1F2 MAC_ParametersXDD_Diff__multipleConfiguredGrants__F2F1.

Opaque MAC_ParametersXDD_Diff__multipleConfiguredGrants__cond MAC_ParametersXDD_Diff__multipleConfiguredGrants__Format.

Definition MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Format : T_Format MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__nat__Format MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1 MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F2 MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F1F2 MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__F2F1.

Opaque MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__cond MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Format.


Definition MAC_ParametersXDD_Diff__ext0O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersXDD_Diff__ext0O__list.
Definition MAC_ParametersXDD_Diff__ext0O__Format_list : MAC_ParametersXDD_Diff__ext0O__Format_Type :=
  (MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16__Format, unit_format).
Definition MAC_ParametersXDD_Diff__ext0O__list__Format := (*Eval compute in *) seq_format MAC_ParametersXDD_Diff__ext0O__list MAC_ParametersXDD_Diff__ext0O__Format_list.
Definition MAC_ParametersXDD_Diff__ext0O__F1 z :=
  (MAC_ParametersXDD_Diff__ext0O__secondaryDRX_Group_r16 z, tt).
Definition MAC_ParametersXDD_Diff__ext0O__F2 (y : seq_type MAC_ParametersXDD_Diff__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MAC_ParametersXDD_Diff__ext0O__Type i0
  end.
Lemma MAC_ParametersXDD_Diff__ext0O__F1F2_cond (z : MAC_ParametersXDD_Diff__ext0O__Type)
  : MAC_ParametersXDD_Diff__ext0O__cond z ->
  (seq_cond MAC_ParametersXDD_Diff__ext0O__list (MAC_ParametersXDD_Diff__ext0O__F1 z)).
intro H. unfold MAC_ParametersXDD_Diff__ext0O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersXDD_Diff__ext0O__F1F2_cond2 (z : MAC_ParametersXDD_Diff__ext0O__Type)
 : MAC_ParametersXDD_Diff__ext0O__F2 (MAC_ParametersXDD_Diff__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersXDD_Diff__ext0O__F2F1_cond (y : seq_type MAC_ParametersXDD_Diff__ext0O__list)
  : seq_cond MAC_ParametersXDD_Diff__ext0O__list y ->
 (MAC_ParametersXDD_Diff__ext0O__cond (MAC_ParametersXDD_Diff__ext0O__F2 y)) /\  MAC_ParametersXDD_Diff__ext0O__F1 (MAC_ParametersXDD_Diff__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersXDD_Diff__ext0O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersXDD_Diff__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersXDD_Diff__ext0O__Format : T_Format MAC_ParametersXDD_Diff__ext0O__Type MAC_ParametersXDD_Diff__ext0O__cond :=
        proj2_format  MAC_ParametersXDD_Diff__ext0O__cond MAC_ParametersXDD_Diff__ext0O__list__Format
    MAC_ParametersXDD_Diff__ext0O__F1 MAC_ParametersXDD_Diff__ext0O__F2 MAC_ParametersXDD_Diff__ext0O__F1F2_cond  MAC_ParametersXDD_Diff__ext0O__F1F2_cond2 MAC_ParametersXDD_Diff__ext0O__F2F1_cond.
Opaque MAC_ParametersXDD_Diff__ext0O__cond MAC_ParametersXDD_Diff__ext0O__Format.

Definition MAC_ParametersXDD_Diff__ext0__check_all_none (b : MAC_ParametersXDD_Diff__ext0O__Type) : bool :=
match b with 
  | make__MAC_ParametersXDD_Diff__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MAC_ParametersXDD_Diff__ext0__Format : T_Format MAC_ParametersXDD_Diff__ext0__Type MAC_ParametersXDD_Diff__ext0__cond :=
  restrict_add_format MAC_ParametersXDD_Diff__ext0__check_all_none MAC_ParametersXDD_Diff__ext0O__Format.

Opaque MAC_ParametersXDD_Diff__ext0__cond MAC_ParametersXDD_Diff__ext0__Format.

Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Format : T_Format MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__nat__Format MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F2 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F1F2 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__F2F1.

Opaque MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__cond MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Format.

Definition MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Format : T_Format MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__nat__Format MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F2 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F1F2 MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__F2F1.

Opaque MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__cond MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Format.


Definition MAC_ParametersXDD_Diff__ext1O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersXDD_Diff__ext1O__list.
Definition MAC_ParametersXDD_Diff__ext1O__Format_list : MAC_ParametersXDD_Diff__ext1O__Format_Type :=
  (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16__Format, (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16__Format, unit_format)).
Definition MAC_ParametersXDD_Diff__ext1O__list__Format := (*Eval compute in *) seq_format MAC_ParametersXDD_Diff__ext1O__list MAC_ParametersXDD_Diff__ext1O__Format_list.
Definition MAC_ParametersXDD_Diff__ext1O__F1 z :=
  (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxDynamic_r16 z, (MAC_ParametersXDD_Diff__ext1O__enhancedSkipUplinkTxConfigured_r16 z, tt)).
Definition MAC_ParametersXDD_Diff__ext1O__F2 (y : seq_type MAC_ParametersXDD_Diff__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MAC_ParametersXDD_Diff__ext1O__Type i0 i1
  end.
Lemma MAC_ParametersXDD_Diff__ext1O__F1F2_cond (z : MAC_ParametersXDD_Diff__ext1O__Type)
  : MAC_ParametersXDD_Diff__ext1O__cond z ->
  (seq_cond MAC_ParametersXDD_Diff__ext1O__list (MAC_ParametersXDD_Diff__ext1O__F1 z)).
intro H. unfold MAC_ParametersXDD_Diff__ext1O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersXDD_Diff__ext1O__F1F2_cond2 (z : MAC_ParametersXDD_Diff__ext1O__Type)
 : MAC_ParametersXDD_Diff__ext1O__F2 (MAC_ParametersXDD_Diff__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersXDD_Diff__ext1O__F2F1_cond (y : seq_type MAC_ParametersXDD_Diff__ext1O__list)
  : seq_cond MAC_ParametersXDD_Diff__ext1O__list y ->
 (MAC_ParametersXDD_Diff__ext1O__cond (MAC_ParametersXDD_Diff__ext1O__F2 y)) /\  MAC_ParametersXDD_Diff__ext1O__F1 (MAC_ParametersXDD_Diff__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersXDD_Diff__ext1O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersXDD_Diff__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersXDD_Diff__ext1O__Format : T_Format MAC_ParametersXDD_Diff__ext1O__Type MAC_ParametersXDD_Diff__ext1O__cond :=
        proj2_format  MAC_ParametersXDD_Diff__ext1O__cond MAC_ParametersXDD_Diff__ext1O__list__Format
    MAC_ParametersXDD_Diff__ext1O__F1 MAC_ParametersXDD_Diff__ext1O__F2 MAC_ParametersXDD_Diff__ext1O__F1F2_cond  MAC_ParametersXDD_Diff__ext1O__F1F2_cond2 MAC_ParametersXDD_Diff__ext1O__F2F1_cond.
Opaque MAC_ParametersXDD_Diff__ext1O__cond MAC_ParametersXDD_Diff__ext1O__Format.

Definition MAC_ParametersXDD_Diff__ext1__check_all_none (b : MAC_ParametersXDD_Diff__ext1O__Type) : bool :=
match b with 
  | make__MAC_ParametersXDD_Diff__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition MAC_ParametersXDD_Diff__ext1__Format : T_Format MAC_ParametersXDD_Diff__ext1__Type MAC_ParametersXDD_Diff__ext1__cond :=
  restrict_add_format MAC_ParametersXDD_Diff__ext1__check_all_none MAC_ParametersXDD_Diff__ext1O__Format.

Opaque MAC_ParametersXDD_Diff__ext1__cond MAC_ParametersXDD_Diff__ext1__Format.


Definition MAC_ParametersXDD_Diff__root_Format_Type := Eval cbn in seq_format_prod MAC_ParametersXDD_Diff__root_list.
Definition MAC_ParametersXDD_Diff__root_Format_list : MAC_ParametersXDD_Diff__root_Format_Type :=
  (MAC_ParametersXDD_Diff__skipUplinkTxDynamic__Format, (MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer__Format, (MAC_ParametersXDD_Diff__longDRX_Cycle__Format, (MAC_ParametersXDD_Diff__shortDRX_Cycle__Format, (MAC_ParametersXDD_Diff__multipleSR_Configurations__Format, (MAC_ParametersXDD_Diff__multipleConfiguredGrants__Format, unit_format)))))).

Definition MAC_ParametersXDD_Diff__ext_Format_Type := Eval cbn in get_formats MAC_ParametersXDD_Diff__ext_list.
Definition MAC_ParametersXDD_Diff__ext_Format_list : MAC_ParametersXDD_Diff__ext_Format_Type :=
  (MAC_ParametersXDD_Diff__ext0__Format, (MAC_ParametersXDD_Diff__ext1__Format, unit__Format)).

Definition MAC_ParametersXDD_Diff__list_type : Set := (seq_type MAC_ParametersXDD_Diff__root_list) * (seq_ext_type MAC_ParametersXDD_Diff__ext_list).
Definition MAC_ParametersXDD_Diff__list_cond (z : MAC_ParametersXDD_Diff__list_type) : Prop :=
        (seq_cond MAC_ParametersXDD_Diff__root_list (fst z)) /\ (seq_ext_cond MAC_ParametersXDD_Diff__ext_list (snd z)).
Definition MAC_ParametersXDD_Diff__list_format : T_Format MAC_ParametersXDD_Diff__list_type MAC_ParametersXDD_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format MAC_ParametersXDD_Diff__root_list MAC_ParametersXDD_Diff__root_Format_list MAC_ParametersXDD_Diff__ext_list MAC_ParametersXDD_Diff__ext_Format_list.

Opaque MAC_ParametersXDD_Diff__list_format.
Definition MAC_ParametersXDD_Diff__F1 (z : MAC_ParametersXDD_Diff__Type) : MAC_ParametersXDD_Diff__list_type :=
  (((MAC_ParametersXDD_Diff__skipUplinkTxDynamic z, (MAC_ParametersXDD_Diff__logicalChannelSR_DelayTimer z, (MAC_ParametersXDD_Diff__longDRX_Cycle z, (MAC_ParametersXDD_Diff__shortDRX_Cycle z, (MAC_ParametersXDD_Diff__multipleSR_Configurations z, (MAC_ParametersXDD_Diff__multipleConfiguredGrants z, tt))))))), (
(MAC_ParametersXDD_Diff__ext0 z, (MAC_ParametersXDD_Diff__ext1 z, tt)))).
Definition MAC_ParametersXDD_Diff__F2 (y : MAC_ParametersXDD_Diff__list_type) : MAC_ParametersXDD_Diff__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, (i1, _)))=>
    make__MAC_ParametersXDD_Diff__Type j0 j1 j2 j3 j4 j5 i0 i1
  end.
Definition MAC_ParametersXDD_Diff__helper1 : (forall a : MAC_ParametersXDD_Diff__Type, MAC_ParametersXDD_Diff__cond a -> MAC_ParametersXDD_Diff__list_cond (MAC_ParametersXDD_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersXDD_Diff__helper2 : (forall a : MAC_ParametersXDD_Diff__Type, MAC_ParametersXDD_Diff__F2 (MAC_ParametersXDD_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersXDD_Diff__helper3 : (forall b : MAC_ParametersXDD_Diff__list_type, MAC_ParametersXDD_Diff__list_cond b -> MAC_ParametersXDD_Diff__cond (MAC_ParametersXDD_Diff__F2 b) /\ MAC_ParametersXDD_Diff__F1 (MAC_ParametersXDD_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MAC_ParametersXDD_Diff__cond, MAC_ParametersXDD_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MAC_ParametersXDD_Diff__Format : T_Format MAC_ParametersXDD_Diff__Type MAC_ParametersXDD_Diff__cond :=
 proj2_format MAC_ParametersXDD_Diff__cond MAC_ParametersXDD_Diff__list_format  MAC_ParametersXDD_Diff__F1 MAC_ParametersXDD_Diff__F2 MAC_ParametersXDD_Diff__helper1 MAC_ParametersXDD_Diff__helper2 MAC_ParametersXDD_Diff__helper3.

Opaque MAC_ParametersXDD_Diff__cond MAC_ParametersXDD_Diff__Format.

