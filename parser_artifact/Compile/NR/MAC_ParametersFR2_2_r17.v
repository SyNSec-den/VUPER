Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Type : Set :=
 | MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__supported
.
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__cond := (fun (_ : MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Type) => True).
Lemma MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__nat__helper.

Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1 t :=
  match t with
  | MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__supported => 0
  end.
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__supported
  | _ => MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__supported
  end.
Lemma MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1F2 : forall x : MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Type, (MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1 x <= 0) /\ MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F2 (MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1 (MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Type : Set :=
 | MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__supported
.
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__cond := (fun (_ : MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Type) => True).
Lemma MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__nat__helper.

Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1 t :=
  match t with
  | MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__supported => 0
  end.
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__supported
  | _ => MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__supported
  end.
Lemma MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1F2 : forall x : MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Type, (MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1 x <= 0) /\ MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F2 (MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1 (MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Type : Set :=
 | MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__supported
.
Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__cond := (fun (_ : MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Type) => True).
Lemma MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__nat__helper.

Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1 t :=
  match t with
  | MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__supported => 0
  end.
Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__supported
  | _ => MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__supported
  end.
Lemma MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1F2 : forall x : MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Type, (MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1 x <= 0) /\ MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F2 (MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1 (MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Type : Set :=
 | MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__supported
.
Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__cond := (fun (_ : MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Type) => True).
Lemma MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__nat__helper.

Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1 t :=
  match t with
  | MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__supported => 0
  end.
Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__supported
  | _ => MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__supported
  end.
Lemma MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1F2 : forall x : MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Type, (MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1 x <= 0) /\ MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F2 (MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1 (MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MinTimeGapFR2_2_r17.

Opaque MinTimeGapFR2_2_r17__cond MinTimeGapFR2_2_r17__Format.

Require Import NR.MinTimeGapFR2_2_r17.

Opaque MinTimeGapFR2_2_r17__cond MinTimeGapFR2_2_r17__Format.

Record MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type : Set :=
  make__MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type {
    MAC_ParametersFR2_2_r17__drx_Adaptation_r17__non_SharedSpectrumChAccess_r17 : option MinTimeGapFR2_2_r17__Type ;
    MAC_ParametersFR2_2_r17__drx_Adaptation_r17__sharedSpectrumChAccess_r17 : option MinTimeGapFR2_2_r17__Type ;
}.
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list := (
 Opt MinTimeGapFR2_2_r17__Type MinTimeGapFR2_2_r17__cond ::
 Opt MinTimeGapFR2_2_r17__Type MinTimeGapFR2_2_r17__cond ::
 nil).
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond z := 
  opt_cond MinTimeGapFR2_2_r17__cond (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__non_SharedSpectrumChAccess_r17 z) /\
  opt_cond MinTimeGapFR2_2_r17__cond (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__sharedSpectrumChAccess_r17 z) /\
  True.

Record MAC_ParametersFR2_2_r17__Type : Set :=
  make__MAC_ParametersFR2_2_r17__Type {
    MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17 : option MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Type ;
    MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17 : option MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Type ;
    MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17 : option MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Type ;
    MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17 : option MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Type ;
    MAC_ParametersFR2_2_r17__drx_Adaptation_r17 : option MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type ;
}.
Definition MAC_ParametersFR2_2_r17__root_list : list seq_elem := (
 Opt MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Type MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__cond ::
 Opt MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Type MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__cond ::
 Opt MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Type MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__cond ::
 Opt MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Type MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__cond ::
 Opt MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond ::
 nil).
Definition MAC_ParametersFR2_2_r17__ext_list : list typ := (
  nil).
Definition MAC_ParametersFR2_2_r17__cond (z : MAC_ParametersFR2_2_r17__Type) := 
(  opt_cond MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__cond (MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17 z) /\
  opt_cond MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__cond (MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17 z) /\
  opt_cond MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__cond (MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17 z) /\
  opt_cond MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__cond (MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17 z) /\
  opt_cond MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond (MAC_ParametersFR2_2_r17__drx_Adaptation_r17 z) /\
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
Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Format : T_Format MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__nat__Format MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1 MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F2 MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F1F2 MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__F2F1.

Opaque MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__cond MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Format.

Definition MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Format : T_Format MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__nat__Format MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1 MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F2 MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F1F2 MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__F2F1.

Opaque MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__cond MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Format.

Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Format : T_Format MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__nat__Format MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1 MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F2 MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F1F2 MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__F2F1.

Opaque MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__cond MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Format.

Definition MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Format : T_Format MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__nat__Format MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1 MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F2 MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F1F2 MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__F2F1.

Opaque MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__cond MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Format.


Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format_Type := Eval cbn in seq_format_prod MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list.
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format_list : MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format_Type :=
  (MinTimeGapFR2_2_r17__Format, (MinTimeGapFR2_2_r17__Format, unit_format)).
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list__Format := (*Eval compute in *) seq_format MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format_list.
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1 z :=
  (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__non_SharedSpectrumChAccess_r17 z, (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__sharedSpectrumChAccess_r17 z, tt)).
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2 (y : seq_type MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type i0 i1
  end.
Lemma MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1F2_cond (z : MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type)
  : MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond z ->
  (seq_cond MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1 z)).
intro H. unfold MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1F2_cond2 (z : MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type)
 : MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2 (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2F1_cond (y : seq_type MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list)
  : seq_cond MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list y ->
 (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2 y)) /\  MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1 (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format : T_Format MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Type MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond :=
        proj2_format  MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond MAC_ParametersFR2_2_r17__drx_Adaptation_r17__list__Format
    MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1 MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2 MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1F2_cond  MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F1F2_cond2 MAC_ParametersFR2_2_r17__drx_Adaptation_r17__F2F1_cond.
Opaque MAC_ParametersFR2_2_r17__drx_Adaptation_r17__cond MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format.


Definition MAC_ParametersFR2_2_r17__root_Format_Type := Eval cbn in seq_format_prod MAC_ParametersFR2_2_r17__root_list.
Definition MAC_ParametersFR2_2_r17__root_Format_list : MAC_ParametersFR2_2_r17__root_Format_Type :=
  (MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17__Format, (MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17__Format, (MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17__Format, (MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17__Format, (MAC_ParametersFR2_2_r17__drx_Adaptation_r17__Format, unit_format))))).

Definition MAC_ParametersFR2_2_r17__ext_Format_Type := Eval cbn in get_formats MAC_ParametersFR2_2_r17__ext_list.
Definition MAC_ParametersFR2_2_r17__ext_Format_list : MAC_ParametersFR2_2_r17__ext_Format_Type :=
  unit__Format.

Definition MAC_ParametersFR2_2_r17__list_type : Set := (seq_type MAC_ParametersFR2_2_r17__root_list) * (seq_ext_type MAC_ParametersFR2_2_r17__ext_list).
Definition MAC_ParametersFR2_2_r17__list_cond (z : MAC_ParametersFR2_2_r17__list_type) : Prop :=
        (seq_cond MAC_ParametersFR2_2_r17__root_list (fst z)) /\ (seq_ext_cond MAC_ParametersFR2_2_r17__ext_list (snd z)).
Definition MAC_ParametersFR2_2_r17__list_format : T_Format MAC_ParametersFR2_2_r17__list_type MAC_ParametersFR2_2_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MAC_ParametersFR2_2_r17__root_list MAC_ParametersFR2_2_r17__root_Format_list MAC_ParametersFR2_2_r17__ext_list MAC_ParametersFR2_2_r17__ext_Format_list.

Opaque MAC_ParametersFR2_2_r17__list_format.
Definition MAC_ParametersFR2_2_r17__F1 (z : MAC_ParametersFR2_2_r17__Type) : MAC_ParametersFR2_2_r17__list_type :=
  (((MAC_ParametersFR2_2_r17__directMCG_SCellActivation_r17 z, (MAC_ParametersFR2_2_r17__directMCG_SCellActivationResume_r17 z, (MAC_ParametersFR2_2_r17__directSCG_SCellActivation_r17 z, (MAC_ParametersFR2_2_r17__directSCG_SCellActivationResume_r17 z, (MAC_ParametersFR2_2_r17__drx_Adaptation_r17 z, tt)))))), (
tt)).
Definition MAC_ParametersFR2_2_r17__F2 (y : MAC_ParametersFR2_2_r17__list_type) : MAC_ParametersFR2_2_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__MAC_ParametersFR2_2_r17__Type j0 j1 j2 j3 j4
  end.
Definition MAC_ParametersFR2_2_r17__helper1 : (forall a : MAC_ParametersFR2_2_r17__Type, MAC_ParametersFR2_2_r17__cond a -> MAC_ParametersFR2_2_r17__list_cond (MAC_ParametersFR2_2_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersFR2_2_r17__helper2 : (forall a : MAC_ParametersFR2_2_r17__Type, MAC_ParametersFR2_2_r17__F2 (MAC_ParametersFR2_2_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersFR2_2_r17__helper3 : (forall b : MAC_ParametersFR2_2_r17__list_type, MAC_ParametersFR2_2_r17__list_cond b -> MAC_ParametersFR2_2_r17__cond (MAC_ParametersFR2_2_r17__F2 b) /\ MAC_ParametersFR2_2_r17__F1 (MAC_ParametersFR2_2_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MAC_ParametersFR2_2_r17__cond, MAC_ParametersFR2_2_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MAC_ParametersFR2_2_r17__Format : T_Format MAC_ParametersFR2_2_r17__Type MAC_ParametersFR2_2_r17__cond :=
 proj2_format MAC_ParametersFR2_2_r17__cond MAC_ParametersFR2_2_r17__list_format  MAC_ParametersFR2_2_r17__F1 MAC_ParametersFR2_2_r17__F2 MAC_ParametersFR2_2_r17__helper1 MAC_ParametersFR2_2_r17__helper2 MAC_ParametersFR2_2_r17__helper3.

Opaque MAC_ParametersFR2_2_r17__cond MAC_ParametersFR2_2_r17__Format.

