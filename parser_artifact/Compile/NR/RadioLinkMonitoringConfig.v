Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RadioLinkMonitoringRS.

Opaque RadioLinkMonitoringRS__cond RadioLinkMonitoringRS__Format.

Definition RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Type := list RadioLinkMonitoringRS__Type.

Lemma RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__helper1 : (0 <= 1 <= maxNrofFailureDetectionResources)%Z. unfold maxNrofFailureDetectionResources.
 lia. Qed.
Lemma RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofFailureDetectionResources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFailureDetectionResources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__cond (z : RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFailureDetectionResources)%Z /\ (list_and RadioLinkMonitoringRS__cond z) .

Require Import NR.RadioLinkMonitoringRS_Id.

Opaque RadioLinkMonitoringRS_Id__cond RadioLinkMonitoringRS_Id__Format.

Definition RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Type := list RadioLinkMonitoringRS_Id__Type.

Lemma RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__helper1 : (0 <= 1 <= maxNrofFailureDetectionResources)%Z. unfold maxNrofFailureDetectionResources.
 lia. Qed.
Lemma RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofFailureDetectionResources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFailureDetectionResources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__cond (z : RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFailureDetectionResources)%Z /\ (list_and RadioLinkMonitoringRS_Id__cond z) .

Inductive RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Type : Set :=
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n1
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n2
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n3
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n4
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n5
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n6
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n8
 | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n10
.
Definition RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__cond := (fun (_ : RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Type) => True).
Lemma RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__nat__helper.

Definition RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1 t :=
  match t with
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n1 => 0
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n2 => 1
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n3 => 2
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n4 => 3
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n5 => 4
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n6 => 5
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n8 => 6
  | RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n10 => 7
  end.
Definition RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F2 n :=
  match n with
  | 0 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n1
  | 1 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n2
  | 2 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n3
  | 3 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n4
  | 4 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n5
  | 5 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n6
  | 6 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n8
  | 7 => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n10
  | _ => RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__n1
  end.
Lemma RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1F2 : forall x : RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Type, (RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1 x <= 7) /\ RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F2 (RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1 x) = x. imp_solve. Qed.
Lemma RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F2F1 : forall (y : nat) (H : y <= 7), RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1 (RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F2 y) = y. enum_solve H y. Qed.

Inductive RadioLinkMonitoringConfig__beamFailureDetectionTimer__Type : Set :=
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd1
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd2
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd3
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd4
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd5
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd6
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd8
 | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd10
.
Definition RadioLinkMonitoringConfig__beamFailureDetectionTimer__cond := (fun (_ : RadioLinkMonitoringConfig__beamFailureDetectionTimer__Type) => True).
Lemma RadioLinkMonitoringConfig__beamFailureDetectionTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RadioLinkMonitoringConfig__beamFailureDetectionTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RadioLinkMonitoringConfig__beamFailureDetectionTimer__nat__helper.

Definition RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1 t :=
  match t with
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd1 => 0
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd2 => 1
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd3 => 2
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd4 => 3
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd5 => 4
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd6 => 5
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd8 => 6
  | RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd10 => 7
  end.
Definition RadioLinkMonitoringConfig__beamFailureDetectionTimer__F2 n :=
  match n with
  | 0 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd1
  | 1 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd2
  | 2 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd3
  | 3 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd4
  | 4 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd5
  | 5 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd6
  | 6 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd8
  | 7 => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd10
  | _ => RadioLinkMonitoringConfig__beamFailureDetectionTimer__pbfd1
  end.
Lemma RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1F2 : forall x : RadioLinkMonitoringConfig__beamFailureDetectionTimer__Type, (RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1 x <= 7) /\ RadioLinkMonitoringConfig__beamFailureDetectionTimer__F2 (RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1 x) = x. imp_solve. Qed.
Lemma RadioLinkMonitoringConfig__beamFailureDetectionTimer__F2F1 : forall (y : nat) (H : y <= 7), RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1 (RadioLinkMonitoringConfig__beamFailureDetectionTimer__F2 y) = y. enum_solve H y. Qed.

Require Import NR.BeamFailureDetection_r17.

Opaque BeamFailureDetection_r17__cond BeamFailureDetection_r17__Format.

Record RadioLinkMonitoringConfig__ext0O__Type : Set :=
  make__RadioLinkMonitoringConfig__ext0O__Type {
    RadioLinkMonitoringConfig__ext0O__beamfailure_r17 : option BeamFailureDetection_r17__Type ;
}.
Definition RadioLinkMonitoringConfig__ext0O__list := (
 Opt BeamFailureDetection_r17__Type BeamFailureDetection_r17__cond ::
 nil).
Definition RadioLinkMonitoringConfig__ext0O__cond z := 
  opt_cond BeamFailureDetection_r17__cond (RadioLinkMonitoringConfig__ext0O__beamfailure_r17 z) /\
  True.

Definition RadioLinkMonitoringConfig__ext0__Type := RadioLinkMonitoringConfig__ext0O__Type.
Definition RadioLinkMonitoringConfig__ext0__cond := RadioLinkMonitoringConfig__ext0O__cond.

Record RadioLinkMonitoringConfig__Type : Set :=
  make__RadioLinkMonitoringConfig__Type {
    RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList : option RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Type ;
    RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList : option RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Type ;
    RadioLinkMonitoringConfig__beamFailureInstanceMaxCount : option RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Type ;
    RadioLinkMonitoringConfig__beamFailureDetectionTimer : option RadioLinkMonitoringConfig__beamFailureDetectionTimer__Type ;
    RadioLinkMonitoringConfig__ext0 : option RadioLinkMonitoringConfig__ext0__Type ;
}.
Definition RadioLinkMonitoringConfig__root_list : list seq_elem := (
 Opt RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Type RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__cond ::
 Opt RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Type RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__cond ::
 Opt RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Type RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__cond ::
 Opt RadioLinkMonitoringConfig__beamFailureDetectionTimer__Type RadioLinkMonitoringConfig__beamFailureDetectionTimer__cond ::
 nil).
Definition RadioLinkMonitoringConfig__ext_list : list typ := (
  typ_cons RadioLinkMonitoringConfig__ext0__Type RadioLinkMonitoringConfig__ext0__cond ::
  nil).
Definition RadioLinkMonitoringConfig__cond (z : RadioLinkMonitoringConfig__Type) := 
(  opt_cond RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__cond (RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList z) /\
  opt_cond RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__cond (RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList z) /\
  opt_cond RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__cond (RadioLinkMonitoringConfig__beamFailureInstanceMaxCount z) /\
  opt_cond RadioLinkMonitoringConfig__beamFailureDetectionTimer__cond (RadioLinkMonitoringConfig__beamFailureDetectionTimer z) /\
  True) /\ 
(  opt_cond RadioLinkMonitoringConfig__ext0__cond (RadioLinkMonitoringConfig__ext0 z) /\
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
Definition RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Format : T_Format RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Type RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__cond := seq_of_format RadioLinkMonitoringRS__Format 1 maxNrofFailureDetectionResources RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__helper1 RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__helper2.

Opaque RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__cond RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Format.

Definition RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Format : T_Format RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Type RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__cond := seq_of_format RadioLinkMonitoringRS_Id__Format 1 maxNrofFailureDetectionResources RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__helper1 RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__helper2.

Opaque RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__cond RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Format.

Definition RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Format : T_Format RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__nat__Format RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1 RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F2 RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F1F2 RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__F2F1.

Opaque RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__cond RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Format.

Definition RadioLinkMonitoringConfig__beamFailureDetectionTimer__Format : T_Format RadioLinkMonitoringConfig__beamFailureDetectionTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RadioLinkMonitoringConfig__beamFailureDetectionTimer__nat__Format RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1 RadioLinkMonitoringConfig__beamFailureDetectionTimer__F2 RadioLinkMonitoringConfig__beamFailureDetectionTimer__F1F2 RadioLinkMonitoringConfig__beamFailureDetectionTimer__F2F1.

Opaque RadioLinkMonitoringConfig__beamFailureDetectionTimer__cond RadioLinkMonitoringConfig__beamFailureDetectionTimer__Format.


Definition RadioLinkMonitoringConfig__ext0O__Format_Type := Eval cbn in seq_format_prod RadioLinkMonitoringConfig__ext0O__list.
Definition RadioLinkMonitoringConfig__ext0O__Format_list : RadioLinkMonitoringConfig__ext0O__Format_Type :=
  (BeamFailureDetection_r17__Format, unit_format).
Definition RadioLinkMonitoringConfig__ext0O__list__Format := (*Eval compute in *) seq_format RadioLinkMonitoringConfig__ext0O__list RadioLinkMonitoringConfig__ext0O__Format_list.
Definition RadioLinkMonitoringConfig__ext0O__F1 z :=
  (RadioLinkMonitoringConfig__ext0O__beamfailure_r17 z, tt).
Definition RadioLinkMonitoringConfig__ext0O__F2 (y : seq_type RadioLinkMonitoringConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RadioLinkMonitoringConfig__ext0O__Type i0
  end.
Lemma RadioLinkMonitoringConfig__ext0O__F1F2_cond (z : RadioLinkMonitoringConfig__ext0O__Type)
  : RadioLinkMonitoringConfig__ext0O__cond z ->
  (seq_cond RadioLinkMonitoringConfig__ext0O__list (RadioLinkMonitoringConfig__ext0O__F1 z)).
intro H. unfold RadioLinkMonitoringConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma RadioLinkMonitoringConfig__ext0O__F1F2_cond2 (z : RadioLinkMonitoringConfig__ext0O__Type)
 : RadioLinkMonitoringConfig__ext0O__F2 (RadioLinkMonitoringConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RadioLinkMonitoringConfig__ext0O__F2F1_cond (y : seq_type RadioLinkMonitoringConfig__ext0O__list)
  : seq_cond RadioLinkMonitoringConfig__ext0O__list y ->
 (RadioLinkMonitoringConfig__ext0O__cond (RadioLinkMonitoringConfig__ext0O__F2 y)) /\  RadioLinkMonitoringConfig__ext0O__F1 (RadioLinkMonitoringConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RadioLinkMonitoringConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold RadioLinkMonitoringConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RadioLinkMonitoringConfig__ext0O__Format : T_Format RadioLinkMonitoringConfig__ext0O__Type RadioLinkMonitoringConfig__ext0O__cond :=
        proj2_format  RadioLinkMonitoringConfig__ext0O__cond RadioLinkMonitoringConfig__ext0O__list__Format
    RadioLinkMonitoringConfig__ext0O__F1 RadioLinkMonitoringConfig__ext0O__F2 RadioLinkMonitoringConfig__ext0O__F1F2_cond  RadioLinkMonitoringConfig__ext0O__F1F2_cond2 RadioLinkMonitoringConfig__ext0O__F2F1_cond.
Opaque RadioLinkMonitoringConfig__ext0O__cond RadioLinkMonitoringConfig__ext0O__Format.

Definition RadioLinkMonitoringConfig__ext0__check_all_none (b : RadioLinkMonitoringConfig__ext0O__Type) : bool :=
match b with 
  | make__RadioLinkMonitoringConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RadioLinkMonitoringConfig__ext0__Format : T_Format RadioLinkMonitoringConfig__ext0__Type RadioLinkMonitoringConfig__ext0__cond :=
  restrict_add_format RadioLinkMonitoringConfig__ext0__check_all_none RadioLinkMonitoringConfig__ext0O__Format.

Opaque RadioLinkMonitoringConfig__ext0__cond RadioLinkMonitoringConfig__ext0__Format.


Definition RadioLinkMonitoringConfig__root_Format_Type := Eval cbn in seq_format_prod RadioLinkMonitoringConfig__root_list.
Definition RadioLinkMonitoringConfig__root_Format_list : RadioLinkMonitoringConfig__root_Format_Type :=
  (RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList__Format, (RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList__Format, (RadioLinkMonitoringConfig__beamFailureInstanceMaxCount__Format, (RadioLinkMonitoringConfig__beamFailureDetectionTimer__Format, unit_format)))).

Definition RadioLinkMonitoringConfig__ext_Format_Type := Eval cbn in get_formats RadioLinkMonitoringConfig__ext_list.
Definition RadioLinkMonitoringConfig__ext_Format_list : RadioLinkMonitoringConfig__ext_Format_Type :=
  (RadioLinkMonitoringConfig__ext0__Format, unit__Format).

Definition RadioLinkMonitoringConfig__list_type : Set := (seq_type RadioLinkMonitoringConfig__root_list) * (seq_ext_type RadioLinkMonitoringConfig__ext_list).
Definition RadioLinkMonitoringConfig__list_cond (z : RadioLinkMonitoringConfig__list_type) : Prop :=
        (seq_cond RadioLinkMonitoringConfig__root_list (fst z)) /\ (seq_ext_cond RadioLinkMonitoringConfig__ext_list (snd z)).
Definition RadioLinkMonitoringConfig__list_format : T_Format RadioLinkMonitoringConfig__list_type RadioLinkMonitoringConfig__list_cond :=
 (* Eval compute in *) seq_ext_format RadioLinkMonitoringConfig__root_list RadioLinkMonitoringConfig__root_Format_list RadioLinkMonitoringConfig__ext_list RadioLinkMonitoringConfig__ext_Format_list.

Opaque RadioLinkMonitoringConfig__list_format.
Definition RadioLinkMonitoringConfig__F1 (z : RadioLinkMonitoringConfig__Type) : RadioLinkMonitoringConfig__list_type :=
  (((RadioLinkMonitoringConfig__failureDetectionResourcesToAddModList z, (RadioLinkMonitoringConfig__failureDetectionResourcesToReleaseList z, (RadioLinkMonitoringConfig__beamFailureInstanceMaxCount z, (RadioLinkMonitoringConfig__beamFailureDetectionTimer z, tt))))), (
(RadioLinkMonitoringConfig__ext0 z, tt))).
Definition RadioLinkMonitoringConfig__F2 (y : RadioLinkMonitoringConfig__list_type) : RadioLinkMonitoringConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__RadioLinkMonitoringConfig__Type j0 j1 j2 j3 i0
  end.
Definition RadioLinkMonitoringConfig__helper1 : (forall a : RadioLinkMonitoringConfig__Type, RadioLinkMonitoringConfig__cond a -> RadioLinkMonitoringConfig__list_cond (RadioLinkMonitoringConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RadioLinkMonitoringConfig__helper2 : (forall a : RadioLinkMonitoringConfig__Type, RadioLinkMonitoringConfig__F2 (RadioLinkMonitoringConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RadioLinkMonitoringConfig__helper3 : (forall b : RadioLinkMonitoringConfig__list_type, RadioLinkMonitoringConfig__list_cond b -> RadioLinkMonitoringConfig__cond (RadioLinkMonitoringConfig__F2 b) /\ RadioLinkMonitoringConfig__F1 (RadioLinkMonitoringConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RadioLinkMonitoringConfig__cond, RadioLinkMonitoringConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RadioLinkMonitoringConfig__Format : T_Format RadioLinkMonitoringConfig__Type RadioLinkMonitoringConfig__cond :=
 proj2_format RadioLinkMonitoringConfig__cond RadioLinkMonitoringConfig__list_format  RadioLinkMonitoringConfig__F1 RadioLinkMonitoringConfig__F2 RadioLinkMonitoringConfig__helper1 RadioLinkMonitoringConfig__helper2 RadioLinkMonitoringConfig__helper3.

Opaque RadioLinkMonitoringConfig__cond RadioLinkMonitoringConfig__Format.

