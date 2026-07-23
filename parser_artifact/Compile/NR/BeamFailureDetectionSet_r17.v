Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BeamLinkMonitoringRS_r17.

Opaque BeamLinkMonitoringRS_r17__cond BeamLinkMonitoringRS_r17__Format.

Definition BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Type := list BeamLinkMonitoringRS_r17__Type.

Lemma BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__helper1 : (0 <= 1 <= maxNrofBFDResourcePerSet_r17)%Z. unfold maxNrofBFDResourcePerSet_r17.
 lia. Qed.
Lemma BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofBFDResourcePerSet_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBFDResourcePerSet_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__cond (z : BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBFDResourcePerSet_r17)%Z /\ (list_and BeamLinkMonitoringRS_r17__cond z) .

Require Import NR.BeamLinkMonitoringRS_Id_r17.

Opaque BeamLinkMonitoringRS_Id_r17__cond BeamLinkMonitoringRS_Id_r17__Format.

Definition BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Type := list BeamLinkMonitoringRS_Id_r17__Type.

Lemma BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofBFDResourcePerSet_r17)%Z. unfold maxNrofBFDResourcePerSet_r17.
 lia. Qed.
Lemma BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofBFDResourcePerSet_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBFDResourcePerSet_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__cond (z : BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBFDResourcePerSet_r17)%Z /\ (list_and BeamLinkMonitoringRS_Id_r17__cond z) .

Inductive BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Type : Set :=
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n1
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n2
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n3
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n4
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n5
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n6
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n8
 | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n10
.
Definition BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__cond := (fun (_ : BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Type) => True).
Lemma BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__nat__helper.

Definition BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1 t :=
  match t with
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n1 => 0
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n2 => 1
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n3 => 2
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n4 => 3
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n5 => 4
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n6 => 5
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n8 => 6
  | BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n10 => 7
  end.
Definition BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F2 n :=
  match n with
  | 0 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n1
  | 1 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n2
  | 2 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n3
  | 3 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n4
  | 4 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n5
  | 5 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n6
  | 6 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n8
  | 7 => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n10
  | _ => BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__n1
  end.
Lemma BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1F2 : forall x : BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Type, (BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1 x <= 7) /\ BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F2 (BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1 x) = x. imp_solve. Qed.
Lemma BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F2F1 : forall (y : nat) (H : y <= 7), BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1 (BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Type : Set :=
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd1
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd2
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd3
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd4
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd5
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd6
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd8
 | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd10
.
Definition BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__cond := (fun (_ : BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Type) => True).
Lemma BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__nat__helper.

Definition BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1 t :=
  match t with
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd1 => 0
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd2 => 1
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd3 => 2
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd4 => 3
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd5 => 4
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd6 => 5
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd8 => 6
  | BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd10 => 7
  end.
Definition BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F2 n :=
  match n with
  | 0 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd1
  | 1 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd2
  | 2 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd3
  | 3 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd4
  | 4 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd5
  | 5 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd6
  | 6 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd8
  | 7 => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd10
  | _ => BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__pbfd1
  end.
Lemma BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1F2 : forall x : BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Type, (BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1 x <= 7) /\ BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F2 (BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F2F1 : forall (y : nat) (H : y <= 7), BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1 (BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F2 y) = y. enum_solve H y. Qed.

Record BeamFailureDetectionSet_r17__Type : Set :=
  make__BeamFailureDetectionSet_r17__Type {
    BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17 : option BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Type ;
    BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17 : option BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Type ;
    BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17 : option BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Type ;
    BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17 : option BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Type ;
}.
Definition BeamFailureDetectionSet_r17__root_list : list seq_elem := (
 Opt BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Type BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__cond ::
 Opt BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Type BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__cond ::
 Opt BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Type BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__cond ::
 Opt BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Type BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__cond ::
 nil).
Definition BeamFailureDetectionSet_r17__ext_list : list typ := (
  nil).
Definition BeamFailureDetectionSet_r17__cond (z : BeamFailureDetectionSet_r17__Type) := 
(  opt_cond BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__cond (BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17 z) /\
  opt_cond BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__cond (BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17 z) /\
  opt_cond BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__cond (BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17 z) /\
  opt_cond BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__cond (BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17 z) /\
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
Definition BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Format : T_Format BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Type BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__cond := seq_of_format BeamLinkMonitoringRS_r17__Format 1 maxNrofBFDResourcePerSet_r17 BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__helper1 BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__helper2.

Opaque BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__cond BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Format.

Definition BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Format : T_Format BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Type BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__cond := seq_of_format BeamLinkMonitoringRS_Id_r17__Format 1 maxNrofBFDResourcePerSet_r17 BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__helper1 BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__helper2.

Opaque BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__cond BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Format.

Definition BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Format : T_Format BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__nat__Format BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1 BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F2 BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F1F2 BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__F2F1.

Opaque BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__cond BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Format.

Definition BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Format : T_Format BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__nat__Format BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1 BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F2 BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F1F2 BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__F2F1.

Opaque BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__cond BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Format.


Definition BeamFailureDetectionSet_r17__root_Format_Type := Eval cbn in seq_format_prod BeamFailureDetectionSet_r17__root_list.
Definition BeamFailureDetectionSet_r17__root_Format_list : BeamFailureDetectionSet_r17__root_Format_Type :=
  (BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17__Format, (BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17__Format, (BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17__Format, (BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17__Format, unit_format)))).

Definition BeamFailureDetectionSet_r17__ext_Format_Type := Eval cbn in get_formats BeamFailureDetectionSet_r17__ext_list.
Definition BeamFailureDetectionSet_r17__ext_Format_list : BeamFailureDetectionSet_r17__ext_Format_Type :=
  unit__Format.

Definition BeamFailureDetectionSet_r17__list_type : Set := (seq_type BeamFailureDetectionSet_r17__root_list) * (seq_ext_type BeamFailureDetectionSet_r17__ext_list).
Definition BeamFailureDetectionSet_r17__list_cond (z : BeamFailureDetectionSet_r17__list_type) : Prop :=
        (seq_cond BeamFailureDetectionSet_r17__root_list (fst z)) /\ (seq_ext_cond BeamFailureDetectionSet_r17__ext_list (snd z)).
Definition BeamFailureDetectionSet_r17__list_format : T_Format BeamFailureDetectionSet_r17__list_type BeamFailureDetectionSet_r17__list_cond :=
 (* Eval compute in *) seq_ext_format BeamFailureDetectionSet_r17__root_list BeamFailureDetectionSet_r17__root_Format_list BeamFailureDetectionSet_r17__ext_list BeamFailureDetectionSet_r17__ext_Format_list.

Opaque BeamFailureDetectionSet_r17__list_format.
Definition BeamFailureDetectionSet_r17__F1 (z : BeamFailureDetectionSet_r17__Type) : BeamFailureDetectionSet_r17__list_type :=
  (((BeamFailureDetectionSet_r17__bfdResourcesToAddModList_r17 z, (BeamFailureDetectionSet_r17__bfdResourcesToReleaseList_r17 z, (BeamFailureDetectionSet_r17__beamFailureInstanceMaxCount_r17 z, (BeamFailureDetectionSet_r17__beamFailureDetectionTimer_r17 z, tt))))), (
tt)).
Definition BeamFailureDetectionSet_r17__F2 (y : BeamFailureDetectionSet_r17__list_type) : BeamFailureDetectionSet_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__BeamFailureDetectionSet_r17__Type j0 j1 j2 j3
  end.
Definition BeamFailureDetectionSet_r17__helper1 : (forall a : BeamFailureDetectionSet_r17__Type, BeamFailureDetectionSet_r17__cond a -> BeamFailureDetectionSet_r17__list_cond (BeamFailureDetectionSet_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BeamFailureDetectionSet_r17__helper2 : (forall a : BeamFailureDetectionSet_r17__Type, BeamFailureDetectionSet_r17__F2 (BeamFailureDetectionSet_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BeamFailureDetectionSet_r17__helper3 : (forall b : BeamFailureDetectionSet_r17__list_type, BeamFailureDetectionSet_r17__list_cond b -> BeamFailureDetectionSet_r17__cond (BeamFailureDetectionSet_r17__F2 b) /\ BeamFailureDetectionSet_r17__F1 (BeamFailureDetectionSet_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BeamFailureDetectionSet_r17__cond, BeamFailureDetectionSet_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BeamFailureDetectionSet_r17__Format : T_Format BeamFailureDetectionSet_r17__Type BeamFailureDetectionSet_r17__cond :=
 proj2_format BeamFailureDetectionSet_r17__cond BeamFailureDetectionSet_r17__list_format  BeamFailureDetectionSet_r17__F1 BeamFailureDetectionSet_r17__F2 BeamFailureDetectionSet_r17__helper1 BeamFailureDetectionSet_r17__helper2 BeamFailureDetectionSet_r17__helper3.

Opaque BeamFailureDetectionSet_r17__cond BeamFailureDetectionSet_r17__Format.

