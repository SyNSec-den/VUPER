Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_PSSCH_TxConfigList_r16.

Opaque SL_PSSCH_TxConfigList_r16__cond SL_PSSCH_TxConfigList_r16__Format.

Inductive SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Type : Set :=
 | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0
 | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot2
 | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot4
 | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot6
 | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot8
.
Definition SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__cond := (fun (_ : SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Type) => True).
Lemma SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__nat__helper.

Definition SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1 t :=
  match t with
  | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0 => 0
  | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot2 => 1
  | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot4 => 2
  | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot6 => 3
  | SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot8 => 4
  end.
Definition SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F2 n :=
  match n with
  | 0 => SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0
  | 1 => SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot2
  | 2 => SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot4
  | 3 => SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot6
  | 4 => SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0dot8
  | _ => SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__v0
  end.
Lemma SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1F2 : forall x : SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Type, (SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1 x <= 4) /\ SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F2 (SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F2F1 : forall (y : nat) (H : y <= 4), SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1 (SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Type : Set :=
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n1
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n2
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n3
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n4
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n5
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n6
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n7
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n8
 | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n9
.
Definition SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__cond := (fun (_ : SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Type) => True).
Lemma SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__nat__helper : to_bit_sz 8 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__nat__Format : T_Format nat (fun z => (z <= 8)) :=
  nat_enum_format 8 SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__nat__helper.

Definition SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1 t :=
  match t with
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n1 => 0
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n2 => 1
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n3 => 2
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n4 => 3
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n5 => 4
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n6 => 5
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n7 => 6
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n8 => 7
  | SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n9 => 8
  end.
Definition SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F2 n :=
  match n with
  | 0 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n1
  | 1 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n2
  | 2 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n3
  | 3 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n4
  | 4 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n5
  | 5 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n6
  | 6 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n7
  | 7 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n8
  | 8 => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n9
  | _ => SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__n1
  end.
Lemma SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1F2 : forall x : SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Type, (SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1 x <= 8) /\ SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F2 (SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F2F1 : forall (y : nat) (H : y <= 8), SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1 (SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_CBR_CommonTxConfigList_r16.

Opaque SL_CBR_CommonTxConfigList_r16__cond SL_CBR_CommonTxConfigList_r16__Format.

Lemma SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__Type := Z.
Definition SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__cond := (fun z => (1 <= z <= 16)%Z).
Lemma SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__Type := Z.
Definition SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__cond := (fun z => (1 <= z <= 8)%Z).
Record SL_UE_SelectedConfig_r16__Type : Set :=
  make__SL_UE_SelectedConfig_r16__Type {
    SL_UE_SelectedConfig_r16__sl_PSSCH_TxConfigList_r16 : option SL_PSSCH_TxConfigList_r16__Type ;
    SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16 : option SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Type ;
    SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16 : option SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Type ;
    SL_UE_SelectedConfig_r16__sl_CBR_CommonTxConfigList_r16 : option SL_CBR_CommonTxConfigList_r16__Type ;
    SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16 : option Z ;
    SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16 : option Z ;
}.
Definition SL_UE_SelectedConfig_r16__root_list : list seq_elem := (
 Opt SL_PSSCH_TxConfigList_r16__Type SL_PSSCH_TxConfigList_r16__cond ::
 Opt SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Type SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__cond ::
 Opt SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Type SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__cond ::
 Opt SL_CBR_CommonTxConfigList_r16__Type SL_CBR_CommonTxConfigList_r16__cond ::
 Opt Z SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__cond ::
 Opt Z SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__cond ::
 nil).
Definition SL_UE_SelectedConfig_r16__ext_list : list typ := (
  nil).
Definition SL_UE_SelectedConfig_r16__cond (z : SL_UE_SelectedConfig_r16__Type) := 
(  opt_cond SL_PSSCH_TxConfigList_r16__cond (SL_UE_SelectedConfig_r16__sl_PSSCH_TxConfigList_r16 z) /\
  opt_cond SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__cond (SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16 z) /\
  opt_cond SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__cond (SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16 z) /\
  opt_cond SL_CBR_CommonTxConfigList_r16__cond (SL_UE_SelectedConfig_r16__sl_CBR_CommonTxConfigList_r16 z) /\
  opt_cond SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__cond (SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16 z) /\
  opt_cond SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__cond (SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16 z) /\
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
Definition SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Format : T_Format SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__nat__Format SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1 SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F2 SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F1F2 SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__F2F1.

Opaque SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__cond SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Format.

Definition SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Format : T_Format SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__nat__Format SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1 SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F2 SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F1F2 SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__F2F1.

Opaque SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__cond SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Format.

Definition SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__Format : T_Format Z SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__cond :=
 ranged_int_format (1) (16) SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__helper1 SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__helper2.

Opaque SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__cond SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__Format.

Definition SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__Format : T_Format Z SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__cond :=
 ranged_int_format (1) (8) SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__helper1 SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__helper2.

Opaque SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__cond SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__Format.


Definition SL_UE_SelectedConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_UE_SelectedConfig_r16__root_list.
Definition SL_UE_SelectedConfig_r16__root_Format_list : SL_UE_SelectedConfig_r16__root_Format_Type :=
  (SL_PSSCH_TxConfigList_r16__Format, (SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16__Format, (SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16__Format, (SL_CBR_CommonTxConfigList_r16__Format, (SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16__Format, (SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16__Format, unit_format)))))).

Definition SL_UE_SelectedConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_UE_SelectedConfig_r16__ext_list.
Definition SL_UE_SelectedConfig_r16__ext_Format_list : SL_UE_SelectedConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_UE_SelectedConfig_r16__list_type : Set := (seq_type SL_UE_SelectedConfig_r16__root_list) * (seq_ext_type SL_UE_SelectedConfig_r16__ext_list).
Definition SL_UE_SelectedConfig_r16__list_cond (z : SL_UE_SelectedConfig_r16__list_type) : Prop :=
        (seq_cond SL_UE_SelectedConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_UE_SelectedConfig_r16__ext_list (snd z)).
Definition SL_UE_SelectedConfig_r16__list_format : T_Format SL_UE_SelectedConfig_r16__list_type SL_UE_SelectedConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_UE_SelectedConfig_r16__root_list SL_UE_SelectedConfig_r16__root_Format_list SL_UE_SelectedConfig_r16__ext_list SL_UE_SelectedConfig_r16__ext_Format_list.

Opaque SL_UE_SelectedConfig_r16__list_format.
Definition SL_UE_SelectedConfig_r16__F1 (z : SL_UE_SelectedConfig_r16__Type) : SL_UE_SelectedConfig_r16__list_type :=
  (((SL_UE_SelectedConfig_r16__sl_PSSCH_TxConfigList_r16 z, (SL_UE_SelectedConfig_r16__sl_ProbResourceKeep_r16 z, (SL_UE_SelectedConfig_r16__sl_ReselectAfter_r16 z, (SL_UE_SelectedConfig_r16__sl_CBR_CommonTxConfigList_r16 z, (SL_UE_SelectedConfig_r16__ul_PrioritizationThres_r16 z, (SL_UE_SelectedConfig_r16__sl_PrioritizationThres_r16 z, tt))))))), (
tt)).
Definition SL_UE_SelectedConfig_r16__F2 (y : SL_UE_SelectedConfig_r16__list_type) : SL_UE_SelectedConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SL_UE_SelectedConfig_r16__Type j0 j1 j2 j3 j4 j5
  end.
Definition SL_UE_SelectedConfig_r16__helper1 : (forall a : SL_UE_SelectedConfig_r16__Type, SL_UE_SelectedConfig_r16__cond a -> SL_UE_SelectedConfig_r16__list_cond (SL_UE_SelectedConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_UE_SelectedConfig_r16__helper2 : (forall a : SL_UE_SelectedConfig_r16__Type, SL_UE_SelectedConfig_r16__F2 (SL_UE_SelectedConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_UE_SelectedConfig_r16__helper3 : (forall b : SL_UE_SelectedConfig_r16__list_type, SL_UE_SelectedConfig_r16__list_cond b -> SL_UE_SelectedConfig_r16__cond (SL_UE_SelectedConfig_r16__F2 b) /\ SL_UE_SelectedConfig_r16__F1 (SL_UE_SelectedConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_UE_SelectedConfig_r16__cond, SL_UE_SelectedConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_UE_SelectedConfig_r16__Format : T_Format SL_UE_SelectedConfig_r16__Type SL_UE_SelectedConfig_r16__cond :=
 proj2_format SL_UE_SelectedConfig_r16__cond SL_UE_SelectedConfig_r16__list_format  SL_UE_SelectedConfig_r16__F1 SL_UE_SelectedConfig_r16__F2 SL_UE_SelectedConfig_r16__helper1 SL_UE_SelectedConfig_r16__helper2 SL_UE_SelectedConfig_r16__helper3.

Opaque SL_UE_SelectedConfig_r16__cond SL_UE_SelectedConfig_r16__Format.

