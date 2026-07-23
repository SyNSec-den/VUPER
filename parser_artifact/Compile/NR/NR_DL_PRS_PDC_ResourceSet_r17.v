Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Format.

Inductive NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Type : Set :=
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n2
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n4
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n6
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n12
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare4
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare3
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare2
 | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare1
.
Definition NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__cond := (fun (_ : NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Type) => True).
Lemma NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__nat__helper.

Definition NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1 t :=
  match t with
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n2 => 0
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n4 => 1
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n6 => 2
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n12 => 3
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare4 => 4
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare3 => 5
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare2 => 6
  | NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare1 => 7
  end.
Definition NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F2 n :=
  match n with
  | 0 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n2
  | 1 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n4
  | 2 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n6
  | 3 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n12
  | 4 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare4
  | 5 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare3
  | 6 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare2
  | 7 => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__spare1
  | _ => NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__n2
  end.
Lemma NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1F2 : forall x : NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Type, (NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1 x <= 7) /\ NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F2 (NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1 x) = x. imp_solve. Qed.
Lemma NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F2F1 : forall (y : nat) (H : y <= 7), NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1 (NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F2 y) = y. enum_solve H y. Qed.

Lemma NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__helper1 : (1 <= 63)%Z.  lia. Qed.
Lemma NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__helper2 : to_bit_sz (Z.to_nat (63 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__Type := Z.
Definition NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__cond := (fun z => (1 <= z <= 63)%Z).
Lemma NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__helper1 : (0 <= 2176)%Z.  lia. Qed.
Lemma NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__helper2 : to_bit_sz (Z.to_nat (2176 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2176 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__Type := Z.
Definition NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__cond := (fun z => (0 <= z <= 2176)%Z).
Require Import NR.NR_DL_PRS_Resource_r17.

Opaque NR_DL_PRS_Resource_r17__cond NR_DL_PRS_Resource_r17__Format.

Definition NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Type := list NR_DL_PRS_Resource_r17__Type.

Lemma NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__helper1 : (0 <= 1 <= maxNrofPRS_ResourcesPerSet_r17)%Z. unfold maxNrofPRS_ResourcesPerSet_r17.
 lia. Qed.
Lemma NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPRS_ResourcesPerSet_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPRS_ResourcesPerSet_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__cond (z : NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPRS_ResourcesPerSet_r17)%Z /\ (list_and NR_DL_PRS_Resource_r17__cond z) .

Require Import NR.RepFactorAndTimeGap_r17.

Opaque RepFactorAndTimeGap_r17__cond RepFactorAndTimeGap_r17__Format.

Record NR_DL_PRS_PDC_ResourceSet_r17__Type : Set :=
  make__NR_DL_PRS_PDC_ResourceSet_r17__Type {
    NR_DL_PRS_PDC_ResourceSet_r17__periodicityAndOffset_r17 : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Type ;
    NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17 : NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Type ;
    NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17 : Z ;
    NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17 : Z ;
    NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17 : NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Type ;
    NR_DL_PRS_PDC_ResourceSet_r17__repFactorAndTimeGap_r17 : option RepFactorAndTimeGap_r17__Type ;
}.
Definition NR_DL_PRS_PDC_ResourceSet_r17__root_list : list seq_elem := (
 Nor NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__cond ::
 Nor NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Type NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__cond ::
 Nor Z NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__cond ::
 Nor Z NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__cond ::
 Nor NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Type NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__cond ::
 Opt RepFactorAndTimeGap_r17__Type RepFactorAndTimeGap_r17__cond ::
 nil).
Definition NR_DL_PRS_PDC_ResourceSet_r17__ext_list : list typ := (
  nil).
Definition NR_DL_PRS_PDC_ResourceSet_r17__cond (z : NR_DL_PRS_PDC_ResourceSet_r17__Type) := 
(  NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__periodicityAndOffset_r17 z) /\
  NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17 z) /\
  NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17 z) /\
  NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17 z) /\
  NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17 z) /\
  opt_cond RepFactorAndTimeGap_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__repFactorAndTimeGap_r17 z) /\
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
Definition NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Format : T_Format NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__nat__Format NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1 NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F2 NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F1F2 NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__F2F1.

Opaque NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__cond NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Format.

Definition NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__Format : T_Format Z NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__cond :=
 ranged_int_format (1) (63) NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__helper1 NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__helper2.

Opaque NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__cond NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__Format.

Definition NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__Format : T_Format Z NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__cond :=
 ranged_int_format (0) (2176) NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__helper1 NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__helper2.

Opaque NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__cond NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__Format.

Definition NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Format : T_Format NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Type NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__cond := seq_of_format NR_DL_PRS_Resource_r17__Format 1 maxNrofPRS_ResourcesPerSet_r17 NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__helper1 NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__helper2.

Opaque NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__cond NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Format.


Definition NR_DL_PRS_PDC_ResourceSet_r17__root_Format_Type := Eval cbn in seq_format_prod NR_DL_PRS_PDC_ResourceSet_r17__root_list.
Definition NR_DL_PRS_PDC_ResourceSet_r17__root_Format_list : NR_DL_PRS_PDC_ResourceSet_r17__root_Format_Type :=
  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Format, (NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17__Format, (NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17__Format, (NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17__Format, (NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17__Format, (RepFactorAndTimeGap_r17__Format, unit_format)))))).

Definition NR_DL_PRS_PDC_ResourceSet_r17__ext_Format_Type := Eval cbn in get_formats NR_DL_PRS_PDC_ResourceSet_r17__ext_list.
Definition NR_DL_PRS_PDC_ResourceSet_r17__ext_Format_list : NR_DL_PRS_PDC_ResourceSet_r17__ext_Format_Type :=
  unit__Format.

Definition NR_DL_PRS_PDC_ResourceSet_r17__list_type : Set := (seq_type NR_DL_PRS_PDC_ResourceSet_r17__root_list) * (seq_ext_type NR_DL_PRS_PDC_ResourceSet_r17__ext_list).
Definition NR_DL_PRS_PDC_ResourceSet_r17__list_cond (z : NR_DL_PRS_PDC_ResourceSet_r17__list_type) : Prop :=
        (seq_cond NR_DL_PRS_PDC_ResourceSet_r17__root_list (fst z)) /\ (seq_ext_cond NR_DL_PRS_PDC_ResourceSet_r17__ext_list (snd z)).
Definition NR_DL_PRS_PDC_ResourceSet_r17__list_format : T_Format NR_DL_PRS_PDC_ResourceSet_r17__list_type NR_DL_PRS_PDC_ResourceSet_r17__list_cond :=
 (* Eval compute in *) seq_ext_format NR_DL_PRS_PDC_ResourceSet_r17__root_list NR_DL_PRS_PDC_ResourceSet_r17__root_Format_list NR_DL_PRS_PDC_ResourceSet_r17__ext_list NR_DL_PRS_PDC_ResourceSet_r17__ext_Format_list.

Opaque NR_DL_PRS_PDC_ResourceSet_r17__list_format.
Definition NR_DL_PRS_PDC_ResourceSet_r17__F1 (z : NR_DL_PRS_PDC_ResourceSet_r17__Type) : NR_DL_PRS_PDC_ResourceSet_r17__list_type :=
  (((NR_DL_PRS_PDC_ResourceSet_r17__periodicityAndOffset_r17 z, (NR_DL_PRS_PDC_ResourceSet_r17__numSymbols_r17 z, (NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_ResourceBandwidth_r17 z, (NR_DL_PRS_PDC_ResourceSet_r17__dl_PRS_StartPRB_r17 z, (NR_DL_PRS_PDC_ResourceSet_r17__resourceList_r17 z, (NR_DL_PRS_PDC_ResourceSet_r17__repFactorAndTimeGap_r17 z, tt))))))), (
tt)).
Definition NR_DL_PRS_PDC_ResourceSet_r17__F2 (y : NR_DL_PRS_PDC_ResourceSet_r17__list_type) : NR_DL_PRS_PDC_ResourceSet_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__NR_DL_PRS_PDC_ResourceSet_r17__Type j0 j1 j2 j3 j4 j5
  end.
Definition NR_DL_PRS_PDC_ResourceSet_r17__helper1 : (forall a : NR_DL_PRS_PDC_ResourceSet_r17__Type, NR_DL_PRS_PDC_ResourceSet_r17__cond a -> NR_DL_PRS_PDC_ResourceSet_r17__list_cond (NR_DL_PRS_PDC_ResourceSet_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__helper2 : (forall a : NR_DL_PRS_PDC_ResourceSet_r17__Type, NR_DL_PRS_PDC_ResourceSet_r17__F2 (NR_DL_PRS_PDC_ResourceSet_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__helper3 : (forall b : NR_DL_PRS_PDC_ResourceSet_r17__list_type, NR_DL_PRS_PDC_ResourceSet_r17__list_cond b -> NR_DL_PRS_PDC_ResourceSet_r17__cond (NR_DL_PRS_PDC_ResourceSet_r17__F2 b) /\ NR_DL_PRS_PDC_ResourceSet_r17__F1 (NR_DL_PRS_PDC_ResourceSet_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NR_DL_PRS_PDC_ResourceSet_r17__cond, NR_DL_PRS_PDC_ResourceSet_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NR_DL_PRS_PDC_ResourceSet_r17__Format : T_Format NR_DL_PRS_PDC_ResourceSet_r17__Type NR_DL_PRS_PDC_ResourceSet_r17__cond :=
 proj2_format NR_DL_PRS_PDC_ResourceSet_r17__cond NR_DL_PRS_PDC_ResourceSet_r17__list_format  NR_DL_PRS_PDC_ResourceSet_r17__F1 NR_DL_PRS_PDC_ResourceSet_r17__F2 NR_DL_PRS_PDC_ResourceSet_r17__helper1 NR_DL_PRS_PDC_ResourceSet_r17__helper2 NR_DL_PRS_PDC_ResourceSet_r17__helper3.

Opaque NR_DL_PRS_PDC_ResourceSet_r17__cond NR_DL_PRS_PDC_ResourceSet_r17__Format.

