Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NTN_Config_r17.

Opaque NTN_Config_r17__cond NTN_Config_r17__Format.

Lemma SIB19_r17__t_Service_r17__helper1 : (0 <= 549755813887)%Z.  lia. Qed.
Lemma SIB19_r17__t_Service_r17__helper2 : to_bit_sz (Z.to_nat (549755813887 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (549755813887 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB19_r17__t_Service_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB19_r17__t_Service_r17__Type := Z.
Definition SIB19_r17__t_Service_r17__cond := (fun z => (0 <= z <= 549755813887)%Z).
Require Import NR.ReferenceLocation_r17.

Opaque ReferenceLocation_r17__cond ReferenceLocation_r17__Format.

Lemma SIB19_r17__distanceThresh_r17__helper1 : (0 <= 65525)%Z.  lia. Qed.
Lemma SIB19_r17__distanceThresh_r17__helper2 : to_bit_sz (Z.to_nat (65525 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65525 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB19_r17__distanceThresh_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB19_r17__distanceThresh_r17__Type := Z.
Definition SIB19_r17__distanceThresh_r17__cond := (fun z => (0 <= z <= 65525)%Z).
Require Import NR.NTN_NeighCellConfigList_r17.

Opaque NTN_NeighCellConfigList_r17__cond NTN_NeighCellConfigList_r17__Format.

Require Import NR.NTN_NeighCellConfigList_r17.

Opaque NTN_NeighCellConfigList_r17__cond NTN_NeighCellConfigList_r17__Format.

Record SIB19_r17__ext0O__Type : Set :=
  make__SIB19_r17__ext0O__Type {
    SIB19_r17__ext0O__ntn_NeighCellConfigListExt_v1720 : option NTN_NeighCellConfigList_r17__Type ;
}.
Definition SIB19_r17__ext0O__list := (
 Opt NTN_NeighCellConfigList_r17__Type NTN_NeighCellConfigList_r17__cond ::
 nil).
Definition SIB19_r17__ext0O__cond z := 
  opt_cond NTN_NeighCellConfigList_r17__cond (SIB19_r17__ext0O__ntn_NeighCellConfigListExt_v1720 z) /\
  True.

Definition SIB19_r17__ext0__Type := SIB19_r17__ext0O__Type.
Definition SIB19_r17__ext0__cond := SIB19_r17__ext0O__cond.

Record SIB19_r17__Type : Set :=
  make__SIB19_r17__Type {
    SIB19_r17__ntn_Config_r17 : option NTN_Config_r17__Type ;
    SIB19_r17__t_Service_r17 : option Z ;
    SIB19_r17__referenceLocation_r17 : option ReferenceLocation_r17__Type ;
    SIB19_r17__distanceThresh_r17 : option Z ;
    SIB19_r17__ntn_NeighCellConfigList_r17 : option NTN_NeighCellConfigList_r17__Type ;
    SIB19_r17__lateNonCriticalExtension : option octet_string ;
    SIB19_r17__ext0 : option SIB19_r17__ext0__Type ;
}.
Definition SIB19_r17__root_list : list seq_elem := (
 Opt NTN_Config_r17__Type NTN_Config_r17__cond ::
 Opt Z SIB19_r17__t_Service_r17__cond ::
 Opt ReferenceLocation_r17__Type ReferenceLocation_r17__cond ::
 Opt Z SIB19_r17__distanceThresh_r17__cond ::
 Opt NTN_NeighCellConfigList_r17__Type NTN_NeighCellConfigList_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB19_r17__ext_list : list typ := (
  typ_cons SIB19_r17__ext0__Type SIB19_r17__ext0__cond ::
  nil).
Definition SIB19_r17__cond (z : SIB19_r17__Type) := 
(  opt_cond NTN_Config_r17__cond (SIB19_r17__ntn_Config_r17 z) /\
  opt_cond SIB19_r17__t_Service_r17__cond (SIB19_r17__t_Service_r17 z) /\
  opt_cond ReferenceLocation_r17__cond (SIB19_r17__referenceLocation_r17 z) /\
  opt_cond SIB19_r17__distanceThresh_r17__cond (SIB19_r17__distanceThresh_r17 z) /\
  opt_cond NTN_NeighCellConfigList_r17__cond (SIB19_r17__ntn_NeighCellConfigList_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB19_r17__lateNonCriticalExtension z) /\
  True) /\ 
(  opt_cond SIB19_r17__ext0__cond (SIB19_r17__ext0 z) /\
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
Definition SIB19_r17__t_Service_r17__Format : T_Format Z SIB19_r17__t_Service_r17__cond :=
 ranged_int_format (0) (549755813887) SIB19_r17__t_Service_r17__helper1 SIB19_r17__t_Service_r17__helper2.

Opaque SIB19_r17__t_Service_r17__cond SIB19_r17__t_Service_r17__Format.

Definition SIB19_r17__distanceThresh_r17__Format : T_Format Z SIB19_r17__distanceThresh_r17__cond :=
 ranged_int_format (0) (65525) SIB19_r17__distanceThresh_r17__helper1 SIB19_r17__distanceThresh_r17__helper2.

Opaque SIB19_r17__distanceThresh_r17__cond SIB19_r17__distanceThresh_r17__Format.


Definition SIB19_r17__ext0O__Format_Type := Eval cbn in seq_format_prod SIB19_r17__ext0O__list.
Definition SIB19_r17__ext0O__Format_list : SIB19_r17__ext0O__Format_Type :=
  (NTN_NeighCellConfigList_r17__Format, unit_format).
Definition SIB19_r17__ext0O__list__Format := (*Eval compute in *) seq_format SIB19_r17__ext0O__list SIB19_r17__ext0O__Format_list.
Definition SIB19_r17__ext0O__F1 z :=
  (SIB19_r17__ext0O__ntn_NeighCellConfigListExt_v1720 z, tt).
Definition SIB19_r17__ext0O__F2 (y : seq_type SIB19_r17__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SIB19_r17__ext0O__Type i0
  end.
Lemma SIB19_r17__ext0O__F1F2_cond (z : SIB19_r17__ext0O__Type)
  : SIB19_r17__ext0O__cond z ->
  (seq_cond SIB19_r17__ext0O__list (SIB19_r17__ext0O__F1 z)).
intro H. unfold SIB19_r17__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB19_r17__ext0O__F1F2_cond2 (z : SIB19_r17__ext0O__Type)
 : SIB19_r17__ext0O__F2 (SIB19_r17__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB19_r17__ext0O__F2F1_cond (y : seq_type SIB19_r17__ext0O__list)
  : seq_cond SIB19_r17__ext0O__list y ->
 (SIB19_r17__ext0O__cond (SIB19_r17__ext0O__F2 y)) /\  SIB19_r17__ext0O__F1 (SIB19_r17__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB19_r17__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB19_r17__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB19_r17__ext0O__Format : T_Format SIB19_r17__ext0O__Type SIB19_r17__ext0O__cond :=
        proj2_format  SIB19_r17__ext0O__cond SIB19_r17__ext0O__list__Format
    SIB19_r17__ext0O__F1 SIB19_r17__ext0O__F2 SIB19_r17__ext0O__F1F2_cond  SIB19_r17__ext0O__F1F2_cond2 SIB19_r17__ext0O__F2F1_cond.
Opaque SIB19_r17__ext0O__cond SIB19_r17__ext0O__Format.

Definition SIB19_r17__ext0__check_all_none (b : SIB19_r17__ext0O__Type) : bool :=
match b with 
  | make__SIB19_r17__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SIB19_r17__ext0__Format : T_Format SIB19_r17__ext0__Type SIB19_r17__ext0__cond :=
  restrict_add_format SIB19_r17__ext0__check_all_none SIB19_r17__ext0O__Format.

Opaque SIB19_r17__ext0__cond SIB19_r17__ext0__Format.


Definition SIB19_r17__root_Format_Type := Eval cbn in seq_format_prod SIB19_r17__root_list.
Definition SIB19_r17__root_Format_list : SIB19_r17__root_Format_Type :=
  (NTN_Config_r17__Format, (SIB19_r17__t_Service_r17__Format, (ReferenceLocation_r17__Format, (SIB19_r17__distanceThresh_r17__Format, (NTN_NeighCellConfigList_r17__Format, (octet_string_nc__Format, unit_format)))))).

Definition SIB19_r17__ext_Format_Type := Eval cbn in get_formats SIB19_r17__ext_list.
Definition SIB19_r17__ext_Format_list : SIB19_r17__ext_Format_Type :=
  (SIB19_r17__ext0__Format, unit__Format).

Definition SIB19_r17__list_type : Set := (seq_type SIB19_r17__root_list) * (seq_ext_type SIB19_r17__ext_list).
Definition SIB19_r17__list_cond (z : SIB19_r17__list_type) : Prop :=
        (seq_cond SIB19_r17__root_list (fst z)) /\ (seq_ext_cond SIB19_r17__ext_list (snd z)).
Definition SIB19_r17__list_format : T_Format SIB19_r17__list_type SIB19_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SIB19_r17__root_list SIB19_r17__root_Format_list SIB19_r17__ext_list SIB19_r17__ext_Format_list.

Opaque SIB19_r17__list_format.
Definition SIB19_r17__F1 (z : SIB19_r17__Type) : SIB19_r17__list_type :=
  (((SIB19_r17__ntn_Config_r17 z, (SIB19_r17__t_Service_r17 z, (SIB19_r17__referenceLocation_r17 z, (SIB19_r17__distanceThresh_r17 z, (SIB19_r17__ntn_NeighCellConfigList_r17 z, (SIB19_r17__lateNonCriticalExtension z, tt))))))), (
(SIB19_r17__ext0 z, tt))).
Definition SIB19_r17__F2 (y : SIB19_r17__list_type) : SIB19_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__SIB19_r17__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition SIB19_r17__helper1 : (forall a : SIB19_r17__Type, SIB19_r17__cond a -> SIB19_r17__list_cond (SIB19_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB19_r17__helper2 : (forall a : SIB19_r17__Type, SIB19_r17__F2 (SIB19_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB19_r17__helper3 : (forall b : SIB19_r17__list_type, SIB19_r17__list_cond b -> SIB19_r17__cond (SIB19_r17__F2 b) /\ SIB19_r17__F1 (SIB19_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB19_r17__cond, SIB19_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB19_r17__Format : T_Format SIB19_r17__Type SIB19_r17__cond :=
 proj2_format SIB19_r17__cond SIB19_r17__list_format  SIB19_r17__F1 SIB19_r17__F2 SIB19_r17__helper1 SIB19_r17__helper2 SIB19_r17__helper3.

Opaque SIB19_r17__cond SIB19_r17__Format.

