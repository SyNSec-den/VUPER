Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_ResourceConfigId.

Opaque CSI_ResourceConfigId__cond CSI_ResourceConfigId__Format.

Require Import NR.NZP_CSI_RS_ResourceSetId.

Opaque NZP_CSI_RS_ResourceSetId__cond NZP_CSI_RS_ResourceSetId__Format.

Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Type := list NZP_CSI_RS_ResourceSetId__Type.

Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_ResourceSetsPerConfig)%Z. unfold maxNrofNZP_CSI_RS_ResourceSetsPerConfig.
 lia. Qed.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_ResourceSetsPerConfig - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_ResourceSetsPerConfig - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__cond (z : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_ResourceSetsPerConfig)%Z /\ (list_and NZP_CSI_RS_ResourceSetId__cond z) .

Require Import NR.CSI_SSB_ResourceSetId.

Opaque CSI_SSB_ResourceSetId__cond CSI_SSB_ResourceSetId__Format.

Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Type := list CSI_SSB_ResourceSetId__Type.

Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__helper1 : (0 <= 1 <= maxNrofCSI_SSB_ResourceSetsPerConfig)%Z. unfold maxNrofCSI_SSB_ResourceSetsPerConfig.
 lia. Qed.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_SSB_ResourceSetsPerConfig - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_SSB_ResourceSetsPerConfig - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__cond (z : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_SSB_ResourceSetsPerConfig)%Z /\ (list_and CSI_SSB_ResourceSetId__cond z) .

Record CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type : Set :=
  make__CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type {
    CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList : option CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Type ;
    CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList : option CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Type ;
}.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list := (
 Opt CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__cond ::
 Opt CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__cond ::
 nil).
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond z := 
  opt_cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__cond (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList z) /\
  opt_cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__cond (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList z) /\
  True.

Require Import NR.CSI_IM_ResourceSetId.

Opaque CSI_IM_ResourceSetId__cond CSI_IM_ResourceSetId__Format.

Definition CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Type := list CSI_IM_ResourceSetId__Type.

Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__helper1 : (0 <= 1 <= maxNrofCSI_IM_ResourceSetsPerConfig)%Z. unfold maxNrofCSI_IM_ResourceSetsPerConfig.
 lia. Qed.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_IM_ResourceSetsPerConfig - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_IM_ResourceSetsPerConfig - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__cond (z : CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_IM_ResourceSetsPerConfig)%Z /\ (list_and CSI_IM_ResourceSetId__cond z) .


Inductive CSI_ResourceConfig__csi_RS_ResourceSetList__Type : Set :=
  | CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type -> CSI_ResourceConfig__csi_RS_ResourceSetList__Type
  | CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList : CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Type -> CSI_ResourceConfig__csi_RS_ResourceSetList__Type
.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__list : list typ := (
typ_cons CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond ::
typ_cons CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__cond ::
 nil).
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__cond (c : CSI_ResourceConfig__csi_RS_ResourceSetList__Type) := 
  match c with
  | CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB t => CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond t 
  | CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList t => CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__cond t 
  end.

Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__len_helper1 : to_bit_sz (length CSI_ResourceConfig__csi_RS_ResourceSetList__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__len_helper2 : 2 <= length2 CSI_ResourceConfig__csi_RS_ResourceSetList__list.
 simpl. lia. Qed.
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Inductive CSI_ResourceConfig__resourceType__Type : Set :=
 | CSI_ResourceConfig__resourceType__aperiodic
 | CSI_ResourceConfig__resourceType__semiPersistent
 | CSI_ResourceConfig__resourceType__periodic
.
Definition CSI_ResourceConfig__resourceType__cond := (fun (_ : CSI_ResourceConfig__resourceType__Type) => True).
Lemma CSI_ResourceConfig__resourceType__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ResourceConfig__resourceType__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CSI_ResourceConfig__resourceType__nat__helper.

Definition CSI_ResourceConfig__resourceType__F1 t :=
  match t with
  | CSI_ResourceConfig__resourceType__aperiodic => 0
  | CSI_ResourceConfig__resourceType__semiPersistent => 1
  | CSI_ResourceConfig__resourceType__periodic => 2
  end.
Definition CSI_ResourceConfig__resourceType__F2 n :=
  match n with
  | 0 => CSI_ResourceConfig__resourceType__aperiodic
  | 1 => CSI_ResourceConfig__resourceType__semiPersistent
  | 2 => CSI_ResourceConfig__resourceType__periodic
  | _ => CSI_ResourceConfig__resourceType__aperiodic
  end.
Lemma CSI_ResourceConfig__resourceType__F1F2 : forall x : CSI_ResourceConfig__resourceType__Type, (CSI_ResourceConfig__resourceType__F1 x <= 2) /\ CSI_ResourceConfig__resourceType__F2 (CSI_ResourceConfig__resourceType__F1 x) = x. imp_solve. Qed.
Lemma CSI_ResourceConfig__resourceType__F2F1 : forall (y : nat) (H : y <= 2), CSI_ResourceConfig__resourceType__F1 (CSI_ResourceConfig__resourceType__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CSI_SSB_ResourceSetId.

Opaque CSI_SSB_ResourceSetId__cond CSI_SSB_ResourceSetId__Format.

Record CSI_ResourceConfig__ext0O__Type : Set :=
  make__CSI_ResourceConfig__ext0O__Type {
    CSI_ResourceConfig__ext0O__csi_SSB_ResourceSetListExt_r17 : option CSI_SSB_ResourceSetId__Type ;
}.
Definition CSI_ResourceConfig__ext0O__list := (
 Opt CSI_SSB_ResourceSetId__Type CSI_SSB_ResourceSetId__cond ::
 nil).
Definition CSI_ResourceConfig__ext0O__cond z := 
  opt_cond CSI_SSB_ResourceSetId__cond (CSI_ResourceConfig__ext0O__csi_SSB_ResourceSetListExt_r17 z) /\
  True.

Definition CSI_ResourceConfig__ext0__Type := CSI_ResourceConfig__ext0O__Type.
Definition CSI_ResourceConfig__ext0__cond := CSI_ResourceConfig__ext0O__cond.

Record CSI_ResourceConfig__Type : Set :=
  make__CSI_ResourceConfig__Type {
    CSI_ResourceConfig__csi_ResourceConfigId : CSI_ResourceConfigId__Type ;
    CSI_ResourceConfig__csi_RS_ResourceSetList : CSI_ResourceConfig__csi_RS_ResourceSetList__Type ;
    CSI_ResourceConfig__bwp_Id : BWP_Id__Type ;
    CSI_ResourceConfig__resourceType : CSI_ResourceConfig__resourceType__Type ;
    CSI_ResourceConfig__ext0 : option CSI_ResourceConfig__ext0__Type ;
}.
Definition CSI_ResourceConfig__root_list : list seq_elem := (
 Nor CSI_ResourceConfigId__Type CSI_ResourceConfigId__cond ::
 Nor CSI_ResourceConfig__csi_RS_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__cond ::
 Nor BWP_Id__Type BWP_Id__cond ::
 Nor CSI_ResourceConfig__resourceType__Type CSI_ResourceConfig__resourceType__cond ::
 nil).
Definition CSI_ResourceConfig__ext_list : list typ := (
  typ_cons CSI_ResourceConfig__ext0__Type CSI_ResourceConfig__ext0__cond ::
  nil).
Definition CSI_ResourceConfig__cond (z : CSI_ResourceConfig__Type) := 
(  CSI_ResourceConfigId__cond (CSI_ResourceConfig__csi_ResourceConfigId z) /\
  CSI_ResourceConfig__csi_RS_ResourceSetList__cond (CSI_ResourceConfig__csi_RS_ResourceSetList z) /\
  BWP_Id__cond (CSI_ResourceConfig__bwp_Id z) /\
  CSI_ResourceConfig__resourceType__cond (CSI_ResourceConfig__resourceType z) /\
  True) /\ 
(  opt_cond CSI_ResourceConfig__ext0__cond (CSI_ResourceConfig__ext0 z) /\
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
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Format : T_Format CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__cond := seq_of_format NZP_CSI_RS_ResourceSetId__Format 1 maxNrofNZP_CSI_RS_ResourceSetsPerConfig CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__helper1 CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__helper2.

Opaque CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Format.

Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Format : T_Format CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__cond := seq_of_format CSI_SSB_ResourceSetId__Format 1 maxNrofCSI_SSB_ResourceSetsPerConfig CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__helper1 CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__helper2.

Opaque CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Format.


Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format_Type := Eval cbn in seq_format_prod CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format_list : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format_Type :=
  (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList__Format, (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList__Format, unit_format)).
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list__Format := (*Eval compute in *) seq_format CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format_list.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1 z :=
  (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__nzp_CSI_RS_ResourceSetList z, (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__csi_SSB_ResourceSetList z, tt)).
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2 (y : seq_type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type i0 i1
  end.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1F2_cond (z : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type)
  : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond z ->
  (seq_cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1 z)).
intro H. unfold CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond in H. simpl. auto. Qed.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1F2_cond2 (z : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type)
 : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2 (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2F1_cond (y : seq_type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list)
  : seq_cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list y ->
 (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2 y)) /\  CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1 (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond. simpl in *. auto.
 - simpl. unfold CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format : T_Format CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond :=
        proj2_format  CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__list__Format
    CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1 CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2 CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1F2_cond  CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F1F2_cond2 CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__F2F1_cond.
Opaque CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__cond CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format.

Definition CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Format : T_Format CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__cond := seq_of_format CSI_IM_ResourceSetId__Format 1 maxNrofCSI_IM_ResourceSetsPerConfig CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__helper1 CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__helper2.

Opaque CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__cond CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Format.


Definition CSI_ResourceConfig__csi_RS_ResourceSetList__Format_Type := Eval cbn in get_formats CSI_ResourceConfig__csi_RS_ResourceSetList__list.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__Format_list : CSI_ResourceConfig__csi_RS_ResourceSetList__Format_Type :=
  (CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Format, (CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Format, unit__Format)).
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__list__Format := Eval compute in choice_format CSI_ResourceConfig__csi_RS_ResourceSetList__list CSI_ResourceConfig__csi_RS_ResourceSetList__len_helper1 CSI_ResourceConfig__csi_RS_ResourceSetList__len_helper2  CSI_ResourceConfig__csi_RS_ResourceSetList__Format_list.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__F1 (z : CSI_ResourceConfig__csi_RS_ResourceSetList__Type) : (choice CSI_ResourceConfig__csi_RS_ResourceSetList__list) :=
  match z with
   | CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB t => existT _ 0 t
  | CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList t => existT _ 1 t
  end.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__g := (fun n => typ_set (get_nth_typ CSI_ResourceConfig__csi_RS_ResourceSetList__list n)).
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__F2 (y : choice CSI_ResourceConfig__csi_RS_ResourceSetList__list) : CSI_ResourceConfig__csi_RS_ResourceSetList__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ResourceConfig__csi_RS_ResourceSetList__g n -> CSI_ResourceConfig__csi_RS_ResourceSetList__Type) with
    | 0 => fun (t : CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB__Type) => CSI_ResourceConfig__csi_RS_ResourceSetList__nzp_CSI_RS_SSB t 
    | 1 => fun (t : CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList__Type) => CSI_ResourceConfig__csi_RS_ResourceSetList__csi_IM_ResourceSetList t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CSI_ResourceConfig__csi_RS_ResourceSetList__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CSI_ResourceConfig__csi_RS_ResourceSetList__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ResourceConfig__csi_RS_ResourceSetList__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CSI_ResourceConfig__csi_RS_ResourceSetList__Type with end) n0
           end t0).

Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__helper2 :  forall (y : CSI_ResourceConfig__csi_RS_ResourceSetList__Type), CSI_ResourceConfig__csi_RS_ResourceSetList__cond y -> choice_cond CSI_ResourceConfig__csi_RS_ResourceSetList__list (CSI_ResourceConfig__csi_RS_ResourceSetList__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__helper3 :  forall (y : CSI_ResourceConfig__csi_RS_ResourceSetList__Type), CSI_ResourceConfig__csi_RS_ResourceSetList__F2 (CSI_ResourceConfig__csi_RS_ResourceSetList__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ResourceConfig__csi_RS_ResourceSetList__helper4 : (forall b : choice CSI_ResourceConfig__csi_RS_ResourceSetList__list, choice_cond CSI_ResourceConfig__csi_RS_ResourceSetList__list b -> CSI_ResourceConfig__csi_RS_ResourceSetList__cond (CSI_ResourceConfig__csi_RS_ResourceSetList__F2 b) /\ CSI_ResourceConfig__csi_RS_ResourceSetList__F1 (CSI_ResourceConfig__csi_RS_ResourceSetList__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ResourceConfig__csi_RS_ResourceSetList__F1 CSI_ResourceConfig__csi_RS_ResourceSetList__F2.
Definition CSI_ResourceConfig__csi_RS_ResourceSetList__Format : T_Format CSI_ResourceConfig__csi_RS_ResourceSetList__Type CSI_ResourceConfig__csi_RS_ResourceSetList__cond :=
  (* Eval compute in *) proj2_format CSI_ResourceConfig__csi_RS_ResourceSetList__cond CSI_ResourceConfig__csi_RS_ResourceSetList__list__Format CSI_ResourceConfig__csi_RS_ResourceSetList__F1 CSI_ResourceConfig__csi_RS_ResourceSetList__F2 CSI_ResourceConfig__csi_RS_ResourceSetList__helper2 CSI_ResourceConfig__csi_RS_ResourceSetList__helper3 CSI_ResourceConfig__csi_RS_ResourceSetList__helper4.
Opaque CSI_ResourceConfig__csi_RS_ResourceSetList__cond CSI_ResourceConfig__csi_RS_ResourceSetList__Format.

Definition CSI_ResourceConfig__resourceType__Format : T_Format CSI_ResourceConfig__resourceType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ResourceConfig__resourceType__nat__Format CSI_ResourceConfig__resourceType__F1 CSI_ResourceConfig__resourceType__F2 CSI_ResourceConfig__resourceType__F1F2 CSI_ResourceConfig__resourceType__F2F1.

Opaque CSI_ResourceConfig__resourceType__cond CSI_ResourceConfig__resourceType__Format.


Definition CSI_ResourceConfig__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_ResourceConfig__ext0O__list.
Definition CSI_ResourceConfig__ext0O__Format_list : CSI_ResourceConfig__ext0O__Format_Type :=
  (CSI_SSB_ResourceSetId__Format, unit_format).
Definition CSI_ResourceConfig__ext0O__list__Format := (*Eval compute in *) seq_format CSI_ResourceConfig__ext0O__list CSI_ResourceConfig__ext0O__Format_list.
Definition CSI_ResourceConfig__ext0O__F1 z :=
  (CSI_ResourceConfig__ext0O__csi_SSB_ResourceSetListExt_r17 z, tt).
Definition CSI_ResourceConfig__ext0O__F2 (y : seq_type CSI_ResourceConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ResourceConfig__ext0O__Type i0
  end.
Lemma CSI_ResourceConfig__ext0O__F1F2_cond (z : CSI_ResourceConfig__ext0O__Type)
  : CSI_ResourceConfig__ext0O__cond z ->
  (seq_cond CSI_ResourceConfig__ext0O__list (CSI_ResourceConfig__ext0O__F1 z)).
intro H. unfold CSI_ResourceConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_ResourceConfig__ext0O__F1F2_cond2 (z : CSI_ResourceConfig__ext0O__Type)
 : CSI_ResourceConfig__ext0O__F2 (CSI_ResourceConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ResourceConfig__ext0O__F2F1_cond (y : seq_type CSI_ResourceConfig__ext0O__list)
  : seq_cond CSI_ResourceConfig__ext0O__list y ->
 (CSI_ResourceConfig__ext0O__cond (CSI_ResourceConfig__ext0O__F2 y)) /\  CSI_ResourceConfig__ext0O__F1 (CSI_ResourceConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ResourceConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_ResourceConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ResourceConfig__ext0O__Format : T_Format CSI_ResourceConfig__ext0O__Type CSI_ResourceConfig__ext0O__cond :=
        proj2_format  CSI_ResourceConfig__ext0O__cond CSI_ResourceConfig__ext0O__list__Format
    CSI_ResourceConfig__ext0O__F1 CSI_ResourceConfig__ext0O__F2 CSI_ResourceConfig__ext0O__F1F2_cond  CSI_ResourceConfig__ext0O__F1F2_cond2 CSI_ResourceConfig__ext0O__F2F1_cond.
Opaque CSI_ResourceConfig__ext0O__cond CSI_ResourceConfig__ext0O__Format.

Definition CSI_ResourceConfig__ext0__check_all_none (b : CSI_ResourceConfig__ext0O__Type) : bool :=
match b with 
  | make__CSI_ResourceConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_ResourceConfig__ext0__Format : T_Format CSI_ResourceConfig__ext0__Type CSI_ResourceConfig__ext0__cond :=
  restrict_add_format CSI_ResourceConfig__ext0__check_all_none CSI_ResourceConfig__ext0O__Format.

Opaque CSI_ResourceConfig__ext0__cond CSI_ResourceConfig__ext0__Format.


Definition CSI_ResourceConfig__root_Format_Type := Eval cbn in seq_format_prod CSI_ResourceConfig__root_list.
Definition CSI_ResourceConfig__root_Format_list : CSI_ResourceConfig__root_Format_Type :=
  (CSI_ResourceConfigId__Format, (CSI_ResourceConfig__csi_RS_ResourceSetList__Format, (BWP_Id__Format, (CSI_ResourceConfig__resourceType__Format, unit_format)))).

Definition CSI_ResourceConfig__ext_Format_Type := Eval cbn in get_formats CSI_ResourceConfig__ext_list.
Definition CSI_ResourceConfig__ext_Format_list : CSI_ResourceConfig__ext_Format_Type :=
  (CSI_ResourceConfig__ext0__Format, unit__Format).

Definition CSI_ResourceConfig__list_type : Set := (seq_type CSI_ResourceConfig__root_list) * (seq_ext_type CSI_ResourceConfig__ext_list).
Definition CSI_ResourceConfig__list_cond (z : CSI_ResourceConfig__list_type) : Prop :=
        (seq_cond CSI_ResourceConfig__root_list (fst z)) /\ (seq_ext_cond CSI_ResourceConfig__ext_list (snd z)).
Definition CSI_ResourceConfig__list_format : T_Format CSI_ResourceConfig__list_type CSI_ResourceConfig__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_ResourceConfig__root_list CSI_ResourceConfig__root_Format_list CSI_ResourceConfig__ext_list CSI_ResourceConfig__ext_Format_list.

Opaque CSI_ResourceConfig__list_format.
Definition CSI_ResourceConfig__F1 (z : CSI_ResourceConfig__Type) : CSI_ResourceConfig__list_type :=
  (((CSI_ResourceConfig__csi_ResourceConfigId z, (CSI_ResourceConfig__csi_RS_ResourceSetList z, (CSI_ResourceConfig__bwp_Id z, (CSI_ResourceConfig__resourceType z, tt))))), (
(CSI_ResourceConfig__ext0 z, tt))).
Definition CSI_ResourceConfig__F2 (y : CSI_ResourceConfig__list_type) : CSI_ResourceConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__CSI_ResourceConfig__Type j0 j1 j2 j3 i0
  end.
Definition CSI_ResourceConfig__helper1 : (forall a : CSI_ResourceConfig__Type, CSI_ResourceConfig__cond a -> CSI_ResourceConfig__list_cond (CSI_ResourceConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_ResourceConfig__helper2 : (forall a : CSI_ResourceConfig__Type, CSI_ResourceConfig__F2 (CSI_ResourceConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_ResourceConfig__helper3 : (forall b : CSI_ResourceConfig__list_type, CSI_ResourceConfig__list_cond b -> CSI_ResourceConfig__cond (CSI_ResourceConfig__F2 b) /\ CSI_ResourceConfig__F1 (CSI_ResourceConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_ResourceConfig__cond, CSI_ResourceConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_ResourceConfig__Format : T_Format CSI_ResourceConfig__Type CSI_ResourceConfig__cond :=
 proj2_format CSI_ResourceConfig__cond CSI_ResourceConfig__list_format  CSI_ResourceConfig__F1 CSI_ResourceConfig__F2 CSI_ResourceConfig__helper1 CSI_ResourceConfig__helper2 CSI_ResourceConfig__helper3.

Opaque CSI_ResourceConfig__cond CSI_ResourceConfig__Format.

