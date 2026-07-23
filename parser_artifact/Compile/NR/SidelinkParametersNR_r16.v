Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RLC_ParametersSidelink_r16.

Opaque RLC_ParametersSidelink_r16__cond RLC_ParametersSidelink_r16__Format.

Require Import NR.MAC_ParametersSidelink_r16.

Opaque MAC_ParametersSidelink_r16__cond MAC_ParametersSidelink_r16__Format.

Require Import NR.UE_SidelinkCapabilityAddXDD_Mode_r16.

Opaque UE_SidelinkCapabilityAddXDD_Mode_r16__cond UE_SidelinkCapabilityAddXDD_Mode_r16__Format.

Require Import NR.UE_SidelinkCapabilityAddXDD_Mode_r16.

Opaque UE_SidelinkCapabilityAddXDD_Mode_r16__cond UE_SidelinkCapabilityAddXDD_Mode_r16__Format.

Require Import NR.BandSidelink_r16.

Opaque BandSidelink_r16__cond BandSidelink_r16__Format.

Definition SidelinkParametersNR_r16__supportedBandListSidelink_r16__Type := list BandSidelink_r16__Type.

Lemma SidelinkParametersNR_r16__supportedBandListSidelink_r16__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma SidelinkParametersNR_r16__supportedBandListSidelink_r16__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkParametersNR_r16__supportedBandListSidelink_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkParametersNR_r16__supportedBandListSidelink_r16__cond (z : SidelinkParametersNR_r16__supportedBandListSidelink_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and BandSidelink_r16__cond z) .

Require Import NR.RelayParameters_r17.

Opaque RelayParameters_r17__cond RelayParameters_r17__Format.

Record SidelinkParametersNR_r16__ext0O__Type : Set :=
  make__SidelinkParametersNR_r16__ext0O__Type {
    SidelinkParametersNR_r16__ext0O__relayParameters_r17 : option RelayParameters_r17__Type ;
}.
Definition SidelinkParametersNR_r16__ext0O__list := (
 Opt RelayParameters_r17__Type RelayParameters_r17__cond ::
 nil).
Definition SidelinkParametersNR_r16__ext0O__cond z := 
  opt_cond RelayParameters_r17__cond (SidelinkParametersNR_r16__ext0O__relayParameters_r17 z) /\
  True.

Definition SidelinkParametersNR_r16__ext0__Type := SidelinkParametersNR_r16__ext0O__Type.
Definition SidelinkParametersNR_r16__ext0__cond := SidelinkParametersNR_r16__ext0O__cond.

Inductive SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Type : Set :=
 | SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__supported
.
Definition SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__cond := (fun (_ : SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Type) => True).
Lemma SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__nat__helper.

Definition SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1 t :=
  match t with
  | SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__supported => 0
  end.
Definition SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F2 n :=
  match n with
  | 0 => SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__supported
  | _ => SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__supported
  end.
Lemma SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1F2 : forall x : SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Type, (SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1 x <= 0) /\ SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F2 (SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1 x) = x. imp_solve. Qed.
Lemma SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F2F1 : forall (y : nat) (H : y <= 0), SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1 (SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F2 y) = y. enum_solve H y. Qed.

Record SidelinkParametersNR_r16__ext1O__Type : Set :=
  make__SidelinkParametersNR_r16__ext1O__Type {
    SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17 : option SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Type ;
}.
Definition SidelinkParametersNR_r16__ext1O__list := (
 Opt SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Type SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__cond ::
 nil).
Definition SidelinkParametersNR_r16__ext1O__cond z := 
  opt_cond SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__cond (SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17 z) /\
  True.

Definition SidelinkParametersNR_r16__ext1__Type := SidelinkParametersNR_r16__ext1O__Type.
Definition SidelinkParametersNR_r16__ext1__cond := SidelinkParametersNR_r16__ext1O__cond.

Record SidelinkParametersNR_r16__Type : Set :=
  make__SidelinkParametersNR_r16__Type {
    SidelinkParametersNR_r16__rlc_ParametersSidelink_r16 : option RLC_ParametersSidelink_r16__Type ;
    SidelinkParametersNR_r16__mac_ParametersSidelink_r16 : option MAC_ParametersSidelink_r16__Type ;
    SidelinkParametersNR_r16__fdd_Add_UE_Sidelink_Capabilities_r16 : option UE_SidelinkCapabilityAddXDD_Mode_r16__Type ;
    SidelinkParametersNR_r16__tdd_Add_UE_Sidelink_Capabilities_r16 : option UE_SidelinkCapabilityAddXDD_Mode_r16__Type ;
    SidelinkParametersNR_r16__supportedBandListSidelink_r16 : option SidelinkParametersNR_r16__supportedBandListSidelink_r16__Type ;
    SidelinkParametersNR_r16__ext0 : option SidelinkParametersNR_r16__ext0__Type ;
    SidelinkParametersNR_r16__ext1 : option SidelinkParametersNR_r16__ext1__Type ;
}.
Definition SidelinkParametersNR_r16__root_list : list seq_elem := (
 Opt RLC_ParametersSidelink_r16__Type RLC_ParametersSidelink_r16__cond ::
 Opt MAC_ParametersSidelink_r16__Type MAC_ParametersSidelink_r16__cond ::
 Opt UE_SidelinkCapabilityAddXDD_Mode_r16__Type UE_SidelinkCapabilityAddXDD_Mode_r16__cond ::
 Opt UE_SidelinkCapabilityAddXDD_Mode_r16__Type UE_SidelinkCapabilityAddXDD_Mode_r16__cond ::
 Opt SidelinkParametersNR_r16__supportedBandListSidelink_r16__Type SidelinkParametersNR_r16__supportedBandListSidelink_r16__cond ::
 nil).
Definition SidelinkParametersNR_r16__ext_list : list typ := (
  typ_cons SidelinkParametersNR_r16__ext0__Type SidelinkParametersNR_r16__ext0__cond ::
  typ_cons SidelinkParametersNR_r16__ext1__Type SidelinkParametersNR_r16__ext1__cond ::
  nil).
Definition SidelinkParametersNR_r16__cond (z : SidelinkParametersNR_r16__Type) := 
(  opt_cond RLC_ParametersSidelink_r16__cond (SidelinkParametersNR_r16__rlc_ParametersSidelink_r16 z) /\
  opt_cond MAC_ParametersSidelink_r16__cond (SidelinkParametersNR_r16__mac_ParametersSidelink_r16 z) /\
  opt_cond UE_SidelinkCapabilityAddXDD_Mode_r16__cond (SidelinkParametersNR_r16__fdd_Add_UE_Sidelink_Capabilities_r16 z) /\
  opt_cond UE_SidelinkCapabilityAddXDD_Mode_r16__cond (SidelinkParametersNR_r16__tdd_Add_UE_Sidelink_Capabilities_r16 z) /\
  opt_cond SidelinkParametersNR_r16__supportedBandListSidelink_r16__cond (SidelinkParametersNR_r16__supportedBandListSidelink_r16 z) /\
  True) /\ 
(  opt_cond SidelinkParametersNR_r16__ext0__cond (SidelinkParametersNR_r16__ext0 z) /\
  opt_cond SidelinkParametersNR_r16__ext1__cond (SidelinkParametersNR_r16__ext1 z) /\
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
Definition SidelinkParametersNR_r16__supportedBandListSidelink_r16__Format : T_Format SidelinkParametersNR_r16__supportedBandListSidelink_r16__Type SidelinkParametersNR_r16__supportedBandListSidelink_r16__cond := seq_of_format BandSidelink_r16__Format 1 maxBands SidelinkParametersNR_r16__supportedBandListSidelink_r16__helper1 SidelinkParametersNR_r16__supportedBandListSidelink_r16__helper2.

Opaque SidelinkParametersNR_r16__supportedBandListSidelink_r16__cond SidelinkParametersNR_r16__supportedBandListSidelink_r16__Format.


Definition SidelinkParametersNR_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SidelinkParametersNR_r16__ext0O__list.
Definition SidelinkParametersNR_r16__ext0O__Format_list : SidelinkParametersNR_r16__ext0O__Format_Type :=
  (RelayParameters_r17__Format, unit_format).
Definition SidelinkParametersNR_r16__ext0O__list__Format := (*Eval compute in *) seq_format SidelinkParametersNR_r16__ext0O__list SidelinkParametersNR_r16__ext0O__Format_list.
Definition SidelinkParametersNR_r16__ext0O__F1 z :=
  (SidelinkParametersNR_r16__ext0O__relayParameters_r17 z, tt).
Definition SidelinkParametersNR_r16__ext0O__F2 (y : seq_type SidelinkParametersNR_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SidelinkParametersNR_r16__ext0O__Type i0
  end.
Lemma SidelinkParametersNR_r16__ext0O__F1F2_cond (z : SidelinkParametersNR_r16__ext0O__Type)
  : SidelinkParametersNR_r16__ext0O__cond z ->
  (seq_cond SidelinkParametersNR_r16__ext0O__list (SidelinkParametersNR_r16__ext0O__F1 z)).
intro H. unfold SidelinkParametersNR_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SidelinkParametersNR_r16__ext0O__F1F2_cond2 (z : SidelinkParametersNR_r16__ext0O__Type)
 : SidelinkParametersNR_r16__ext0O__F2 (SidelinkParametersNR_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SidelinkParametersNR_r16__ext0O__F2F1_cond (y : seq_type SidelinkParametersNR_r16__ext0O__list)
  : seq_cond SidelinkParametersNR_r16__ext0O__list y ->
 (SidelinkParametersNR_r16__ext0O__cond (SidelinkParametersNR_r16__ext0O__F2 y)) /\  SidelinkParametersNR_r16__ext0O__F1 (SidelinkParametersNR_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SidelinkParametersNR_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SidelinkParametersNR_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SidelinkParametersNR_r16__ext0O__Format : T_Format SidelinkParametersNR_r16__ext0O__Type SidelinkParametersNR_r16__ext0O__cond :=
        proj2_format  SidelinkParametersNR_r16__ext0O__cond SidelinkParametersNR_r16__ext0O__list__Format
    SidelinkParametersNR_r16__ext0O__F1 SidelinkParametersNR_r16__ext0O__F2 SidelinkParametersNR_r16__ext0O__F1F2_cond  SidelinkParametersNR_r16__ext0O__F1F2_cond2 SidelinkParametersNR_r16__ext0O__F2F1_cond.
Opaque SidelinkParametersNR_r16__ext0O__cond SidelinkParametersNR_r16__ext0O__Format.

Definition SidelinkParametersNR_r16__ext0__check_all_none (b : SidelinkParametersNR_r16__ext0O__Type) : bool :=
match b with 
  | make__SidelinkParametersNR_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SidelinkParametersNR_r16__ext0__Format : T_Format SidelinkParametersNR_r16__ext0__Type SidelinkParametersNR_r16__ext0__cond :=
  restrict_add_format SidelinkParametersNR_r16__ext0__check_all_none SidelinkParametersNR_r16__ext0O__Format.

Opaque SidelinkParametersNR_r16__ext0__cond SidelinkParametersNR_r16__ext0__Format.

Definition SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Format : T_Format SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__nat__Format SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1 SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F2 SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F1F2 SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__F2F1.

Opaque SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__cond SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Format.


Definition SidelinkParametersNR_r16__ext1O__Format_Type := Eval cbn in seq_format_prod SidelinkParametersNR_r16__ext1O__list.
Definition SidelinkParametersNR_r16__ext1O__Format_list : SidelinkParametersNR_r16__ext1O__Format_Type :=
  (SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17__Format, unit_format).
Definition SidelinkParametersNR_r16__ext1O__list__Format := (*Eval compute in *) seq_format SidelinkParametersNR_r16__ext1O__list SidelinkParametersNR_r16__ext1O__Format_list.
Definition SidelinkParametersNR_r16__ext1O__F1 z :=
  (SidelinkParametersNR_r16__ext1O__p0_OLPC_Sidelink_r17 z, tt).
Definition SidelinkParametersNR_r16__ext1O__F2 (y : seq_type SidelinkParametersNR_r16__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__SidelinkParametersNR_r16__ext1O__Type i0
  end.
Lemma SidelinkParametersNR_r16__ext1O__F1F2_cond (z : SidelinkParametersNR_r16__ext1O__Type)
  : SidelinkParametersNR_r16__ext1O__cond z ->
  (seq_cond SidelinkParametersNR_r16__ext1O__list (SidelinkParametersNR_r16__ext1O__F1 z)).
intro H. unfold SidelinkParametersNR_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma SidelinkParametersNR_r16__ext1O__F1F2_cond2 (z : SidelinkParametersNR_r16__ext1O__Type)
 : SidelinkParametersNR_r16__ext1O__F2 (SidelinkParametersNR_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SidelinkParametersNR_r16__ext1O__F2F1_cond (y : seq_type SidelinkParametersNR_r16__ext1O__list)
  : seq_cond SidelinkParametersNR_r16__ext1O__list y ->
 (SidelinkParametersNR_r16__ext1O__cond (SidelinkParametersNR_r16__ext1O__F2 y)) /\  SidelinkParametersNR_r16__ext1O__F1 (SidelinkParametersNR_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SidelinkParametersNR_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold SidelinkParametersNR_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SidelinkParametersNR_r16__ext1O__Format : T_Format SidelinkParametersNR_r16__ext1O__Type SidelinkParametersNR_r16__ext1O__cond :=
        proj2_format  SidelinkParametersNR_r16__ext1O__cond SidelinkParametersNR_r16__ext1O__list__Format
    SidelinkParametersNR_r16__ext1O__F1 SidelinkParametersNR_r16__ext1O__F2 SidelinkParametersNR_r16__ext1O__F1F2_cond  SidelinkParametersNR_r16__ext1O__F1F2_cond2 SidelinkParametersNR_r16__ext1O__F2F1_cond.
Opaque SidelinkParametersNR_r16__ext1O__cond SidelinkParametersNR_r16__ext1O__Format.

Definition SidelinkParametersNR_r16__ext1__check_all_none (b : SidelinkParametersNR_r16__ext1O__Type) : bool :=
match b with 
  | make__SidelinkParametersNR_r16__ext1O__Type None  => false 
  | _ => true 
 end.
Definition SidelinkParametersNR_r16__ext1__Format : T_Format SidelinkParametersNR_r16__ext1__Type SidelinkParametersNR_r16__ext1__cond :=
  restrict_add_format SidelinkParametersNR_r16__ext1__check_all_none SidelinkParametersNR_r16__ext1O__Format.

Opaque SidelinkParametersNR_r16__ext1__cond SidelinkParametersNR_r16__ext1__Format.


Definition SidelinkParametersNR_r16__root_Format_Type := Eval cbn in seq_format_prod SidelinkParametersNR_r16__root_list.
Definition SidelinkParametersNR_r16__root_Format_list : SidelinkParametersNR_r16__root_Format_Type :=
  (RLC_ParametersSidelink_r16__Format, (MAC_ParametersSidelink_r16__Format, (UE_SidelinkCapabilityAddXDD_Mode_r16__Format, (UE_SidelinkCapabilityAddXDD_Mode_r16__Format, (SidelinkParametersNR_r16__supportedBandListSidelink_r16__Format, unit_format))))).

Definition SidelinkParametersNR_r16__ext_Format_Type := Eval cbn in get_formats SidelinkParametersNR_r16__ext_list.
Definition SidelinkParametersNR_r16__ext_Format_list : SidelinkParametersNR_r16__ext_Format_Type :=
  (SidelinkParametersNR_r16__ext0__Format, (SidelinkParametersNR_r16__ext1__Format, unit__Format)).

Definition SidelinkParametersNR_r16__list_type : Set := (seq_type SidelinkParametersNR_r16__root_list) * (seq_ext_type SidelinkParametersNR_r16__ext_list).
Definition SidelinkParametersNR_r16__list_cond (z : SidelinkParametersNR_r16__list_type) : Prop :=
        (seq_cond SidelinkParametersNR_r16__root_list (fst z)) /\ (seq_ext_cond SidelinkParametersNR_r16__ext_list (snd z)).
Definition SidelinkParametersNR_r16__list_format : T_Format SidelinkParametersNR_r16__list_type SidelinkParametersNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SidelinkParametersNR_r16__root_list SidelinkParametersNR_r16__root_Format_list SidelinkParametersNR_r16__ext_list SidelinkParametersNR_r16__ext_Format_list.

Opaque SidelinkParametersNR_r16__list_format.
Definition SidelinkParametersNR_r16__F1 (z : SidelinkParametersNR_r16__Type) : SidelinkParametersNR_r16__list_type :=
  (((SidelinkParametersNR_r16__rlc_ParametersSidelink_r16 z, (SidelinkParametersNR_r16__mac_ParametersSidelink_r16 z, (SidelinkParametersNR_r16__fdd_Add_UE_Sidelink_Capabilities_r16 z, (SidelinkParametersNR_r16__tdd_Add_UE_Sidelink_Capabilities_r16 z, (SidelinkParametersNR_r16__supportedBandListSidelink_r16 z, tt)))))), (
(SidelinkParametersNR_r16__ext0 z, (SidelinkParametersNR_r16__ext1 z, tt)))).
Definition SidelinkParametersNR_r16__F2 (y : SidelinkParametersNR_r16__list_type) : SidelinkParametersNR_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, _)))=>
    make__SidelinkParametersNR_r16__Type j0 j1 j2 j3 j4 i0 i1
  end.
Definition SidelinkParametersNR_r16__helper1 : (forall a : SidelinkParametersNR_r16__Type, SidelinkParametersNR_r16__cond a -> SidelinkParametersNR_r16__list_cond (SidelinkParametersNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SidelinkParametersNR_r16__helper2 : (forall a : SidelinkParametersNR_r16__Type, SidelinkParametersNR_r16__F2 (SidelinkParametersNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SidelinkParametersNR_r16__helper3 : (forall b : SidelinkParametersNR_r16__list_type, SidelinkParametersNR_r16__list_cond b -> SidelinkParametersNR_r16__cond (SidelinkParametersNR_r16__F2 b) /\ SidelinkParametersNR_r16__F1 (SidelinkParametersNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SidelinkParametersNR_r16__cond, SidelinkParametersNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SidelinkParametersNR_r16__Format : T_Format SidelinkParametersNR_r16__Type SidelinkParametersNR_r16__cond :=
 proj2_format SidelinkParametersNR_r16__cond SidelinkParametersNR_r16__list_format  SidelinkParametersNR_r16__F1 SidelinkParametersNR_r16__F2 SidelinkParametersNR_r16__helper1 SidelinkParametersNR_r16__helper2 SidelinkParametersNR_r16__helper3.

Opaque SidelinkParametersNR_r16__cond SidelinkParametersNR_r16__Format.

