Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.AppLayerBufferLevel_r17.

Opaque AppLayerBufferLevel_r17__cond AppLayerBufferLevel_r17__Format.

Definition RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type := list AppLayerBufferLevel_r17__Type.

Lemma RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__cond (z : RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and AppLayerBufferLevel_r17__cond z) .

Lemma RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__helper1 : (0 <= 30000)%Z.  lia. Qed.
Lemma RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__helper2 : to_bit_sz (Z.to_nat (30000 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (30000 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__Type := Z.
Definition RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__cond := (fun z => (0 <= z <= 30000)%Z).
Require Import NR.PDU_SessionID.

Opaque PDU_SessionID__cond PDU_SessionID__Format.

Definition RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type := list PDU_SessionID__Type.

Lemma RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__helper1 : (0 <= 1 <= maxNrofPDU_Sessions_r17)%Z. unfold maxNrofPDU_Sessions_r17.
 lia. Qed.
Lemma RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPDU_Sessions_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPDU_Sessions_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__cond (z : RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPDU_Sessions_r17)%Z /\ (list_and PDU_SessionID__cond z) .

Record RAN_VisibleMeasurements_r17__Type : Set :=
  make__RAN_VisibleMeasurements_r17__Type {
    RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17 : option RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type ;
    RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17 : option Z ;
    RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17 : option RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type ;
}.
Definition RAN_VisibleMeasurements_r17__root_list : list seq_elem := (
 Opt RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__cond ::
 Opt Z RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__cond ::
 Opt RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__cond ::
 nil).
Definition RAN_VisibleMeasurements_r17__ext_list : list typ := (
  nil).
Definition RAN_VisibleMeasurements_r17__cond (z : RAN_VisibleMeasurements_r17__Type) := 
(  opt_cond RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__cond (RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17 z) /\
  opt_cond RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__cond (RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17 z) /\
  opt_cond RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__cond (RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17 z) /\
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
Definition RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Format : T_Format RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__cond := seq_of_format AppLayerBufferLevel_r17__Format 1 8 RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__helper1 RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__helper2.

Opaque RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__cond RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Format.

Definition RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__Format : T_Format Z RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__cond :=
 ranged_int_format (0) (30000) RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__helper1 RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__helper2.

Opaque RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__cond RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__Format.

Definition RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Format : T_Format RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__cond := seq_of_format PDU_SessionID__Format 1 maxNrofPDU_Sessions_r17 RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__helper1 RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__helper2.

Opaque RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__cond RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Format.


Definition RAN_VisibleMeasurements_r17__root_Format_Type := Eval cbn in seq_format_prod RAN_VisibleMeasurements_r17__root_list.
Definition RAN_VisibleMeasurements_r17__root_Format_list : RAN_VisibleMeasurements_r17__root_Format_Type :=
  (RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Format, (RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__Format, (RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Format, unit_format))).

Definition RAN_VisibleMeasurements_r17__ext_Format_Type := Eval cbn in get_formats RAN_VisibleMeasurements_r17__ext_list.
Definition RAN_VisibleMeasurements_r17__ext_Format_list : RAN_VisibleMeasurements_r17__ext_Format_Type :=
  unit__Format.

Definition RAN_VisibleMeasurements_r17__list_type : Set := (seq_type RAN_VisibleMeasurements_r17__root_list) * (seq_ext_type RAN_VisibleMeasurements_r17__ext_list).
Definition RAN_VisibleMeasurements_r17__list_cond (z : RAN_VisibleMeasurements_r17__list_type) : Prop :=
        (seq_cond RAN_VisibleMeasurements_r17__root_list (fst z)) /\ (seq_ext_cond RAN_VisibleMeasurements_r17__ext_list (snd z)).
Definition RAN_VisibleMeasurements_r17__list_format : T_Format RAN_VisibleMeasurements_r17__list_type RAN_VisibleMeasurements_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RAN_VisibleMeasurements_r17__root_list RAN_VisibleMeasurements_r17__root_Format_list RAN_VisibleMeasurements_r17__ext_list RAN_VisibleMeasurements_r17__ext_Format_list.

Opaque RAN_VisibleMeasurements_r17__list_format.
Definition RAN_VisibleMeasurements_r17__F1 (z : RAN_VisibleMeasurements_r17__Type) : RAN_VisibleMeasurements_r17__list_type :=
  (((RAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17 z, (RAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17 z, (RAN_VisibleMeasurements_r17__pdu_SessionIdList_r17 z, tt)))), (
tt)).
Definition RAN_VisibleMeasurements_r17__F2 (y : RAN_VisibleMeasurements_r17__list_type) : RAN_VisibleMeasurements_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__RAN_VisibleMeasurements_r17__Type j0 j1 j2
  end.
Definition RAN_VisibleMeasurements_r17__helper1 : (forall a : RAN_VisibleMeasurements_r17__Type, RAN_VisibleMeasurements_r17__cond a -> RAN_VisibleMeasurements_r17__list_cond (RAN_VisibleMeasurements_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RAN_VisibleMeasurements_r17__helper2 : (forall a : RAN_VisibleMeasurements_r17__Type, RAN_VisibleMeasurements_r17__F2 (RAN_VisibleMeasurements_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RAN_VisibleMeasurements_r17__helper3 : (forall b : RAN_VisibleMeasurements_r17__list_type, RAN_VisibleMeasurements_r17__list_cond b -> RAN_VisibleMeasurements_r17__cond (RAN_VisibleMeasurements_r17__F2 b) /\ RAN_VisibleMeasurements_r17__F1 (RAN_VisibleMeasurements_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RAN_VisibleMeasurements_r17__cond, RAN_VisibleMeasurements_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RAN_VisibleMeasurements_r17__Format : T_Format RAN_VisibleMeasurements_r17__Type RAN_VisibleMeasurements_r17__cond :=
 proj2_format RAN_VisibleMeasurements_r17__cond RAN_VisibleMeasurements_r17__list_format  RAN_VisibleMeasurements_r17__F1 RAN_VisibleMeasurements_r17__F2 RAN_VisibleMeasurements_r17__helper1 RAN_VisibleMeasurements_r17__helper2 RAN_VisibleMeasurements_r17__helper3.

Opaque RAN_VisibleMeasurements_r17__cond RAN_VisibleMeasurements_r17__Format.

