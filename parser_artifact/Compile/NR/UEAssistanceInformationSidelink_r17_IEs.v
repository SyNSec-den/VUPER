Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SL_DRX_ConfigUC_SemiStatic_r17.

Opaque SL_DRX_ConfigUC_SemiStatic_r17__cond SL_DRX_ConfigUC_SemiStatic_r17__Format.

Definition UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Type := list SL_DRX_ConfigUC_SemiStatic_r17__Type.

Lemma UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__helper1 : (0 <= 1 <= maxNrofSL_RxInfoSet_r17)%Z. unfold maxNrofSL_RxInfoSet_r17.
 lia. Qed.
Lemma UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_RxInfoSet_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_RxInfoSet_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__cond (z : UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_RxInfoSet_r17)%Z /\ (list_and SL_DRX_ConfigUC_SemiStatic_r17__cond z) .

Record UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type : Set := make__UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type {}.
Definition UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__cond (z : UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type) := True.
Record UEAssistanceInformationSidelink_r17_IEs__Type : Set :=
  make__UEAssistanceInformationSidelink_r17_IEs__Type {
    UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17 : option UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Type ;
    UEAssistanceInformationSidelink_r17_IEs__lateNonCriticalExtension : option octet_string ;
    UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension : option UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type ;
}.
Definition UEAssistanceInformationSidelink_r17_IEs__list := (
 Opt UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Type UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__cond ::
 nil).
Definition UEAssistanceInformationSidelink_r17_IEs__cond z := 
  opt_cond UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__cond (UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UEAssistanceInformationSidelink_r17_IEs__lateNonCriticalExtension z) /\
  opt_cond UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__cond (UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension z) /\
  True.


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
Definition UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Format : T_Format UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Type UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__cond := seq_of_format SL_DRX_ConfigUC_SemiStatic_r17__Format 1 maxNrofSL_RxInfoSet_r17 UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__helper1 UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__helper2.

Opaque UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__cond UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Format.

Definition UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__helper : forall a : UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type, True -> True /\ make__UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Format : T_Format UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Type)
    UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__cond UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Format.


Definition UEAssistanceInformationSidelink_r17_IEs__Format_Type := Eval cbn in seq_format_prod UEAssistanceInformationSidelink_r17_IEs__list.
Definition UEAssistanceInformationSidelink_r17_IEs__Format_list : UEAssistanceInformationSidelink_r17_IEs__Format_Type :=
  (UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17__Format, (octet_string_nc__Format, (UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension__Format, unit_format))).
Definition UEAssistanceInformationSidelink_r17_IEs__list__Format := (*Eval compute in *) seq_format UEAssistanceInformationSidelink_r17_IEs__list UEAssistanceInformationSidelink_r17_IEs__Format_list.
Definition UEAssistanceInformationSidelink_r17_IEs__F1 z :=
  (UEAssistanceInformationSidelink_r17_IEs__sl_PreferredDRX_ConfigList_r17 z, (UEAssistanceInformationSidelink_r17_IEs__lateNonCriticalExtension z, (UEAssistanceInformationSidelink_r17_IEs__nonCriticalExtension z, tt))).
Definition UEAssistanceInformationSidelink_r17_IEs__F2 (y : seq_type UEAssistanceInformationSidelink_r17_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UEAssistanceInformationSidelink_r17_IEs__Type i0 i1 i2
  end.
Lemma UEAssistanceInformationSidelink_r17_IEs__F1F2_cond (z : UEAssistanceInformationSidelink_r17_IEs__Type)
  : UEAssistanceInformationSidelink_r17_IEs__cond z ->
  (seq_cond UEAssistanceInformationSidelink_r17_IEs__list (UEAssistanceInformationSidelink_r17_IEs__F1 z)).
intro H. unfold UEAssistanceInformationSidelink_r17_IEs__cond in H. simpl. auto. Qed.
Lemma UEAssistanceInformationSidelink_r17_IEs__F1F2_cond2 (z : UEAssistanceInformationSidelink_r17_IEs__Type)
 : UEAssistanceInformationSidelink_r17_IEs__F2 (UEAssistanceInformationSidelink_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEAssistanceInformationSidelink_r17_IEs__F2F1_cond (y : seq_type UEAssistanceInformationSidelink_r17_IEs__list)
  : seq_cond UEAssistanceInformationSidelink_r17_IEs__list y ->
 (UEAssistanceInformationSidelink_r17_IEs__cond (UEAssistanceInformationSidelink_r17_IEs__F2 y)) /\  UEAssistanceInformationSidelink_r17_IEs__F1 (UEAssistanceInformationSidelink_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEAssistanceInformationSidelink_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold UEAssistanceInformationSidelink_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEAssistanceInformationSidelink_r17_IEs__Format : T_Format UEAssistanceInformationSidelink_r17_IEs__Type UEAssistanceInformationSidelink_r17_IEs__cond :=
        proj2_format  UEAssistanceInformationSidelink_r17_IEs__cond UEAssistanceInformationSidelink_r17_IEs__list__Format
    UEAssistanceInformationSidelink_r17_IEs__F1 UEAssistanceInformationSidelink_r17_IEs__F2 UEAssistanceInformationSidelink_r17_IEs__F1F2_cond  UEAssistanceInformationSidelink_r17_IEs__F1F2_cond2 UEAssistanceInformationSidelink_r17_IEs__F2F1_cond.
Opaque UEAssistanceInformationSidelink_r17_IEs__cond UEAssistanceInformationSidelink_r17_IEs__Format.

