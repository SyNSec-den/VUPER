Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Inductive UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Type : Set :=
 | UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__supported
.
Definition UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__cond := (fun (_ : UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Type) => True).
Lemma UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__nat__helper.

Definition UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1 t :=
  match t with
  | UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__supported => 0
  end.
Definition UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F2 n :=
  match n with
  | 0 => UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__supported
  | _ => UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__supported
  end.
Lemma UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1F2 : forall x : UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Type, (UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1 x <= 0) /\ UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F2 (UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1 x) = x. imp_solve. Qed.
Lemma UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F2F1 : forall (y : nat) (H : y <= 0), UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1 (UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Type : Set :=
 | UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__one
 | UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__two
.
Definition UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__cond := (fun (_ : UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Type) => True).
Lemma UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__nat__helper.

Definition UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1 t :=
  match t with
  | UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__one => 0
  | UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__two => 1
  end.
Definition UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F2 n :=
  match n with
  | 0 => UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__one
  | 1 => UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__two
  | _ => UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__one
  end.
Lemma UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1F2 : forall x : UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Type, (UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1 x <= 1) /\ UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F2 (UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F2F1 : forall (y : nat) (H : y <= 1), UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1 (UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Definition UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Type := list FreqBandIndicatorNR__Type.

Lemma UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__cond (z : UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and FreqBandIndicatorNR__cond z) .

Record UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type : Set := make__UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type {}.
Definition UERadioPagingInformation_v1700_IEs__nonCriticalExtension__cond (z : UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type) := True.
Record UERadioPagingInformation_v1700_IEs__Type : Set :=
  make__UERadioPagingInformation_v1700_IEs__Type {
    UERadioPagingInformation_v1700_IEs__ue_RadioPagingInfo_r17 : option octet_string ;
    UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17 : option UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Type ;
    UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17 : option UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Type ;
    UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17 : option UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Type ;
    UERadioPagingInformation_v1700_IEs__nonCriticalExtension : option UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition UERadioPagingInformation_v1700_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Type UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__cond ::
 Opt UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Type UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__cond ::
 Opt UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Type UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__cond ::
 Opt UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type UERadioPagingInformation_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition UERadioPagingInformation_v1700_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UERadioPagingInformation_v1700_IEs__ue_RadioPagingInfo_r17 z) /\
  opt_cond UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__cond (UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17 z) /\
  opt_cond UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__cond (UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17 z) /\
  opt_cond UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__cond (UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17 z) /\
  opt_cond UERadioPagingInformation_v1700_IEs__nonCriticalExtension__cond (UERadioPagingInformation_v1700_IEs__nonCriticalExtension z) /\
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
Definition UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Format : T_Format UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__nat__Format UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1 UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F2 UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F1F2 UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__F2F1.

Opaque UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__cond UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Format.

Definition UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Format : T_Format UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__nat__Format UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1 UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F2 UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F1F2 UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__F2F1.

Opaque UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__cond UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Format.

Definition UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Format : T_Format UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Type UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__cond := seq_of_format FreqBandIndicatorNR__Format 1 maxBands UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__helper1 UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__helper2.

Opaque UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__cond UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Format.

Definition UERadioPagingInformation_v1700_IEs__nonCriticalExtension__helper : forall a : UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Format : T_Format UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type UERadioPagingInformation_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Type)
    UERadioPagingInformation_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UERadioPagingInformation_v1700_IEs__nonCriticalExtension__cond UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Format.


Definition UERadioPagingInformation_v1700_IEs__Format_Type := Eval cbn in seq_format_prod UERadioPagingInformation_v1700_IEs__list.
Definition UERadioPagingInformation_v1700_IEs__Format_list : UERadioPagingInformation_v1700_IEs__Format_Type :=
  (octet_string_nc__Format, (UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17__Format, (UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17__Format, (UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17__Format, (UERadioPagingInformation_v1700_IEs__nonCriticalExtension__Format, unit_format))))).
Definition UERadioPagingInformation_v1700_IEs__list__Format := (*Eval compute in *) seq_format UERadioPagingInformation_v1700_IEs__list UERadioPagingInformation_v1700_IEs__Format_list.
Definition UERadioPagingInformation_v1700_IEs__F1 z :=
  (UERadioPagingInformation_v1700_IEs__ue_RadioPagingInfo_r17 z, (UERadioPagingInformation_v1700_IEs__inactiveStatePO_Determination_r17 z, (UERadioPagingInformation_v1700_IEs__numberOfRxRedCap_r17 z, (UERadioPagingInformation_v1700_IEs__halfDuplexFDD_TypeA_RedCap_r17 z, (UERadioPagingInformation_v1700_IEs__nonCriticalExtension z, tt))))).
Definition UERadioPagingInformation_v1700_IEs__F2 (y : seq_type UERadioPagingInformation_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__UERadioPagingInformation_v1700_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma UERadioPagingInformation_v1700_IEs__F1F2_cond (z : UERadioPagingInformation_v1700_IEs__Type)
  : UERadioPagingInformation_v1700_IEs__cond z ->
  (seq_cond UERadioPagingInformation_v1700_IEs__list (UERadioPagingInformation_v1700_IEs__F1 z)).
intro H. unfold UERadioPagingInformation_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma UERadioPagingInformation_v1700_IEs__F1F2_cond2 (z : UERadioPagingInformation_v1700_IEs__Type)
 : UERadioPagingInformation_v1700_IEs__F2 (UERadioPagingInformation_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UERadioPagingInformation_v1700_IEs__F2F1_cond (y : seq_type UERadioPagingInformation_v1700_IEs__list)
  : seq_cond UERadioPagingInformation_v1700_IEs__list y ->
 (UERadioPagingInformation_v1700_IEs__cond (UERadioPagingInformation_v1700_IEs__F2 y)) /\  UERadioPagingInformation_v1700_IEs__F1 (UERadioPagingInformation_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UERadioPagingInformation_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold UERadioPagingInformation_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UERadioPagingInformation_v1700_IEs__Format : T_Format UERadioPagingInformation_v1700_IEs__Type UERadioPagingInformation_v1700_IEs__cond :=
        proj2_format  UERadioPagingInformation_v1700_IEs__cond UERadioPagingInformation_v1700_IEs__list__Format
    UERadioPagingInformation_v1700_IEs__F1 UERadioPagingInformation_v1700_IEs__F2 UERadioPagingInformation_v1700_IEs__F1F2_cond  UERadioPagingInformation_v1700_IEs__F1F2_cond2 UERadioPagingInformation_v1700_IEs__F2F1_cond.
Opaque UERadioPagingInformation_v1700_IEs__cond UERadioPagingInformation_v1700_IEs__Format.

