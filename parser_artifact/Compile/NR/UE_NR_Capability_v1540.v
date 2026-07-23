Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SDAP_Parameters.

Opaque SDAP_Parameters__cond SDAP_Parameters__Format.

Inductive UE_NR_Capability_v1540__overheatingInd__Type : Set :=
 | UE_NR_Capability_v1540__overheatingInd__supported
.
Definition UE_NR_Capability_v1540__overheatingInd__cond := (fun (_ : UE_NR_Capability_v1540__overheatingInd__Type) => True).
Lemma UE_NR_Capability_v1540__overheatingInd__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1540__overheatingInd__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1540__overheatingInd__nat__helper.

Definition UE_NR_Capability_v1540__overheatingInd__F1 t :=
  match t with
  | UE_NR_Capability_v1540__overheatingInd__supported => 0
  end.
Definition UE_NR_Capability_v1540__overheatingInd__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1540__overheatingInd__supported
  | _ => UE_NR_Capability_v1540__overheatingInd__supported
  end.
Lemma UE_NR_Capability_v1540__overheatingInd__F1F2 : forall x : UE_NR_Capability_v1540__overheatingInd__Type, (UE_NR_Capability_v1540__overheatingInd__F1 x <= 0) /\ UE_NR_Capability_v1540__overheatingInd__F2 (UE_NR_Capability_v1540__overheatingInd__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1540__overheatingInd__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1540__overheatingInd__F1 (UE_NR_Capability_v1540__overheatingInd__F2 y) = y. enum_solve H y. Qed.

Require Import NR.IMS_Parameters.

Opaque IMS_Parameters__cond IMS_Parameters__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode_v1540.

Opaque UE_NR_CapabilityAddFRX_Mode_v1540__cond UE_NR_CapabilityAddFRX_Mode_v1540__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode_v1540.

Opaque UE_NR_CapabilityAddFRX_Mode_v1540__cond UE_NR_CapabilityAddFRX_Mode_v1540__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode.

Opaque UE_NR_CapabilityAddFRX_Mode__cond UE_NR_CapabilityAddFRX_Mode__Format.

Require Import NR.UE_NR_Capability_v1550.

Opaque UE_NR_Capability_v1550__cond UE_NR_Capability_v1550__Format.

Record UE_NR_Capability_v1540__Type : Set :=
  make__UE_NR_Capability_v1540__Type {
    UE_NR_Capability_v1540__sdap_Parameters : option SDAP_Parameters__Type ;
    UE_NR_Capability_v1540__overheatingInd : option UE_NR_Capability_v1540__overheatingInd__Type ;
    UE_NR_Capability_v1540__ims_Parameters : option IMS_Parameters__Type ;
    UE_NR_Capability_v1540__fr1_Add_UE_NR_Capabilities_v1540 : option UE_NR_CapabilityAddFRX_Mode_v1540__Type ;
    UE_NR_Capability_v1540__fr2_Add_UE_NR_Capabilities_v1540 : option UE_NR_CapabilityAddFRX_Mode_v1540__Type ;
    UE_NR_Capability_v1540__fr1_fr2_Add_UE_NR_Capabilities : option UE_NR_CapabilityAddFRX_Mode__Type ;
    UE_NR_Capability_v1540__nonCriticalExtension : option UE_NR_Capability_v1550__Type ;
}.
Definition UE_NR_Capability_v1540__list := (
 Opt SDAP_Parameters__Type SDAP_Parameters__cond ::
 Opt UE_NR_Capability_v1540__overheatingInd__Type UE_NR_Capability_v1540__overheatingInd__cond ::
 Opt IMS_Parameters__Type IMS_Parameters__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode_v1540__Type UE_NR_CapabilityAddFRX_Mode_v1540__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode_v1540__Type UE_NR_CapabilityAddFRX_Mode_v1540__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode__Type UE_NR_CapabilityAddFRX_Mode__cond ::
 Opt UE_NR_Capability_v1550__Type UE_NR_Capability_v1550__cond ::
 nil).
Definition UE_NR_Capability_v1540__cond z := 
  opt_cond SDAP_Parameters__cond (UE_NR_Capability_v1540__sdap_Parameters z) /\
  opt_cond UE_NR_Capability_v1540__overheatingInd__cond (UE_NR_Capability_v1540__overheatingInd z) /\
  opt_cond IMS_Parameters__cond (UE_NR_Capability_v1540__ims_Parameters z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode_v1540__cond (UE_NR_Capability_v1540__fr1_Add_UE_NR_Capabilities_v1540 z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode_v1540__cond (UE_NR_Capability_v1540__fr2_Add_UE_NR_Capabilities_v1540 z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode__cond (UE_NR_Capability_v1540__fr1_fr2_Add_UE_NR_Capabilities z) /\
  opt_cond UE_NR_Capability_v1550__cond (UE_NR_Capability_v1540__nonCriticalExtension z) /\
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
Definition UE_NR_Capability_v1540__overheatingInd__Format : T_Format UE_NR_Capability_v1540__overheatingInd__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1540__overheatingInd__nat__Format UE_NR_Capability_v1540__overheatingInd__F1 UE_NR_Capability_v1540__overheatingInd__F2 UE_NR_Capability_v1540__overheatingInd__F1F2 UE_NR_Capability_v1540__overheatingInd__F2F1.

Opaque UE_NR_Capability_v1540__overheatingInd__cond UE_NR_Capability_v1540__overheatingInd__Format.


Definition UE_NR_Capability_v1540__Format_Type := Eval cbn in seq_format_prod UE_NR_Capability_v1540__list.
Definition UE_NR_Capability_v1540__Format_list : UE_NR_Capability_v1540__Format_Type :=
  (SDAP_Parameters__Format, (UE_NR_Capability_v1540__overheatingInd__Format, (IMS_Parameters__Format, (UE_NR_CapabilityAddFRX_Mode_v1540__Format, (UE_NR_CapabilityAddFRX_Mode_v1540__Format, (UE_NR_CapabilityAddFRX_Mode__Format, (UE_NR_Capability_v1550__Format, unit_format))))))).
Definition UE_NR_Capability_v1540__list__Format := (*Eval compute in *) seq_format UE_NR_Capability_v1540__list UE_NR_Capability_v1540__Format_list.
Definition UE_NR_Capability_v1540__F1 z :=
  (UE_NR_Capability_v1540__sdap_Parameters z, (UE_NR_Capability_v1540__overheatingInd z, (UE_NR_Capability_v1540__ims_Parameters z, (UE_NR_Capability_v1540__fr1_Add_UE_NR_Capabilities_v1540 z, (UE_NR_Capability_v1540__fr2_Add_UE_NR_Capabilities_v1540 z, (UE_NR_Capability_v1540__fr1_fr2_Add_UE_NR_Capabilities z, (UE_NR_Capability_v1540__nonCriticalExtension z, tt))))))).
Definition UE_NR_Capability_v1540__F2 (y : seq_type UE_NR_Capability_v1540__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__UE_NR_Capability_v1540__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma UE_NR_Capability_v1540__F1F2_cond (z : UE_NR_Capability_v1540__Type)
  : UE_NR_Capability_v1540__cond z ->
  (seq_cond UE_NR_Capability_v1540__list (UE_NR_Capability_v1540__F1 z)).
intro H. unfold UE_NR_Capability_v1540__cond in H. simpl. auto. Qed.
Lemma UE_NR_Capability_v1540__F1F2_cond2 (z : UE_NR_Capability_v1540__Type)
 : UE_NR_Capability_v1540__F2 (UE_NR_Capability_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_Capability_v1540__F2F1_cond (y : seq_type UE_NR_Capability_v1540__list)
  : seq_cond UE_NR_Capability_v1540__list y ->
 (UE_NR_Capability_v1540__cond (UE_NR_Capability_v1540__F2 y)) /\  UE_NR_Capability_v1540__F1 (UE_NR_Capability_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_Capability_v1540__cond. simpl in *. auto.
 - simpl. unfold UE_NR_Capability_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_Capability_v1540__Format : T_Format UE_NR_Capability_v1540__Type UE_NR_Capability_v1540__cond :=
        proj2_format  UE_NR_Capability_v1540__cond UE_NR_Capability_v1540__list__Format
    UE_NR_Capability_v1540__F1 UE_NR_Capability_v1540__F2 UE_NR_Capability_v1540__F1F2_cond  UE_NR_Capability_v1540__F1F2_cond2 UE_NR_Capability_v1540__F2F1_cond.
Opaque UE_NR_Capability_v1540__cond UE_NR_Capability_v1540__Format.

