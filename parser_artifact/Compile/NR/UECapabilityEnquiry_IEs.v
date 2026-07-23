Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UE_CapabilityRAT_RequestList.

Opaque UE_CapabilityRAT_RequestList__cond UE_CapabilityRAT_RequestList__Format.

Record UECapabilityEnquiry_IEs__Type : Set :=
  make__UECapabilityEnquiry_IEs__Type {
    UECapabilityEnquiry_IEs__ue_CapabilityRAT_RequestList : UE_CapabilityRAT_RequestList__Type ;
    UECapabilityEnquiry_IEs__lateNonCriticalExtension : option octet_string ;
    UECapabilityEnquiry_IEs__ue_CapabilityEnquiryExt : option octet_string ;
}.
Definition UECapabilityEnquiry_IEs__list := (
 Nor UE_CapabilityRAT_RequestList__Type UE_CapabilityRAT_RequestList__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition UECapabilityEnquiry_IEs__cond z := 
  UE_CapabilityRAT_RequestList__cond (UECapabilityEnquiry_IEs__ue_CapabilityRAT_RequestList z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UECapabilityEnquiry_IEs__lateNonCriticalExtension z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UECapabilityEnquiry_IEs__ue_CapabilityEnquiryExt z) /\
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

Definition UECapabilityEnquiry_IEs__Format_Type := Eval cbn in seq_format_prod UECapabilityEnquiry_IEs__list.
Definition UECapabilityEnquiry_IEs__Format_list : UECapabilityEnquiry_IEs__Format_Type :=
  (UE_CapabilityRAT_RequestList__Format, (octet_string_nc__Format, (octet_string_nc__Format, unit_format))).
Definition UECapabilityEnquiry_IEs__list__Format := (*Eval compute in *) seq_format UECapabilityEnquiry_IEs__list UECapabilityEnquiry_IEs__Format_list.
Definition UECapabilityEnquiry_IEs__F1 z :=
  (UECapabilityEnquiry_IEs__ue_CapabilityRAT_RequestList z, (UECapabilityEnquiry_IEs__lateNonCriticalExtension z, (UECapabilityEnquiry_IEs__ue_CapabilityEnquiryExt z, tt))).
Definition UECapabilityEnquiry_IEs__F2 (y : seq_type UECapabilityEnquiry_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UECapabilityEnquiry_IEs__Type i0 i1 i2
  end.
Lemma UECapabilityEnquiry_IEs__F1F2_cond (z : UECapabilityEnquiry_IEs__Type)
  : UECapabilityEnquiry_IEs__cond z ->
  (seq_cond UECapabilityEnquiry_IEs__list (UECapabilityEnquiry_IEs__F1 z)).
intro H. unfold UECapabilityEnquiry_IEs__cond in H. simpl. auto. Qed.
Lemma UECapabilityEnquiry_IEs__F1F2_cond2 (z : UECapabilityEnquiry_IEs__Type)
 : UECapabilityEnquiry_IEs__F2 (UECapabilityEnquiry_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityEnquiry_IEs__F2F1_cond (y : seq_type UECapabilityEnquiry_IEs__list)
  : seq_cond UECapabilityEnquiry_IEs__list y ->
 (UECapabilityEnquiry_IEs__cond (UECapabilityEnquiry_IEs__F2 y)) /\  UECapabilityEnquiry_IEs__F1 (UECapabilityEnquiry_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityEnquiry_IEs__cond. simpl in *. auto.
 - simpl. unfold UECapabilityEnquiry_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityEnquiry_IEs__Format : T_Format UECapabilityEnquiry_IEs__Type UECapabilityEnquiry_IEs__cond :=
        proj2_format  UECapabilityEnquiry_IEs__cond UECapabilityEnquiry_IEs__list__Format
    UECapabilityEnquiry_IEs__F1 UECapabilityEnquiry_IEs__F2 UECapabilityEnquiry_IEs__F1F2_cond  UECapabilityEnquiry_IEs__F1F2_cond2 UECapabilityEnquiry_IEs__F2F1_cond.
Opaque UECapabilityEnquiry_IEs__cond UECapabilityEnquiry_IEs__Format.

