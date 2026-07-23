Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Type : Set :=
 | UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__true
.
Definition UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__cond := (fun (_ : UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Type) => True).
Lemma UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__nat__helper.

Definition UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1 t :=
  match t with
  | UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__true => 0
  end.
Definition UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F2 n :=
  match n with
  | 0 => UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__true
  | _ => UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__true
  end.
Lemma UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1F2 : forall x : UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Type, (UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1 x <= 0) /\ UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F2 (UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1 (UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F2 y) = y. enum_solve H y. Qed.

Record UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type : Set := make__UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type {}.
Definition UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__cond (z : UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type) := True.
Record UE_CapabilityRequestFilterNR_v1710__Type : Set :=
  make__UE_CapabilityRequestFilterNR_v1710__Type {
    UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17 : option UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Type ;
    UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension : option UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type ;
}.
Definition UE_CapabilityRequestFilterNR_v1710__list := (
 Opt UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Type UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__cond ::
 Opt UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__cond ::
 nil).
Definition UE_CapabilityRequestFilterNR_v1710__cond z := 
  opt_cond UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__cond (UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17 z) /\
  opt_cond UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__cond (UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension z) /\
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
Definition UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Format : T_Format UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__nat__Format UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1 UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F2 UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F1F2 UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__F2F1.

Opaque UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__cond UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Format.

Definition UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__helper : forall a : UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type, True -> True /\ make__UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Format : T_Format UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Type)
    UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__cond UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Format.


Definition UE_CapabilityRequestFilterNR_v1710__Format_Type := Eval cbn in seq_format_prod UE_CapabilityRequestFilterNR_v1710__list.
Definition UE_CapabilityRequestFilterNR_v1710__Format_list : UE_CapabilityRequestFilterNR_v1710__Format_Type :=
  (UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17__Format, (UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension__Format, unit_format)).
Definition UE_CapabilityRequestFilterNR_v1710__list__Format := (*Eval compute in *) seq_format UE_CapabilityRequestFilterNR_v1710__list UE_CapabilityRequestFilterNR_v1710__Format_list.
Definition UE_CapabilityRequestFilterNR_v1710__F1 z :=
  (UE_CapabilityRequestFilterNR_v1710__sidelinkRequest_r17 z, (UE_CapabilityRequestFilterNR_v1710__nonCriticalExtension z, tt)).
Definition UE_CapabilityRequestFilterNR_v1710__F2 (y : seq_type UE_CapabilityRequestFilterNR_v1710__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UE_CapabilityRequestFilterNR_v1710__Type i0 i1
  end.
Lemma UE_CapabilityRequestFilterNR_v1710__F1F2_cond (z : UE_CapabilityRequestFilterNR_v1710__Type)
  : UE_CapabilityRequestFilterNR_v1710__cond z ->
  (seq_cond UE_CapabilityRequestFilterNR_v1710__list (UE_CapabilityRequestFilterNR_v1710__F1 z)).
intro H. unfold UE_CapabilityRequestFilterNR_v1710__cond in H. simpl. auto. Qed.
Lemma UE_CapabilityRequestFilterNR_v1710__F1F2_cond2 (z : UE_CapabilityRequestFilterNR_v1710__Type)
 : UE_CapabilityRequestFilterNR_v1710__F2 (UE_CapabilityRequestFilterNR_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_CapabilityRequestFilterNR_v1710__F2F1_cond (y : seq_type UE_CapabilityRequestFilterNR_v1710__list)
  : seq_cond UE_CapabilityRequestFilterNR_v1710__list y ->
 (UE_CapabilityRequestFilterNR_v1710__cond (UE_CapabilityRequestFilterNR_v1710__F2 y)) /\  UE_CapabilityRequestFilterNR_v1710__F1 (UE_CapabilityRequestFilterNR_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_CapabilityRequestFilterNR_v1710__cond. simpl in *. auto.
 - simpl. unfold UE_CapabilityRequestFilterNR_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_CapabilityRequestFilterNR_v1710__Format : T_Format UE_CapabilityRequestFilterNR_v1710__Type UE_CapabilityRequestFilterNR_v1710__cond :=
        proj2_format  UE_CapabilityRequestFilterNR_v1710__cond UE_CapabilityRequestFilterNR_v1710__list__Format
    UE_CapabilityRequestFilterNR_v1710__F1 UE_CapabilityRequestFilterNR_v1710__F2 UE_CapabilityRequestFilterNR_v1710__F1F2_cond  UE_CapabilityRequestFilterNR_v1710__F1F2_cond2 UE_CapabilityRequestFilterNR_v1710__F2F1_cond.
Opaque UE_CapabilityRequestFilterNR_v1710__cond UE_CapabilityRequestFilterNR_v1710__Format.

