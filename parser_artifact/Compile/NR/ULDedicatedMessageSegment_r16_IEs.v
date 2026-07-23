Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Type := Z.
Definition ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond := (fun z => (0 <= z <= 15)%Z).
Inductive ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type : Set :=
 | ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
 | ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment
.
Definition ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond := (fun (_ : ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type) => True).
Lemma ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__helper.

Definition ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 t :=
  match t with
  | ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment => 0
  | ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment => 1
  end.
Definition ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 n :=
  match n with
  | 0 => ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
  | 1 => ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment
  | _ => ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
  end.
Lemma ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1F2 : forall x : ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type, (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 x <= 1) /\ ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 x) = x. imp_solve. Qed.
Lemma ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2F1 : forall (y : nat) (H : y <= 1), ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 y) = y. enum_solve H y. Qed.

Record ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type : Set := make__ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type {}.
Definition ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond (z : ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type) := True.
Record ULDedicatedMessageSegment_r16_IEs__Type : Set :=
  make__ULDedicatedMessageSegment_r16_IEs__Type {
    ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16 : Z ;
    ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 : octet_string ;
    ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 : ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type ;
    ULDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension : option octet_string ;
    ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension : option ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type ;
}.
Definition ULDedicatedMessageSegment_r16_IEs__list := (
 Nor Z ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Nor ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond ::
 nil).
Definition ULDedicatedMessageSegment_r16_IEs__cond z := 
  ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond (ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 z) /\
  ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (ULDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond (ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension z) /\
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
Definition ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format : T_Format Z ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond :=
 ranged_int_format (0) (15) ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper1 ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper2.

Opaque ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format.

Definition ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format : T_Format ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__Format ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1F2 ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2F1.

Opaque ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format.

Definition ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__helper : forall a : ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type, True -> True /\ make__ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format : T_Format ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type)
    ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format.


Definition ULDedicatedMessageSegment_r16_IEs__Format_Type := Eval cbn in seq_format_prod ULDedicatedMessageSegment_r16_IEs__list.
Definition ULDedicatedMessageSegment_r16_IEs__Format_list : ULDedicatedMessageSegment_r16_IEs__Format_Type :=
  (ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format, (octet_string_nc__Format, (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format, (octet_string_nc__Format, (ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format, unit_format))))).
Definition ULDedicatedMessageSegment_r16_IEs__list__Format := (*Eval compute in *) seq_format ULDedicatedMessageSegment_r16_IEs__list ULDedicatedMessageSegment_r16_IEs__Format_list.
Definition ULDedicatedMessageSegment_r16_IEs__F1 z :=
  (ULDedicatedMessageSegment_r16_IEs__segmentNumber_r16 z, (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 z, (ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 z, (ULDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension z, (ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension z, tt))))).
Definition ULDedicatedMessageSegment_r16_IEs__F2 (y : seq_type ULDedicatedMessageSegment_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__ULDedicatedMessageSegment_r16_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma ULDedicatedMessageSegment_r16_IEs__F1F2_cond (z : ULDedicatedMessageSegment_r16_IEs__Type)
  : ULDedicatedMessageSegment_r16_IEs__cond z ->
  (seq_cond ULDedicatedMessageSegment_r16_IEs__list (ULDedicatedMessageSegment_r16_IEs__F1 z)).
intro H. unfold ULDedicatedMessageSegment_r16_IEs__cond in H. simpl. auto. Qed.
Lemma ULDedicatedMessageSegment_r16_IEs__F1F2_cond2 (z : ULDedicatedMessageSegment_r16_IEs__Type)
 : ULDedicatedMessageSegment_r16_IEs__F2 (ULDedicatedMessageSegment_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ULDedicatedMessageSegment_r16_IEs__F2F1_cond (y : seq_type ULDedicatedMessageSegment_r16_IEs__list)
  : seq_cond ULDedicatedMessageSegment_r16_IEs__list y ->
 (ULDedicatedMessageSegment_r16_IEs__cond (ULDedicatedMessageSegment_r16_IEs__F2 y)) /\  ULDedicatedMessageSegment_r16_IEs__F1 (ULDedicatedMessageSegment_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ULDedicatedMessageSegment_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold ULDedicatedMessageSegment_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ULDedicatedMessageSegment_r16_IEs__Format : T_Format ULDedicatedMessageSegment_r16_IEs__Type ULDedicatedMessageSegment_r16_IEs__cond :=
        proj2_format  ULDedicatedMessageSegment_r16_IEs__cond ULDedicatedMessageSegment_r16_IEs__list__Format
    ULDedicatedMessageSegment_r16_IEs__F1 ULDedicatedMessageSegment_r16_IEs__F2 ULDedicatedMessageSegment_r16_IEs__F1F2_cond  ULDedicatedMessageSegment_r16_IEs__F1F2_cond2 ULDedicatedMessageSegment_r16_IEs__F2F1_cond.
Opaque ULDedicatedMessageSegment_r16_IEs__cond ULDedicatedMessageSegment_r16_IEs__Format.

