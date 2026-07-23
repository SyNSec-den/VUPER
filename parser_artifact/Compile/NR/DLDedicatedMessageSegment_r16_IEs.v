Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Type := Z.
Definition DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond := (fun z => (0 <= z <= 4)%Z).
Inductive DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type : Set :=
 | DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
 | DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment
.
Definition DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond := (fun (_ : DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type) => True).
Lemma DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__helper.

Definition DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 t :=
  match t with
  | DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment => 0
  | DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment => 1
  end.
Definition DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 n :=
  match n with
  | 0 => DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
  | 1 => DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment
  | _ => DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
  end.
Lemma DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1F2 : forall x : DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type, (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 x <= 1) /\ DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 x) = x. imp_solve. Qed.
Lemma DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2F1 : forall (y : nat) (H : y <= 1), DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 y) = y. enum_solve H y. Qed.

Record DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type : Set := make__DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type {}.
Definition DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond (z : DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type) := True.
Record DLDedicatedMessageSegment_r16_IEs__Type : Set :=
  make__DLDedicatedMessageSegment_r16_IEs__Type {
    DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16 : Z ;
    DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 : octet_string ;
    DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 : DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type ;
    DLDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension : option octet_string ;
    DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension : option DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type ;
}.
Definition DLDedicatedMessageSegment_r16_IEs__list := (
 Nor Z DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Nor DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond ::
 nil).
Definition DLDedicatedMessageSegment_r16_IEs__cond z := 
  DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond (DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 z) /\
  DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (DLDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond (DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension z) /\
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
Definition DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format : T_Format Z DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond :=
 ranged_int_format (0) (4) DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper1 DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__helper2.

Opaque DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__cond DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format.

Definition DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format : T_Format DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__Format DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1F2 DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2F1.

Opaque DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__cond DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format.

Definition DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__helper : forall a : DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type, True -> True /\ make__DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format : T_Format DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type)
    DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__cond DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format.


Definition DLDedicatedMessageSegment_r16_IEs__Format_Type := Eval cbn in seq_format_prod DLDedicatedMessageSegment_r16_IEs__list.
Definition DLDedicatedMessageSegment_r16_IEs__Format_list : DLDedicatedMessageSegment_r16_IEs__Format_Type :=
  (DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format, (octet_string_nc__Format, (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format, (octet_string_nc__Format, (DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format, unit_format))))).
Definition DLDedicatedMessageSegment_r16_IEs__list__Format := (*Eval compute in *) seq_format DLDedicatedMessageSegment_r16_IEs__list DLDedicatedMessageSegment_r16_IEs__Format_list.
Definition DLDedicatedMessageSegment_r16_IEs__F1 z :=
  (DLDedicatedMessageSegment_r16_IEs__segmentNumber_r16 z, (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 z, (DLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 z, (DLDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension z, (DLDedicatedMessageSegment_r16_IEs__nonCriticalExtension z, tt))))).
Definition DLDedicatedMessageSegment_r16_IEs__F2 (y : seq_type DLDedicatedMessageSegment_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__DLDedicatedMessageSegment_r16_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma DLDedicatedMessageSegment_r16_IEs__F1F2_cond (z : DLDedicatedMessageSegment_r16_IEs__Type)
  : DLDedicatedMessageSegment_r16_IEs__cond z ->
  (seq_cond DLDedicatedMessageSegment_r16_IEs__list (DLDedicatedMessageSegment_r16_IEs__F1 z)).
intro H. unfold DLDedicatedMessageSegment_r16_IEs__cond in H. simpl. auto. Qed.
Lemma DLDedicatedMessageSegment_r16_IEs__F1F2_cond2 (z : DLDedicatedMessageSegment_r16_IEs__Type)
 : DLDedicatedMessageSegment_r16_IEs__F2 (DLDedicatedMessageSegment_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DLDedicatedMessageSegment_r16_IEs__F2F1_cond (y : seq_type DLDedicatedMessageSegment_r16_IEs__list)
  : seq_cond DLDedicatedMessageSegment_r16_IEs__list y ->
 (DLDedicatedMessageSegment_r16_IEs__cond (DLDedicatedMessageSegment_r16_IEs__F2 y)) /\  DLDedicatedMessageSegment_r16_IEs__F1 (DLDedicatedMessageSegment_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DLDedicatedMessageSegment_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold DLDedicatedMessageSegment_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DLDedicatedMessageSegment_r16_IEs__Format : T_Format DLDedicatedMessageSegment_r16_IEs__Type DLDedicatedMessageSegment_r16_IEs__cond :=
        proj2_format  DLDedicatedMessageSegment_r16_IEs__cond DLDedicatedMessageSegment_r16_IEs__list__Format
    DLDedicatedMessageSegment_r16_IEs__F1 DLDedicatedMessageSegment_r16_IEs__F2 DLDedicatedMessageSegment_r16_IEs__F1F2_cond  DLDedicatedMessageSegment_r16_IEs__F1F2_cond2 DLDedicatedMessageSegment_r16_IEs__F2F1_cond.
Opaque DLDedicatedMessageSegment_r16_IEs__cond DLDedicatedMessageSegment_r16_IEs__Format.

