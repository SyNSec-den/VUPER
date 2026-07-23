Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Type : Set :=
 | MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__true
.
Definition MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__cond := (fun (_ : MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Type) => True).
Lemma MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__nat__helper.

Definition MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1 t :=
  match t with
  | MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__true => 0
  end.
Definition MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F2 n :=
  match n with
  | 0 => MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__true
  | _ => MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__true
  end.
Lemma MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1F2 : forall x : MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Type, (MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1 x <= 0) /\ MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F2 (MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1 x) = x. imp_solve. Qed.
Lemma MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F2F1 : forall (y : nat) (H : y <= 0), MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1 (MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F2 y) = y. enum_solve H y. Qed.

Record MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type : Set := make__MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type {}.
Definition MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__cond (z : MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type) := True.
Record MobilityFromNRCommand_v1610_IEs__Type : Set :=
  make__MobilityFromNRCommand_v1610_IEs__Type {
    MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16 : option MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Type ;
    MobilityFromNRCommand_v1610_IEs__nonCriticalExtension : option MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type ;
}.
Definition MobilityFromNRCommand_v1610_IEs__list := (
 Opt MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Type MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__cond ::
 Opt MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__cond ::
 nil).
Definition MobilityFromNRCommand_v1610_IEs__cond z := 
  opt_cond MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__cond (MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16 z) /\
  opt_cond MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__cond (MobilityFromNRCommand_v1610_IEs__nonCriticalExtension z) /\
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
Definition MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Format : T_Format MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__nat__Format MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1 MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F2 MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F1F2 MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__F2F1.

Opaque MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__cond MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Format.

Definition MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__helper : forall a : MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type, True -> True /\ make__MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Format : T_Format MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Type)
    MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__cond MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Format.


Definition MobilityFromNRCommand_v1610_IEs__Format_Type := Eval cbn in seq_format_prod MobilityFromNRCommand_v1610_IEs__list.
Definition MobilityFromNRCommand_v1610_IEs__Format_list : MobilityFromNRCommand_v1610_IEs__Format_Type :=
  (MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16__Format, (MobilityFromNRCommand_v1610_IEs__nonCriticalExtension__Format, unit_format)).
Definition MobilityFromNRCommand_v1610_IEs__list__Format := (*Eval compute in *) seq_format MobilityFromNRCommand_v1610_IEs__list MobilityFromNRCommand_v1610_IEs__Format_list.
Definition MobilityFromNRCommand_v1610_IEs__F1 z :=
  (MobilityFromNRCommand_v1610_IEs__voiceFallbackIndication_r16 z, (MobilityFromNRCommand_v1610_IEs__nonCriticalExtension z, tt)).
Definition MobilityFromNRCommand_v1610_IEs__F2 (y : seq_type MobilityFromNRCommand_v1610_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MobilityFromNRCommand_v1610_IEs__Type i0 i1
  end.
Lemma MobilityFromNRCommand_v1610_IEs__F1F2_cond (z : MobilityFromNRCommand_v1610_IEs__Type)
  : MobilityFromNRCommand_v1610_IEs__cond z ->
  (seq_cond MobilityFromNRCommand_v1610_IEs__list (MobilityFromNRCommand_v1610_IEs__F1 z)).
intro H. unfold MobilityFromNRCommand_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma MobilityFromNRCommand_v1610_IEs__F1F2_cond2 (z : MobilityFromNRCommand_v1610_IEs__Type)
 : MobilityFromNRCommand_v1610_IEs__F2 (MobilityFromNRCommand_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MobilityFromNRCommand_v1610_IEs__F2F1_cond (y : seq_type MobilityFromNRCommand_v1610_IEs__list)
  : seq_cond MobilityFromNRCommand_v1610_IEs__list y ->
 (MobilityFromNRCommand_v1610_IEs__cond (MobilityFromNRCommand_v1610_IEs__F2 y)) /\  MobilityFromNRCommand_v1610_IEs__F1 (MobilityFromNRCommand_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MobilityFromNRCommand_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold MobilityFromNRCommand_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MobilityFromNRCommand_v1610_IEs__Format : T_Format MobilityFromNRCommand_v1610_IEs__Type MobilityFromNRCommand_v1610_IEs__cond :=
        proj2_format  MobilityFromNRCommand_v1610_IEs__cond MobilityFromNRCommand_v1610_IEs__list__Format
    MobilityFromNRCommand_v1610_IEs__F1 MobilityFromNRCommand_v1610_IEs__F2 MobilityFromNRCommand_v1610_IEs__F1F2_cond  MobilityFromNRCommand_v1610_IEs__F1F2_cond2 MobilityFromNRCommand_v1610_IEs__F2F1_cond.
Opaque MobilityFromNRCommand_v1610_IEs__cond MobilityFromNRCommand_v1610_IEs__Format.

