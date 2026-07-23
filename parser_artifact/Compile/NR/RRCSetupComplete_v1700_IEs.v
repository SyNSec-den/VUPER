Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type : Set :=
 | RRCSetupComplete_v1700_IEs__onboardingRequest_r17__true
.
Definition RRCSetupComplete_v1700_IEs__onboardingRequest_r17__cond := (fun (_ : RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type) => True).
Lemma RRCSetupComplete_v1700_IEs__onboardingRequest_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCSetupComplete_v1700_IEs__onboardingRequest_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCSetupComplete_v1700_IEs__onboardingRequest_r17__nat__helper.

Definition RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1 t :=
  match t with
  | RRCSetupComplete_v1700_IEs__onboardingRequest_r17__true => 0
  end.
Definition RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2 n :=
  match n with
  | 0 => RRCSetupComplete_v1700_IEs__onboardingRequest_r17__true
  | _ => RRCSetupComplete_v1700_IEs__onboardingRequest_r17__true
  end.
Lemma RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1F2 : forall x : RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type, (RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1 x <= 0) /\ RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2 (RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1 x) = x. imp_solve. Qed.
Lemma RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2F1 : forall (y : nat) (H : y <= 0), RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1 (RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2 y) = y. enum_solve H y. Qed.

Record RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type : Set := make__RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type {}.
Definition RRCSetupComplete_v1700_IEs__nonCriticalExtension__cond (z : RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type) := True.
Record RRCSetupComplete_v1700_IEs__Type : Set :=
  make__RRCSetupComplete_v1700_IEs__Type {
    RRCSetupComplete_v1700_IEs__onboardingRequest_r17 : option RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type ;
    RRCSetupComplete_v1700_IEs__nonCriticalExtension : option RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition RRCSetupComplete_v1700_IEs__list := (
 Opt RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type RRCSetupComplete_v1700_IEs__onboardingRequest_r17__cond ::
 Opt RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type RRCSetupComplete_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition RRCSetupComplete_v1700_IEs__cond z := 
  opt_cond RRCSetupComplete_v1700_IEs__onboardingRequest_r17__cond (RRCSetupComplete_v1700_IEs__onboardingRequest_r17 z) /\
  opt_cond RRCSetupComplete_v1700_IEs__nonCriticalExtension__cond (RRCSetupComplete_v1700_IEs__nonCriticalExtension z) /\
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
Definition RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Format : T_Format RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCSetupComplete_v1700_IEs__onboardingRequest_r17__nat__Format RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1 RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2 RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1F2 RRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2F1.

Opaque RRCSetupComplete_v1700_IEs__onboardingRequest_r17__cond RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Format.

Definition RRCSetupComplete_v1700_IEs__nonCriticalExtension__helper : forall a : RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCSetupComplete_v1700_IEs__nonCriticalExtension__Format : T_Format RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type RRCSetupComplete_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type)
    RRCSetupComplete_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque RRCSetupComplete_v1700_IEs__nonCriticalExtension__cond RRCSetupComplete_v1700_IEs__nonCriticalExtension__Format.


Definition RRCSetupComplete_v1700_IEs__Format_Type := Eval cbn in seq_format_prod RRCSetupComplete_v1700_IEs__list.
Definition RRCSetupComplete_v1700_IEs__Format_list : RRCSetupComplete_v1700_IEs__Format_Type :=
  (RRCSetupComplete_v1700_IEs__onboardingRequest_r17__Format, (RRCSetupComplete_v1700_IEs__nonCriticalExtension__Format, unit_format)).
Definition RRCSetupComplete_v1700_IEs__list__Format := (*Eval compute in *) seq_format RRCSetupComplete_v1700_IEs__list RRCSetupComplete_v1700_IEs__Format_list.
Definition RRCSetupComplete_v1700_IEs__F1 z :=
  (RRCSetupComplete_v1700_IEs__onboardingRequest_r17 z, (RRCSetupComplete_v1700_IEs__nonCriticalExtension z, tt)).
Definition RRCSetupComplete_v1700_IEs__F2 (y : seq_type RRCSetupComplete_v1700_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCSetupComplete_v1700_IEs__Type i0 i1
  end.
Lemma RRCSetupComplete_v1700_IEs__F1F2_cond (z : RRCSetupComplete_v1700_IEs__Type)
  : RRCSetupComplete_v1700_IEs__cond z ->
  (seq_cond RRCSetupComplete_v1700_IEs__list (RRCSetupComplete_v1700_IEs__F1 z)).
intro H. unfold RRCSetupComplete_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma RRCSetupComplete_v1700_IEs__F1F2_cond2 (z : RRCSetupComplete_v1700_IEs__Type)
 : RRCSetupComplete_v1700_IEs__F2 (RRCSetupComplete_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetupComplete_v1700_IEs__F2F1_cond (y : seq_type RRCSetupComplete_v1700_IEs__list)
  : seq_cond RRCSetupComplete_v1700_IEs__list y ->
 (RRCSetupComplete_v1700_IEs__cond (RRCSetupComplete_v1700_IEs__F2 y)) /\  RRCSetupComplete_v1700_IEs__F1 (RRCSetupComplete_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetupComplete_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCSetupComplete_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetupComplete_v1700_IEs__Format : T_Format RRCSetupComplete_v1700_IEs__Type RRCSetupComplete_v1700_IEs__cond :=
        proj2_format  RRCSetupComplete_v1700_IEs__cond RRCSetupComplete_v1700_IEs__list__Format
    RRCSetupComplete_v1700_IEs__F1 RRCSetupComplete_v1700_IEs__F2 RRCSetupComplete_v1700_IEs__F1F2_cond  RRCSetupComplete_v1700_IEs__F1F2_cond2 RRCSetupComplete_v1700_IEs__F2F1_cond.
Opaque RRCSetupComplete_v1700_IEs__cond RRCSetupComplete_v1700_IEs__Format.

