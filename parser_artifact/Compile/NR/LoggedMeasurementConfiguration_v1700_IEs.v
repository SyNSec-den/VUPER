Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Type : Set :=
 | LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__true
.
Definition LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__cond := (fun (_ : LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Type) => True).
Lemma LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__nat__helper.

Definition LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1 t :=
  match t with
  | LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__true => 0
  end.
Definition LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F2 n :=
  match n with
  | 0 => LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__true
  | _ => LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__true
  end.
Lemma LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1F2 : forall x : LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Type, (LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1 x <= 0) /\ LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F2 (LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1 x) = x. imp_solve. Qed.
Lemma LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F2F1 : forall (y : nat) (H : y <= 0), LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1 (LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F2 y) = y. enum_solve H y. Qed.

Inductive LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Type : Set :=
 | LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__true
.
Definition LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__cond := (fun (_ : LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Type) => True).
Lemma LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__nat__helper.

Definition LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1 t :=
  match t with
  | LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__true => 0
  end.
Definition LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F2 n :=
  match n with
  | 0 => LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__true
  | _ => LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__true
  end.
Lemma LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1F2 : forall x : LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Type, (LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1 x <= 0) /\ LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F2 (LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1 x) = x. imp_solve. Qed.
Lemma LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F2F1 : forall (y : nat) (H : y <= 0), LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1 (LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.AreaConfiguration_v1700.

Opaque AreaConfiguration_v1700__cond AreaConfiguration_v1700__Format.

Record LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type : Set := make__LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type {}.
Definition LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__cond (z : LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type) := True.
Record LoggedMeasurementConfiguration_v1700_IEs__Type : Set :=
  make__LoggedMeasurementConfiguration_v1700_IEs__Type {
    LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17 : option LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Type ;
    LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17 : option LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Type ;
    LoggedMeasurementConfiguration_v1700_IEs__areaConfiguration_v1700 : option AreaConfiguration_v1700__Type ;
    LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension : option LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition LoggedMeasurementConfiguration_v1700_IEs__list := (
 Opt LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Type LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__cond ::
 Opt LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Type LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__cond ::
 Opt AreaConfiguration_v1700__Type AreaConfiguration_v1700__cond ::
 Opt LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition LoggedMeasurementConfiguration_v1700_IEs__cond z := 
  opt_cond LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__cond (LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17 z) /\
  opt_cond LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__cond (LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17 z) /\
  opt_cond AreaConfiguration_v1700__cond (LoggedMeasurementConfiguration_v1700_IEs__areaConfiguration_v1700 z) /\
  opt_cond LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__cond (LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension z) /\
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
Definition LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Format : T_Format LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__nat__Format LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1 LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F2 LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F1F2 LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__F2F1.

Opaque LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__cond LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Format.

Definition LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Format : T_Format LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__nat__Format LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1 LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F2 LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F1F2 LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__F2F1.

Opaque LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__cond LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Format.

Definition LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__helper : forall a : LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Format : T_Format LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Type)
    LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__cond LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Format.


Definition LoggedMeasurementConfiguration_v1700_IEs__Format_Type := Eval cbn in seq_format_prod LoggedMeasurementConfiguration_v1700_IEs__list.
Definition LoggedMeasurementConfiguration_v1700_IEs__Format_list : LoggedMeasurementConfiguration_v1700_IEs__Format_Type :=
  (LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17__Format, (LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17__Format, (AreaConfiguration_v1700__Format, (LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension__Format, unit_format)))).
Definition LoggedMeasurementConfiguration_v1700_IEs__list__Format := (*Eval compute in *) seq_format LoggedMeasurementConfiguration_v1700_IEs__list LoggedMeasurementConfiguration_v1700_IEs__Format_list.
Definition LoggedMeasurementConfiguration_v1700_IEs__F1 z :=
  (LoggedMeasurementConfiguration_v1700_IEs__sigLoggedMeasType_r17 z, (LoggedMeasurementConfiguration_v1700_IEs__earlyMeasIndication_r17 z, (LoggedMeasurementConfiguration_v1700_IEs__areaConfiguration_v1700 z, (LoggedMeasurementConfiguration_v1700_IEs__nonCriticalExtension z, tt)))).
Definition LoggedMeasurementConfiguration_v1700_IEs__F2 (y : seq_type LoggedMeasurementConfiguration_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__LoggedMeasurementConfiguration_v1700_IEs__Type i0 i1 i2 i3
  end.
Lemma LoggedMeasurementConfiguration_v1700_IEs__F1F2_cond (z : LoggedMeasurementConfiguration_v1700_IEs__Type)
  : LoggedMeasurementConfiguration_v1700_IEs__cond z ->
  (seq_cond LoggedMeasurementConfiguration_v1700_IEs__list (LoggedMeasurementConfiguration_v1700_IEs__F1 z)).
intro H. unfold LoggedMeasurementConfiguration_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma LoggedMeasurementConfiguration_v1700_IEs__F1F2_cond2 (z : LoggedMeasurementConfiguration_v1700_IEs__Type)
 : LoggedMeasurementConfiguration_v1700_IEs__F2 (LoggedMeasurementConfiguration_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LoggedMeasurementConfiguration_v1700_IEs__F2F1_cond (y : seq_type LoggedMeasurementConfiguration_v1700_IEs__list)
  : seq_cond LoggedMeasurementConfiguration_v1700_IEs__list y ->
 (LoggedMeasurementConfiguration_v1700_IEs__cond (LoggedMeasurementConfiguration_v1700_IEs__F2 y)) /\  LoggedMeasurementConfiguration_v1700_IEs__F1 (LoggedMeasurementConfiguration_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LoggedMeasurementConfiguration_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold LoggedMeasurementConfiguration_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LoggedMeasurementConfiguration_v1700_IEs__Format : T_Format LoggedMeasurementConfiguration_v1700_IEs__Type LoggedMeasurementConfiguration_v1700_IEs__cond :=
        proj2_format  LoggedMeasurementConfiguration_v1700_IEs__cond LoggedMeasurementConfiguration_v1700_IEs__list__Format
    LoggedMeasurementConfiguration_v1700_IEs__F1 LoggedMeasurementConfiguration_v1700_IEs__F2 LoggedMeasurementConfiguration_v1700_IEs__F1F2_cond  LoggedMeasurementConfiguration_v1700_IEs__F1F2_cond2 LoggedMeasurementConfiguration_v1700_IEs__F2F1_cond.
Opaque LoggedMeasurementConfiguration_v1700_IEs__cond LoggedMeasurementConfiguration_v1700_IEs__Format.

