Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Type : Set :=
 | SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__true
.
Definition SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__cond := (fun (_ : SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Type) => True).
Lemma SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__nat__helper.

Definition SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1 t :=
  match t with
  | SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__true => 0
  end.
Definition SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F2 n :=
  match n with
  | 0 => SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__true
  | _ => SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__true
  end.
Lemma SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1F2 : forall x : SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Type, (SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1 x <= 0) /\ SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F2 (SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F2F1 : forall (y : nat) (H : y <= 0), SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1 (SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Type : Set :=
 | SIB1_v1610_IEs__idleModeMeasurementsNR_r16__true
.
Definition SIB1_v1610_IEs__idleModeMeasurementsNR_r16__cond := (fun (_ : SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Type) => True).
Lemma SIB1_v1610_IEs__idleModeMeasurementsNR_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1610_IEs__idleModeMeasurementsNR_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1_v1610_IEs__idleModeMeasurementsNR_r16__nat__helper.

Definition SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1 t :=
  match t with
  | SIB1_v1610_IEs__idleModeMeasurementsNR_r16__true => 0
  end.
Definition SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F2 n :=
  match n with
  | 0 => SIB1_v1610_IEs__idleModeMeasurementsNR_r16__true
  | _ => SIB1_v1610_IEs__idleModeMeasurementsNR_r16__true
  end.
Lemma SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1F2 : forall x : SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Type, (SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1 x <= 0) /\ SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F2 (SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F2F1 : forall (y : nat) (H : y <= 0), SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1 (SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PosSI_SchedulingInfo_r16.

Opaque PosSI_SchedulingInfo_r16__cond PosSI_SchedulingInfo_r16__Format.

Require Import NR.SIB1_v1630_IEs.

Opaque SIB1_v1630_IEs__cond SIB1_v1630_IEs__Format.

Record SIB1_v1610_IEs__Type : Set :=
  make__SIB1_v1610_IEs__Type {
    SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16 : option SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Type ;
    SIB1_v1610_IEs__idleModeMeasurementsNR_r16 : option SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Type ;
    SIB1_v1610_IEs__posSI_SchedulingInfo_r16 : option PosSI_SchedulingInfo_r16__Type ;
    SIB1_v1610_IEs__nonCriticalExtension : option SIB1_v1630_IEs__Type ;
}.
Definition SIB1_v1610_IEs__list := (
 Opt SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Type SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__cond ::
 Opt SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Type SIB1_v1610_IEs__idleModeMeasurementsNR_r16__cond ::
 Opt PosSI_SchedulingInfo_r16__Type PosSI_SchedulingInfo_r16__cond ::
 Opt SIB1_v1630_IEs__Type SIB1_v1630_IEs__cond ::
 nil).
Definition SIB1_v1610_IEs__cond z := 
  opt_cond SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__cond (SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16 z) /\
  opt_cond SIB1_v1610_IEs__idleModeMeasurementsNR_r16__cond (SIB1_v1610_IEs__idleModeMeasurementsNR_r16 z) /\
  opt_cond PosSI_SchedulingInfo_r16__cond (SIB1_v1610_IEs__posSI_SchedulingInfo_r16 z) /\
  opt_cond SIB1_v1630_IEs__cond (SIB1_v1610_IEs__nonCriticalExtension z) /\
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
Definition SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Format : T_Format SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__nat__Format SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1 SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F2 SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F1F2 SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__F2F1.

Opaque SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__cond SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Format.

Definition SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Format : T_Format SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1610_IEs__idleModeMeasurementsNR_r16__nat__Format SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1 SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F2 SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F1F2 SIB1_v1610_IEs__idleModeMeasurementsNR_r16__F2F1.

Opaque SIB1_v1610_IEs__idleModeMeasurementsNR_r16__cond SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Format.


Definition SIB1_v1610_IEs__Format_Type := Eval cbn in seq_format_prod SIB1_v1610_IEs__list.
Definition SIB1_v1610_IEs__Format_list : SIB1_v1610_IEs__Format_Type :=
  (SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16__Format, (SIB1_v1610_IEs__idleModeMeasurementsNR_r16__Format, (PosSI_SchedulingInfo_r16__Format, (SIB1_v1630_IEs__Format, unit_format)))).
Definition SIB1_v1610_IEs__list__Format := (*Eval compute in *) seq_format SIB1_v1610_IEs__list SIB1_v1610_IEs__Format_list.
Definition SIB1_v1610_IEs__F1 z :=
  (SIB1_v1610_IEs__idleModeMeasurementsEUTRA_r16 z, (SIB1_v1610_IEs__idleModeMeasurementsNR_r16 z, (SIB1_v1610_IEs__posSI_SchedulingInfo_r16 z, (SIB1_v1610_IEs__nonCriticalExtension z, tt)))).
Definition SIB1_v1610_IEs__F2 (y : seq_type SIB1_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SIB1_v1610_IEs__Type i0 i1 i2 i3
  end.
Lemma SIB1_v1610_IEs__F1F2_cond (z : SIB1_v1610_IEs__Type)
  : SIB1_v1610_IEs__cond z ->
  (seq_cond SIB1_v1610_IEs__list (SIB1_v1610_IEs__F1 z)).
intro H. unfold SIB1_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma SIB1_v1610_IEs__F1F2_cond2 (z : SIB1_v1610_IEs__Type)
 : SIB1_v1610_IEs__F2 (SIB1_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1_v1610_IEs__F2F1_cond (y : seq_type SIB1_v1610_IEs__list)
  : seq_cond SIB1_v1610_IEs__list y ->
 (SIB1_v1610_IEs__cond (SIB1_v1610_IEs__F2 y)) /\  SIB1_v1610_IEs__F1 (SIB1_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold SIB1_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1_v1610_IEs__Format : T_Format SIB1_v1610_IEs__Type SIB1_v1610_IEs__cond :=
        proj2_format  SIB1_v1610_IEs__cond SIB1_v1610_IEs__list__Format
    SIB1_v1610_IEs__F1 SIB1_v1610_IEs__F2 SIB1_v1610_IEs__F1F2_cond  SIB1_v1610_IEs__F1F2_cond2 SIB1_v1610_IEs__F2F1_cond.
Opaque SIB1_v1610_IEs__cond SIB1_v1610_IEs__Format.

