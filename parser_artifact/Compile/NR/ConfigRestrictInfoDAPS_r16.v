Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Inductive ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Type : Set :=
 | ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode1
 | ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode2
 | ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__dynamic
.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__cond := (fun (_ : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Type) => True).
Lemma ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__nat__helper.

Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1 t :=
  match t with
  | ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode1 => 0
  | ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode2 => 1
  | ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__dynamic => 2
  end.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F2 n :=
  match n with
  | 0 => ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode1
  | 1 => ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode2
  | 2 => ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__dynamic
  | _ => ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__semi_static_mode1
  end.
Lemma ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1F2 : forall x : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Type, (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1 x <= 2) /\ ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F2 (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F2F1 : forall (y : nat) (H : y <= 2), ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1 (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F2 y) = y. enum_solve H y. Qed.

Record ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type : Set :=
  make__ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type {
    ConfigRestrictInfoDAPS_r16__powerCoordination_r16__p_DAPS_Source_r16 : P_Max__Type ;
    ConfigRestrictInfoDAPS_r16__powerCoordination_r16__p_DAPS_Target_r16 : P_Max__Type ;
    ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16 : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Type ;
}.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list := (
 Nor P_Max__Type P_Max__cond ::
 Nor P_Max__Type P_Max__cond ::
 Nor ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Type ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__cond ::
 nil).
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond z := 
  P_Max__cond (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__p_DAPS_Source_r16 z) /\
  P_Max__cond (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__p_DAPS_Target_r16 z) /\
  ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__cond (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16 z) /\
  True.

Record ConfigRestrictInfoDAPS_r16__Type : Set :=
  make__ConfigRestrictInfoDAPS_r16__Type {
    ConfigRestrictInfoDAPS_r16__powerCoordination_r16 : option ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type ;
}.
Definition ConfigRestrictInfoDAPS_r16__list := (
 Opt ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond ::
 nil).
Definition ConfigRestrictInfoDAPS_r16__cond z := 
  opt_cond ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond (ConfigRestrictInfoDAPS_r16__powerCoordination_r16 z) /\
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
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Format : T_Format ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__nat__Format ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F2 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F1F2 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__F2F1.

Opaque ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__cond ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Format.


Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format_list : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format_Type :=
  (P_Max__Format, (P_Max__Format, (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16__Format, unit_format))).
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format_list.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1 z :=
  (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__p_DAPS_Source_r16 z, (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__p_DAPS_Target_r16 z, (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__uplinkPowerSharingDAPS_Mode_r16 z, tt))).
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2 (y : seq_type ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type i0 i1 i2
  end.
Lemma ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1F2_cond (z : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type)
  : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond z ->
  (seq_cond ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1 z)).
intro H. unfold ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1F2_cond2 (z : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type)
 : ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2 (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2F1_cond (y : seq_type ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list)
  : seq_cond ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list y ->
 (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2 y)) /\  ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1 (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format : T_Format ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Type ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond :=
        proj2_format  ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond ConfigRestrictInfoDAPS_r16__powerCoordination_r16__list__Format
    ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1F2_cond  ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F1F2_cond2 ConfigRestrictInfoDAPS_r16__powerCoordination_r16__F2F1_cond.
Opaque ConfigRestrictInfoDAPS_r16__powerCoordination_r16__cond ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format.


Definition ConfigRestrictInfoDAPS_r16__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoDAPS_r16__list.
Definition ConfigRestrictInfoDAPS_r16__Format_list : ConfigRestrictInfoDAPS_r16__Format_Type :=
  (ConfigRestrictInfoDAPS_r16__powerCoordination_r16__Format, unit_format).
Definition ConfigRestrictInfoDAPS_r16__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoDAPS_r16__list ConfigRestrictInfoDAPS_r16__Format_list.
Definition ConfigRestrictInfoDAPS_r16__F1 z :=
  (ConfigRestrictInfoDAPS_r16__powerCoordination_r16 z, tt).
Definition ConfigRestrictInfoDAPS_r16__F2 (y : seq_type ConfigRestrictInfoDAPS_r16__list) :=
  match y with
  | (i0, _)=>
    make__ConfigRestrictInfoDAPS_r16__Type i0
  end.
Lemma ConfigRestrictInfoDAPS_r16__F1F2_cond (z : ConfigRestrictInfoDAPS_r16__Type)
  : ConfigRestrictInfoDAPS_r16__cond z ->
  (seq_cond ConfigRestrictInfoDAPS_r16__list (ConfigRestrictInfoDAPS_r16__F1 z)).
intro H. unfold ConfigRestrictInfoDAPS_r16__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoDAPS_r16__F1F2_cond2 (z : ConfigRestrictInfoDAPS_r16__Type)
 : ConfigRestrictInfoDAPS_r16__F2 (ConfigRestrictInfoDAPS_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoDAPS_r16__F2F1_cond (y : seq_type ConfigRestrictInfoDAPS_r16__list)
  : seq_cond ConfigRestrictInfoDAPS_r16__list y ->
 (ConfigRestrictInfoDAPS_r16__cond (ConfigRestrictInfoDAPS_r16__F2 y)) /\  ConfigRestrictInfoDAPS_r16__F1 (ConfigRestrictInfoDAPS_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoDAPS_r16__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoDAPS_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoDAPS_r16__Format : T_Format ConfigRestrictInfoDAPS_r16__Type ConfigRestrictInfoDAPS_r16__cond :=
        proj2_format  ConfigRestrictInfoDAPS_r16__cond ConfigRestrictInfoDAPS_r16__list__Format
    ConfigRestrictInfoDAPS_r16__F1 ConfigRestrictInfoDAPS_r16__F2 ConfigRestrictInfoDAPS_r16__F1F2_cond  ConfigRestrictInfoDAPS_r16__F1F2_cond2 ConfigRestrictInfoDAPS_r16__F2F1_cond.
Opaque ConfigRestrictInfoDAPS_r16__cond ConfigRestrictInfoDAPS_r16__Format.

