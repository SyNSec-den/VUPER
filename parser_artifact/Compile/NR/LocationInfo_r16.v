Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CommonLocationInfo_r16.

Opaque CommonLocationInfo_r16__cond CommonLocationInfo_r16__Format.

Require Import NR.LogMeasResultListBT_r16.

Opaque LogMeasResultListBT_r16__cond LogMeasResultListBT_r16__Format.

Require Import NR.LogMeasResultListWLAN_r16.

Opaque LogMeasResultListWLAN_r16__cond LogMeasResultListWLAN_r16__Format.

Require Import NR.Sensor_LocationInfo_r16.

Opaque Sensor_LocationInfo_r16__cond Sensor_LocationInfo_r16__Format.

Record LocationInfo_r16__Type : Set :=
  make__LocationInfo_r16__Type {
    LocationInfo_r16__commonLocationInfo_r16 : option CommonLocationInfo_r16__Type ;
    LocationInfo_r16__bt_LocationInfo_r16 : option LogMeasResultListBT_r16__Type ;
    LocationInfo_r16__wlan_LocationInfo_r16 : option LogMeasResultListWLAN_r16__Type ;
    LocationInfo_r16__sensor_LocationInfo_r16 : option Sensor_LocationInfo_r16__Type ;
}.
Definition LocationInfo_r16__root_list : list seq_elem := (
 Opt CommonLocationInfo_r16__Type CommonLocationInfo_r16__cond ::
 Opt LogMeasResultListBT_r16__Type LogMeasResultListBT_r16__cond ::
 Opt LogMeasResultListWLAN_r16__Type LogMeasResultListWLAN_r16__cond ::
 Opt Sensor_LocationInfo_r16__Type Sensor_LocationInfo_r16__cond ::
 nil).
Definition LocationInfo_r16__ext_list : list typ := (
  nil).
Definition LocationInfo_r16__cond (z : LocationInfo_r16__Type) := 
(  opt_cond CommonLocationInfo_r16__cond (LocationInfo_r16__commonLocationInfo_r16 z) /\
  opt_cond LogMeasResultListBT_r16__cond (LocationInfo_r16__bt_LocationInfo_r16 z) /\
  opt_cond LogMeasResultListWLAN_r16__cond (LocationInfo_r16__wlan_LocationInfo_r16 z) /\
  opt_cond Sensor_LocationInfo_r16__cond (LocationInfo_r16__sensor_LocationInfo_r16 z) /\
  True) /\ 
(  True).


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

Definition LocationInfo_r16__root_Format_Type := Eval cbn in seq_format_prod LocationInfo_r16__root_list.
Definition LocationInfo_r16__root_Format_list : LocationInfo_r16__root_Format_Type :=
  (CommonLocationInfo_r16__Format, (LogMeasResultListBT_r16__Format, (LogMeasResultListWLAN_r16__Format, (Sensor_LocationInfo_r16__Format, unit_format)))).

Definition LocationInfo_r16__ext_Format_Type := Eval cbn in get_formats LocationInfo_r16__ext_list.
Definition LocationInfo_r16__ext_Format_list : LocationInfo_r16__ext_Format_Type :=
  unit__Format.

Definition LocationInfo_r16__list_type : Set := (seq_type LocationInfo_r16__root_list) * (seq_ext_type LocationInfo_r16__ext_list).
Definition LocationInfo_r16__list_cond (z : LocationInfo_r16__list_type) : Prop :=
        (seq_cond LocationInfo_r16__root_list (fst z)) /\ (seq_ext_cond LocationInfo_r16__ext_list (snd z)).
Definition LocationInfo_r16__list_format : T_Format LocationInfo_r16__list_type LocationInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format LocationInfo_r16__root_list LocationInfo_r16__root_Format_list LocationInfo_r16__ext_list LocationInfo_r16__ext_Format_list.

Opaque LocationInfo_r16__list_format.
Definition LocationInfo_r16__F1 (z : LocationInfo_r16__Type) : LocationInfo_r16__list_type :=
  (((LocationInfo_r16__commonLocationInfo_r16 z, (LocationInfo_r16__bt_LocationInfo_r16 z, (LocationInfo_r16__wlan_LocationInfo_r16 z, (LocationInfo_r16__sensor_LocationInfo_r16 z, tt))))), (
tt)).
Definition LocationInfo_r16__F2 (y : LocationInfo_r16__list_type) : LocationInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__LocationInfo_r16__Type j0 j1 j2 j3
  end.
Definition LocationInfo_r16__helper1 : (forall a : LocationInfo_r16__Type, LocationInfo_r16__cond a -> LocationInfo_r16__list_cond (LocationInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LocationInfo_r16__helper2 : (forall a : LocationInfo_r16__Type, LocationInfo_r16__F2 (LocationInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LocationInfo_r16__helper3 : (forall b : LocationInfo_r16__list_type, LocationInfo_r16__list_cond b -> LocationInfo_r16__cond (LocationInfo_r16__F2 b) /\ LocationInfo_r16__F1 (LocationInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LocationInfo_r16__cond, LocationInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LocationInfo_r16__Format : T_Format LocationInfo_r16__Type LocationInfo_r16__cond :=
 proj2_format LocationInfo_r16__cond LocationInfo_r16__list_format  LocationInfo_r16__F1 LocationInfo_r16__F2 LocationInfo_r16__helper1 LocationInfo_r16__helper2 LocationInfo_r16__helper3.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

