Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition LogMeasResultBT_r16__bt_Addr_r16__Type := bit_string_fixed.
Definition LogMeasResultBT_r16__bt_Addr_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 48 /\ bit_string_len_prop (fst z) (snd z)).
Lemma LogMeasResultBT_r16__rssi_BT_r16__helper1 : (-128 <= 127)%Z.  lia. Qed.
Lemma LogMeasResultBT_r16__rssi_BT_r16__helper2 : to_bit_sz (Z.to_nat (127 - -128)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - -128))%Z). { apply Zorder.Zle_minus_le_0. apply LogMeasResultBT_r16__rssi_BT_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogMeasResultBT_r16__rssi_BT_r16__Type := Z.
Definition LogMeasResultBT_r16__rssi_BT_r16__cond := (fun z => (-128 <= z <= 127)%Z).
Record LogMeasResultBT_r16__Type : Set :=
  make__LogMeasResultBT_r16__Type {
    LogMeasResultBT_r16__bt_Addr_r16 : LogMeasResultBT_r16__bt_Addr_r16__Type ;
    LogMeasResultBT_r16__rssi_BT_r16 : option Z ;
}.
Definition LogMeasResultBT_r16__root_list : list seq_elem := (
 Nor LogMeasResultBT_r16__bt_Addr_r16__Type LogMeasResultBT_r16__bt_Addr_r16__cond ::
 Opt Z LogMeasResultBT_r16__rssi_BT_r16__cond ::
 nil).
Definition LogMeasResultBT_r16__ext_list : list typ := (
  nil).
Definition LogMeasResultBT_r16__cond (z : LogMeasResultBT_r16__Type) := 
(  LogMeasResultBT_r16__bt_Addr_r16__cond (LogMeasResultBT_r16__bt_Addr_r16 z) /\
  opt_cond LogMeasResultBT_r16__rssi_BT_r16__cond (LogMeasResultBT_r16__rssi_BT_r16 z) /\
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
Definition LogMeasResultBT_r16__bt_Addr_r16__Format : T_Format LogMeasResultBT_r16__bt_Addr_r16__Type LogMeasResultBT_r16__bt_Addr_r16__cond := (* Eval compute in *) bit_string_fixed_format 48.
Opaque LogMeasResultBT_r16__bt_Addr_r16__cond LogMeasResultBT_r16__bt_Addr_r16__Format.

Definition LogMeasResultBT_r16__rssi_BT_r16__Format : T_Format Z LogMeasResultBT_r16__rssi_BT_r16__cond :=
 ranged_int_format (-128) (127) LogMeasResultBT_r16__rssi_BT_r16__helper1 LogMeasResultBT_r16__rssi_BT_r16__helper2.

Opaque LogMeasResultBT_r16__rssi_BT_r16__cond LogMeasResultBT_r16__rssi_BT_r16__Format.


Definition LogMeasResultBT_r16__root_Format_Type := Eval cbn in seq_format_prod LogMeasResultBT_r16__root_list.
Definition LogMeasResultBT_r16__root_Format_list : LogMeasResultBT_r16__root_Format_Type :=
  (LogMeasResultBT_r16__bt_Addr_r16__Format, (LogMeasResultBT_r16__rssi_BT_r16__Format, unit_format)).

Definition LogMeasResultBT_r16__ext_Format_Type := Eval cbn in get_formats LogMeasResultBT_r16__ext_list.
Definition LogMeasResultBT_r16__ext_Format_list : LogMeasResultBT_r16__ext_Format_Type :=
  unit__Format.

Definition LogMeasResultBT_r16__list_type : Set := (seq_type LogMeasResultBT_r16__root_list) * (seq_ext_type LogMeasResultBT_r16__ext_list).
Definition LogMeasResultBT_r16__list_cond (z : LogMeasResultBT_r16__list_type) : Prop :=
        (seq_cond LogMeasResultBT_r16__root_list (fst z)) /\ (seq_ext_cond LogMeasResultBT_r16__ext_list (snd z)).
Definition LogMeasResultBT_r16__list_format : T_Format LogMeasResultBT_r16__list_type LogMeasResultBT_r16__list_cond :=
 (* Eval compute in *) seq_ext_format LogMeasResultBT_r16__root_list LogMeasResultBT_r16__root_Format_list LogMeasResultBT_r16__ext_list LogMeasResultBT_r16__ext_Format_list.

Opaque LogMeasResultBT_r16__list_format.
Definition LogMeasResultBT_r16__F1 (z : LogMeasResultBT_r16__Type) : LogMeasResultBT_r16__list_type :=
  (((LogMeasResultBT_r16__bt_Addr_r16 z, (LogMeasResultBT_r16__rssi_BT_r16 z, tt))), (
tt)).
Definition LogMeasResultBT_r16__F2 (y : LogMeasResultBT_r16__list_type) : LogMeasResultBT_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__LogMeasResultBT_r16__Type j0 j1
  end.
Definition LogMeasResultBT_r16__helper1 : (forall a : LogMeasResultBT_r16__Type, LogMeasResultBT_r16__cond a -> LogMeasResultBT_r16__list_cond (LogMeasResultBT_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LogMeasResultBT_r16__helper2 : (forall a : LogMeasResultBT_r16__Type, LogMeasResultBT_r16__F2 (LogMeasResultBT_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LogMeasResultBT_r16__helper3 : (forall b : LogMeasResultBT_r16__list_type, LogMeasResultBT_r16__list_cond b -> LogMeasResultBT_r16__cond (LogMeasResultBT_r16__F2 b) /\ LogMeasResultBT_r16__F1 (LogMeasResultBT_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LogMeasResultBT_r16__cond, LogMeasResultBT_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LogMeasResultBT_r16__Format : T_Format LogMeasResultBT_r16__Type LogMeasResultBT_r16__cond :=
 proj2_format LogMeasResultBT_r16__cond LogMeasResultBT_r16__list_format  LogMeasResultBT_r16__F1 LogMeasResultBT_r16__F2 LogMeasResultBT_r16__helper1 LogMeasResultBT_r16__helper2 LogMeasResultBT_r16__helper3.

Opaque LogMeasResultBT_r16__cond LogMeasResultBT_r16__Format.

