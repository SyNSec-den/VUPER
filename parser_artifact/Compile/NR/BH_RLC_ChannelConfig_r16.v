Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BH_LogicalChannelIdentity_r16.

Opaque BH_LogicalChannelIdentity_r16__cond BH_LogicalChannelIdentity_r16__Format.

Require Import NR.BH_RLC_ChannelID_r16.

Opaque BH_RLC_ChannelID_r16__cond BH_RLC_ChannelID_r16__Format.

Inductive BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Type : Set :=
 | BH_RLC_ChannelConfig_r16__reestablishRLC_r16__true
.
Definition BH_RLC_ChannelConfig_r16__reestablishRLC_r16__cond := (fun (_ : BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Type) => True).
Lemma BH_RLC_ChannelConfig_r16__reestablishRLC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BH_RLC_ChannelConfig_r16__reestablishRLC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BH_RLC_ChannelConfig_r16__reestablishRLC_r16__nat__helper.

Definition BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1 t :=
  match t with
  | BH_RLC_ChannelConfig_r16__reestablishRLC_r16__true => 0
  end.
Definition BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F2 n :=
  match n with
  | 0 => BH_RLC_ChannelConfig_r16__reestablishRLC_r16__true
  | _ => BH_RLC_ChannelConfig_r16__reestablishRLC_r16__true
  end.
Lemma BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1F2 : forall x : BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Type, (BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1 x <= 0) /\ BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F2 (BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1 x) = x. imp_solve. Qed.
Lemma BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F2F1 : forall (y : nat) (H : y <= 0), BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1 (BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RLC_Config.

Opaque RLC_Config__cond RLC_Config__Format.

Require Import NR.LogicalChannelConfig.

Opaque LogicalChannelConfig__cond LogicalChannelConfig__Format.

Record BH_RLC_ChannelConfig_r16__Type : Set :=
  make__BH_RLC_ChannelConfig_r16__Type {
    BH_RLC_ChannelConfig_r16__bh_LogicalChannelIdentity_r16 : option BH_LogicalChannelIdentity_r16__Type ;
    BH_RLC_ChannelConfig_r16__bh_RLC_ChannelID_r16 : BH_RLC_ChannelID_r16__Type ;
    BH_RLC_ChannelConfig_r16__reestablishRLC_r16 : option BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Type ;
    BH_RLC_ChannelConfig_r16__rlc_Config_r16 : option RLC_Config__Type ;
    BH_RLC_ChannelConfig_r16__mac_LogicalChannelConfig_r16 : option LogicalChannelConfig__Type ;
}.
Definition BH_RLC_ChannelConfig_r16__root_list : list seq_elem := (
 Opt BH_LogicalChannelIdentity_r16__Type BH_LogicalChannelIdentity_r16__cond ::
 Nor BH_RLC_ChannelID_r16__Type BH_RLC_ChannelID_r16__cond ::
 Opt BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Type BH_RLC_ChannelConfig_r16__reestablishRLC_r16__cond ::
 Opt RLC_Config__Type RLC_Config__cond ::
 Opt LogicalChannelConfig__Type LogicalChannelConfig__cond ::
 nil).
Definition BH_RLC_ChannelConfig_r16__ext_list : list typ := (
  nil).
Definition BH_RLC_ChannelConfig_r16__cond (z : BH_RLC_ChannelConfig_r16__Type) := 
(  opt_cond BH_LogicalChannelIdentity_r16__cond (BH_RLC_ChannelConfig_r16__bh_LogicalChannelIdentity_r16 z) /\
  BH_RLC_ChannelID_r16__cond (BH_RLC_ChannelConfig_r16__bh_RLC_ChannelID_r16 z) /\
  opt_cond BH_RLC_ChannelConfig_r16__reestablishRLC_r16__cond (BH_RLC_ChannelConfig_r16__reestablishRLC_r16 z) /\
  opt_cond RLC_Config__cond (BH_RLC_ChannelConfig_r16__rlc_Config_r16 z) /\
  opt_cond LogicalChannelConfig__cond (BH_RLC_ChannelConfig_r16__mac_LogicalChannelConfig_r16 z) /\
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
Definition BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Format : T_Format BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BH_RLC_ChannelConfig_r16__reestablishRLC_r16__nat__Format BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1 BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F2 BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F1F2 BH_RLC_ChannelConfig_r16__reestablishRLC_r16__F2F1.

Opaque BH_RLC_ChannelConfig_r16__reestablishRLC_r16__cond BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Format.


Definition BH_RLC_ChannelConfig_r16__root_Format_Type := Eval cbn in seq_format_prod BH_RLC_ChannelConfig_r16__root_list.
Definition BH_RLC_ChannelConfig_r16__root_Format_list : BH_RLC_ChannelConfig_r16__root_Format_Type :=
  (BH_LogicalChannelIdentity_r16__Format, (BH_RLC_ChannelID_r16__Format, (BH_RLC_ChannelConfig_r16__reestablishRLC_r16__Format, (RLC_Config__Format, (LogicalChannelConfig__Format, unit_format))))).

Definition BH_RLC_ChannelConfig_r16__ext_Format_Type := Eval cbn in get_formats BH_RLC_ChannelConfig_r16__ext_list.
Definition BH_RLC_ChannelConfig_r16__ext_Format_list : BH_RLC_ChannelConfig_r16__ext_Format_Type :=
  unit__Format.

Definition BH_RLC_ChannelConfig_r16__list_type : Set := (seq_type BH_RLC_ChannelConfig_r16__root_list) * (seq_ext_type BH_RLC_ChannelConfig_r16__ext_list).
Definition BH_RLC_ChannelConfig_r16__list_cond (z : BH_RLC_ChannelConfig_r16__list_type) : Prop :=
        (seq_cond BH_RLC_ChannelConfig_r16__root_list (fst z)) /\ (seq_ext_cond BH_RLC_ChannelConfig_r16__ext_list (snd z)).
Definition BH_RLC_ChannelConfig_r16__list_format : T_Format BH_RLC_ChannelConfig_r16__list_type BH_RLC_ChannelConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format BH_RLC_ChannelConfig_r16__root_list BH_RLC_ChannelConfig_r16__root_Format_list BH_RLC_ChannelConfig_r16__ext_list BH_RLC_ChannelConfig_r16__ext_Format_list.

Opaque BH_RLC_ChannelConfig_r16__list_format.
Definition BH_RLC_ChannelConfig_r16__F1 (z : BH_RLC_ChannelConfig_r16__Type) : BH_RLC_ChannelConfig_r16__list_type :=
  (((BH_RLC_ChannelConfig_r16__bh_LogicalChannelIdentity_r16 z, (BH_RLC_ChannelConfig_r16__bh_RLC_ChannelID_r16 z, (BH_RLC_ChannelConfig_r16__reestablishRLC_r16 z, (BH_RLC_ChannelConfig_r16__rlc_Config_r16 z, (BH_RLC_ChannelConfig_r16__mac_LogicalChannelConfig_r16 z, tt)))))), (
tt)).
Definition BH_RLC_ChannelConfig_r16__F2 (y : BH_RLC_ChannelConfig_r16__list_type) : BH_RLC_ChannelConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__BH_RLC_ChannelConfig_r16__Type j0 j1 j2 j3 j4
  end.
Definition BH_RLC_ChannelConfig_r16__helper1 : (forall a : BH_RLC_ChannelConfig_r16__Type, BH_RLC_ChannelConfig_r16__cond a -> BH_RLC_ChannelConfig_r16__list_cond (BH_RLC_ChannelConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BH_RLC_ChannelConfig_r16__helper2 : (forall a : BH_RLC_ChannelConfig_r16__Type, BH_RLC_ChannelConfig_r16__F2 (BH_RLC_ChannelConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BH_RLC_ChannelConfig_r16__helper3 : (forall b : BH_RLC_ChannelConfig_r16__list_type, BH_RLC_ChannelConfig_r16__list_cond b -> BH_RLC_ChannelConfig_r16__cond (BH_RLC_ChannelConfig_r16__F2 b) /\ BH_RLC_ChannelConfig_r16__F1 (BH_RLC_ChannelConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BH_RLC_ChannelConfig_r16__cond, BH_RLC_ChannelConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BH_RLC_ChannelConfig_r16__Format : T_Format BH_RLC_ChannelConfig_r16__Type BH_RLC_ChannelConfig_r16__cond :=
 proj2_format BH_RLC_ChannelConfig_r16__cond BH_RLC_ChannelConfig_r16__list_format  BH_RLC_ChannelConfig_r16__F1 BH_RLC_ChannelConfig_r16__F2 BH_RLC_ChannelConfig_r16__helper1 BH_RLC_ChannelConfig_r16__helper2 BH_RLC_ChannelConfig_r16__helper3.

Opaque BH_RLC_ChannelConfig_r16__cond BH_RLC_ChannelConfig_r16__Format.

