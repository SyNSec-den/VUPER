Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Require Import NR.Uu_RelayRLC_ChannelID_r17.

Opaque Uu_RelayRLC_ChannelID_r17__cond Uu_RelayRLC_ChannelID_r17__Format.

Inductive Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Type : Set :=
 | Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__true
.
Definition Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__cond := (fun (_ : Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Type) => True).
Lemma Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__nat__helper.

Definition Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1 t :=
  match t with
  | Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__true => 0
  end.
Definition Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F2 n :=
  match n with
  | 0 => Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__true
  | _ => Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__true
  end.
Lemma Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1F2 : forall x : Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Type, (Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1 x <= 0) /\ Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F2 (Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1 x) = x. imp_solve. Qed.
Lemma Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F2F1 : forall (y : nat) (H : y <= 0), Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1 (Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RLC_Config.

Opaque RLC_Config__cond RLC_Config__Format.

Require Import NR.LogicalChannelConfig.

Opaque LogicalChannelConfig__cond LogicalChannelConfig__Format.

Record Uu_RelayRLC_ChannelConfig_r17__Type : Set :=
  make__Uu_RelayRLC_ChannelConfig_r17__Type {
    Uu_RelayRLC_ChannelConfig_r17__uu_LogicalChannelIdentity_r17 : option LogicalChannelIdentity__Type ;
    Uu_RelayRLC_ChannelConfig_r17__uu_RelayRLC_ChannelID_r17 : Uu_RelayRLC_ChannelID_r17__Type ;
    Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17 : option Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Type ;
    Uu_RelayRLC_ChannelConfig_r17__rlc_Config_r17 : option RLC_Config__Type ;
    Uu_RelayRLC_ChannelConfig_r17__mac_LogicalChannelConfig_r17 : option LogicalChannelConfig__Type ;
}.
Definition Uu_RelayRLC_ChannelConfig_r17__root_list : list seq_elem := (
 Opt LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
 Nor Uu_RelayRLC_ChannelID_r17__Type Uu_RelayRLC_ChannelID_r17__cond ::
 Opt Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Type Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__cond ::
 Opt RLC_Config__Type RLC_Config__cond ::
 Opt LogicalChannelConfig__Type LogicalChannelConfig__cond ::
 nil).
Definition Uu_RelayRLC_ChannelConfig_r17__ext_list : list typ := (
  nil).
Definition Uu_RelayRLC_ChannelConfig_r17__cond (z : Uu_RelayRLC_ChannelConfig_r17__Type) := 
(  opt_cond LogicalChannelIdentity__cond (Uu_RelayRLC_ChannelConfig_r17__uu_LogicalChannelIdentity_r17 z) /\
  Uu_RelayRLC_ChannelID_r17__cond (Uu_RelayRLC_ChannelConfig_r17__uu_RelayRLC_ChannelID_r17 z) /\
  opt_cond Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__cond (Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17 z) /\
  opt_cond RLC_Config__cond (Uu_RelayRLC_ChannelConfig_r17__rlc_Config_r17 z) /\
  opt_cond LogicalChannelConfig__cond (Uu_RelayRLC_ChannelConfig_r17__mac_LogicalChannelConfig_r17 z) /\
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
Definition Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Format : T_Format Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__nat__Format Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1 Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F2 Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F1F2 Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__F2F1.

Opaque Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__cond Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Format.


Definition Uu_RelayRLC_ChannelConfig_r17__root_Format_Type := Eval cbn in seq_format_prod Uu_RelayRLC_ChannelConfig_r17__root_list.
Definition Uu_RelayRLC_ChannelConfig_r17__root_Format_list : Uu_RelayRLC_ChannelConfig_r17__root_Format_Type :=
  (LogicalChannelIdentity__Format, (Uu_RelayRLC_ChannelID_r17__Format, (Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17__Format, (RLC_Config__Format, (LogicalChannelConfig__Format, unit_format))))).

Definition Uu_RelayRLC_ChannelConfig_r17__ext_Format_Type := Eval cbn in get_formats Uu_RelayRLC_ChannelConfig_r17__ext_list.
Definition Uu_RelayRLC_ChannelConfig_r17__ext_Format_list : Uu_RelayRLC_ChannelConfig_r17__ext_Format_Type :=
  unit__Format.

Definition Uu_RelayRLC_ChannelConfig_r17__list_type : Set := (seq_type Uu_RelayRLC_ChannelConfig_r17__root_list) * (seq_ext_type Uu_RelayRLC_ChannelConfig_r17__ext_list).
Definition Uu_RelayRLC_ChannelConfig_r17__list_cond (z : Uu_RelayRLC_ChannelConfig_r17__list_type) : Prop :=
        (seq_cond Uu_RelayRLC_ChannelConfig_r17__root_list (fst z)) /\ (seq_ext_cond Uu_RelayRLC_ChannelConfig_r17__ext_list (snd z)).
Definition Uu_RelayRLC_ChannelConfig_r17__list_format : T_Format Uu_RelayRLC_ChannelConfig_r17__list_type Uu_RelayRLC_ChannelConfig_r17__list_cond :=
 (* Eval compute in *) seq_ext_format Uu_RelayRLC_ChannelConfig_r17__root_list Uu_RelayRLC_ChannelConfig_r17__root_Format_list Uu_RelayRLC_ChannelConfig_r17__ext_list Uu_RelayRLC_ChannelConfig_r17__ext_Format_list.

Opaque Uu_RelayRLC_ChannelConfig_r17__list_format.
Definition Uu_RelayRLC_ChannelConfig_r17__F1 (z : Uu_RelayRLC_ChannelConfig_r17__Type) : Uu_RelayRLC_ChannelConfig_r17__list_type :=
  (((Uu_RelayRLC_ChannelConfig_r17__uu_LogicalChannelIdentity_r17 z, (Uu_RelayRLC_ChannelConfig_r17__uu_RelayRLC_ChannelID_r17 z, (Uu_RelayRLC_ChannelConfig_r17__reestablishRLC_r17 z, (Uu_RelayRLC_ChannelConfig_r17__rlc_Config_r17 z, (Uu_RelayRLC_ChannelConfig_r17__mac_LogicalChannelConfig_r17 z, tt)))))), (
tt)).
Definition Uu_RelayRLC_ChannelConfig_r17__F2 (y : Uu_RelayRLC_ChannelConfig_r17__list_type) : Uu_RelayRLC_ChannelConfig_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__Uu_RelayRLC_ChannelConfig_r17__Type j0 j1 j2 j3 j4
  end.
Definition Uu_RelayRLC_ChannelConfig_r17__helper1 : (forall a : Uu_RelayRLC_ChannelConfig_r17__Type, Uu_RelayRLC_ChannelConfig_r17__cond a -> Uu_RelayRLC_ChannelConfig_r17__list_cond (Uu_RelayRLC_ChannelConfig_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Uu_RelayRLC_ChannelConfig_r17__helper2 : (forall a : Uu_RelayRLC_ChannelConfig_r17__Type, Uu_RelayRLC_ChannelConfig_r17__F2 (Uu_RelayRLC_ChannelConfig_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Uu_RelayRLC_ChannelConfig_r17__helper3 : (forall b : Uu_RelayRLC_ChannelConfig_r17__list_type, Uu_RelayRLC_ChannelConfig_r17__list_cond b -> Uu_RelayRLC_ChannelConfig_r17__cond (Uu_RelayRLC_ChannelConfig_r17__F2 b) /\ Uu_RelayRLC_ChannelConfig_r17__F1 (Uu_RelayRLC_ChannelConfig_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Uu_RelayRLC_ChannelConfig_r17__cond, Uu_RelayRLC_ChannelConfig_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Uu_RelayRLC_ChannelConfig_r17__Format : T_Format Uu_RelayRLC_ChannelConfig_r17__Type Uu_RelayRLC_ChannelConfig_r17__cond :=
 proj2_format Uu_RelayRLC_ChannelConfig_r17__cond Uu_RelayRLC_ChannelConfig_r17__list_format  Uu_RelayRLC_ChannelConfig_r17__F1 Uu_RelayRLC_ChannelConfig_r17__F2 Uu_RelayRLC_ChannelConfig_r17__helper1 Uu_RelayRLC_ChannelConfig_r17__helper2 Uu_RelayRLC_ChannelConfig_r17__helper3.

Opaque Uu_RelayRLC_ChannelConfig_r17__cond Uu_RelayRLC_ChannelConfig_r17__Format.

