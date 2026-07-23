Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Type : Set :=
 | MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__supported
.
Definition MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__cond := (fun (_ : MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Type) => True).
Lemma MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__nat__helper.

Definition MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1 t :=
  match t with
  | MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__supported => 0
  end.
Definition MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__supported
  | _ => MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__supported
  end.
Lemma MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1F2 : forall x : MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Type, (MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1 x <= 0) /\ MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F2 (MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1 (MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Type : Set :=
 | MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__supported
.
Definition MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__cond := (fun (_ : MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Type) => True).
Lemma MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__nat__helper.

Definition MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1 t :=
  match t with
  | MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__supported => 0
  end.
Definition MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__supported
  | _ => MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__supported
  end.
Lemma MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1F2 : forall x : MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Type, (MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1 x <= 0) /\ MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F2 (MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1 (MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersSidelinkXDD_Diff_r16__Type : Set :=
  make__MAC_ParametersSidelinkXDD_Diff_r16__Type {
    MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16 : option MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Type ;
    MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16 : option MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Type ;
}.
Definition MAC_ParametersSidelinkXDD_Diff_r16__root_list : list seq_elem := (
 Opt MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Type MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__cond ::
 Opt MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Type MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__cond ::
 nil).
Definition MAC_ParametersSidelinkXDD_Diff_r16__ext_list : list typ := (
  nil).
Definition MAC_ParametersSidelinkXDD_Diff_r16__cond (z : MAC_ParametersSidelinkXDD_Diff_r16__Type) := 
(  opt_cond MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__cond (MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16 z) /\
  opt_cond MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__cond (MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16 z) /\
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
Definition MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Format : T_Format MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__nat__Format MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1 MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F2 MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F1F2 MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__F2F1.

Opaque MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__cond MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Format.

Definition MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Format : T_Format MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__nat__Format MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1 MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F2 MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F1F2 MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__F2F1.

Opaque MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__cond MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Format.


Definition MAC_ParametersSidelinkXDD_Diff_r16__root_Format_Type := Eval cbn in seq_format_prod MAC_ParametersSidelinkXDD_Diff_r16__root_list.
Definition MAC_ParametersSidelinkXDD_Diff_r16__root_Format_list : MAC_ParametersSidelinkXDD_Diff_r16__root_Format_Type :=
  (MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16__Format, (MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16__Format, unit_format)).

Definition MAC_ParametersSidelinkXDD_Diff_r16__ext_Format_Type := Eval cbn in get_formats MAC_ParametersSidelinkXDD_Diff_r16__ext_list.
Definition MAC_ParametersSidelinkXDD_Diff_r16__ext_Format_list : MAC_ParametersSidelinkXDD_Diff_r16__ext_Format_Type :=
  unit__Format.

Definition MAC_ParametersSidelinkXDD_Diff_r16__list_type : Set := (seq_type MAC_ParametersSidelinkXDD_Diff_r16__root_list) * (seq_ext_type MAC_ParametersSidelinkXDD_Diff_r16__ext_list).
Definition MAC_ParametersSidelinkXDD_Diff_r16__list_cond (z : MAC_ParametersSidelinkXDD_Diff_r16__list_type) : Prop :=
        (seq_cond MAC_ParametersSidelinkXDD_Diff_r16__root_list (fst z)) /\ (seq_ext_cond MAC_ParametersSidelinkXDD_Diff_r16__ext_list (snd z)).
Definition MAC_ParametersSidelinkXDD_Diff_r16__list_format : T_Format MAC_ParametersSidelinkXDD_Diff_r16__list_type MAC_ParametersSidelinkXDD_Diff_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MAC_ParametersSidelinkXDD_Diff_r16__root_list MAC_ParametersSidelinkXDD_Diff_r16__root_Format_list MAC_ParametersSidelinkXDD_Diff_r16__ext_list MAC_ParametersSidelinkXDD_Diff_r16__ext_Format_list.

Opaque MAC_ParametersSidelinkXDD_Diff_r16__list_format.
Definition MAC_ParametersSidelinkXDD_Diff_r16__F1 (z : MAC_ParametersSidelinkXDD_Diff_r16__Type) : MAC_ParametersSidelinkXDD_Diff_r16__list_type :=
  (((MAC_ParametersSidelinkXDD_Diff_r16__multipleSR_ConfigurationsSidelink_r16 z, (MAC_ParametersSidelinkXDD_Diff_r16__logicalChannelSR_DelayTimerSidelink_r16 z, tt))), (
tt)).
Definition MAC_ParametersSidelinkXDD_Diff_r16__F2 (y : MAC_ParametersSidelinkXDD_Diff_r16__list_type) : MAC_ParametersSidelinkXDD_Diff_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__MAC_ParametersSidelinkXDD_Diff_r16__Type j0 j1
  end.
Definition MAC_ParametersSidelinkXDD_Diff_r16__helper1 : (forall a : MAC_ParametersSidelinkXDD_Diff_r16__Type, MAC_ParametersSidelinkXDD_Diff_r16__cond a -> MAC_ParametersSidelinkXDD_Diff_r16__list_cond (MAC_ParametersSidelinkXDD_Diff_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersSidelinkXDD_Diff_r16__helper2 : (forall a : MAC_ParametersSidelinkXDD_Diff_r16__Type, MAC_ParametersSidelinkXDD_Diff_r16__F2 (MAC_ParametersSidelinkXDD_Diff_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersSidelinkXDD_Diff_r16__helper3 : (forall b : MAC_ParametersSidelinkXDD_Diff_r16__list_type, MAC_ParametersSidelinkXDD_Diff_r16__list_cond b -> MAC_ParametersSidelinkXDD_Diff_r16__cond (MAC_ParametersSidelinkXDD_Diff_r16__F2 b) /\ MAC_ParametersSidelinkXDD_Diff_r16__F1 (MAC_ParametersSidelinkXDD_Diff_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MAC_ParametersSidelinkXDD_Diff_r16__cond, MAC_ParametersSidelinkXDD_Diff_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MAC_ParametersSidelinkXDD_Diff_r16__Format : T_Format MAC_ParametersSidelinkXDD_Diff_r16__Type MAC_ParametersSidelinkXDD_Diff_r16__cond :=
 proj2_format MAC_ParametersSidelinkXDD_Diff_r16__cond MAC_ParametersSidelinkXDD_Diff_r16__list_format  MAC_ParametersSidelinkXDD_Diff_r16__F1 MAC_ParametersSidelinkXDD_Diff_r16__F2 MAC_ParametersSidelinkXDD_Diff_r16__helper1 MAC_ParametersSidelinkXDD_Diff_r16__helper2 MAC_ParametersSidelinkXDD_Diff_r16__helper3.

Opaque MAC_ParametersSidelinkXDD_Diff_r16__cond MAC_ParametersSidelinkXDD_Diff_r16__Format.

