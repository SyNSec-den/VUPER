Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition BAP_Config_r16__bap_Address_r16__Type := bit_string_fixed.
Definition BAP_Config_r16__bap_Address_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.BAP_RoutingID_r16.

Opaque BAP_RoutingID_r16__cond BAP_RoutingID_r16__Format.

Require Import NR.BH_RLC_ChannelID_r16.

Opaque BH_RLC_ChannelID_r16__cond BH_RLC_ChannelID_r16__Format.

Inductive BAP_Config_r16__flowControlFeedbackType_r16__Type : Set :=
 | BAP_Config_r16__flowControlFeedbackType_r16__perBH_RLC_Channel
 | BAP_Config_r16__flowControlFeedbackType_r16__perRoutingID
 | BAP_Config_r16__flowControlFeedbackType_r16__both
.
Definition BAP_Config_r16__flowControlFeedbackType_r16__cond := (fun (_ : BAP_Config_r16__flowControlFeedbackType_r16__Type) => True).
Lemma BAP_Config_r16__flowControlFeedbackType_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BAP_Config_r16__flowControlFeedbackType_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BAP_Config_r16__flowControlFeedbackType_r16__nat__helper.

Definition BAP_Config_r16__flowControlFeedbackType_r16__F1 t :=
  match t with
  | BAP_Config_r16__flowControlFeedbackType_r16__perBH_RLC_Channel => 0
  | BAP_Config_r16__flowControlFeedbackType_r16__perRoutingID => 1
  | BAP_Config_r16__flowControlFeedbackType_r16__both => 2
  end.
Definition BAP_Config_r16__flowControlFeedbackType_r16__F2 n :=
  match n with
  | 0 => BAP_Config_r16__flowControlFeedbackType_r16__perBH_RLC_Channel
  | 1 => BAP_Config_r16__flowControlFeedbackType_r16__perRoutingID
  | 2 => BAP_Config_r16__flowControlFeedbackType_r16__both
  | _ => BAP_Config_r16__flowControlFeedbackType_r16__perBH_RLC_Channel
  end.
Lemma BAP_Config_r16__flowControlFeedbackType_r16__F1F2 : forall x : BAP_Config_r16__flowControlFeedbackType_r16__Type, (BAP_Config_r16__flowControlFeedbackType_r16__F1 x <= 2) /\ BAP_Config_r16__flowControlFeedbackType_r16__F2 (BAP_Config_r16__flowControlFeedbackType_r16__F1 x) = x. imp_solve. Qed.
Lemma BAP_Config_r16__flowControlFeedbackType_r16__F2F1 : forall (y : nat) (H : y <= 2), BAP_Config_r16__flowControlFeedbackType_r16__F1 (BAP_Config_r16__flowControlFeedbackType_r16__F2 y) = y. enum_solve H y. Qed.

Record BAP_Config_r16__Type : Set :=
  make__BAP_Config_r16__Type {
    BAP_Config_r16__bap_Address_r16 : option BAP_Config_r16__bap_Address_r16__Type ;
    BAP_Config_r16__defaultUL_BAP_RoutingID_r16 : option BAP_RoutingID_r16__Type ;
    BAP_Config_r16__defaultUL_BH_RLC_Channel_r16 : option BH_RLC_ChannelID_r16__Type ;
    BAP_Config_r16__flowControlFeedbackType_r16 : option BAP_Config_r16__flowControlFeedbackType_r16__Type ;
}.
Definition BAP_Config_r16__root_list : list seq_elem := (
 Opt BAP_Config_r16__bap_Address_r16__Type BAP_Config_r16__bap_Address_r16__cond ::
 Opt BAP_RoutingID_r16__Type BAP_RoutingID_r16__cond ::
 Opt BH_RLC_ChannelID_r16__Type BH_RLC_ChannelID_r16__cond ::
 Opt BAP_Config_r16__flowControlFeedbackType_r16__Type BAP_Config_r16__flowControlFeedbackType_r16__cond ::
 nil).
Definition BAP_Config_r16__ext_list : list typ := (
  nil).
Definition BAP_Config_r16__cond (z : BAP_Config_r16__Type) := 
(  opt_cond BAP_Config_r16__bap_Address_r16__cond (BAP_Config_r16__bap_Address_r16 z) /\
  opt_cond BAP_RoutingID_r16__cond (BAP_Config_r16__defaultUL_BAP_RoutingID_r16 z) /\
  opt_cond BH_RLC_ChannelID_r16__cond (BAP_Config_r16__defaultUL_BH_RLC_Channel_r16 z) /\
  opt_cond BAP_Config_r16__flowControlFeedbackType_r16__cond (BAP_Config_r16__flowControlFeedbackType_r16 z) /\
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
Definition BAP_Config_r16__bap_Address_r16__Format : T_Format BAP_Config_r16__bap_Address_r16__Type BAP_Config_r16__bap_Address_r16__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BAP_Config_r16__bap_Address_r16__cond BAP_Config_r16__bap_Address_r16__Format.

Definition BAP_Config_r16__flowControlFeedbackType_r16__Format : T_Format BAP_Config_r16__flowControlFeedbackType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BAP_Config_r16__flowControlFeedbackType_r16__nat__Format BAP_Config_r16__flowControlFeedbackType_r16__F1 BAP_Config_r16__flowControlFeedbackType_r16__F2 BAP_Config_r16__flowControlFeedbackType_r16__F1F2 BAP_Config_r16__flowControlFeedbackType_r16__F2F1.

Opaque BAP_Config_r16__flowControlFeedbackType_r16__cond BAP_Config_r16__flowControlFeedbackType_r16__Format.


Definition BAP_Config_r16__root_Format_Type := Eval cbn in seq_format_prod BAP_Config_r16__root_list.
Definition BAP_Config_r16__root_Format_list : BAP_Config_r16__root_Format_Type :=
  (BAP_Config_r16__bap_Address_r16__Format, (BAP_RoutingID_r16__Format, (BH_RLC_ChannelID_r16__Format, (BAP_Config_r16__flowControlFeedbackType_r16__Format, unit_format)))).

Definition BAP_Config_r16__ext_Format_Type := Eval cbn in get_formats BAP_Config_r16__ext_list.
Definition BAP_Config_r16__ext_Format_list : BAP_Config_r16__ext_Format_Type :=
  unit__Format.

Definition BAP_Config_r16__list_type : Set := (seq_type BAP_Config_r16__root_list) * (seq_ext_type BAP_Config_r16__ext_list).
Definition BAP_Config_r16__list_cond (z : BAP_Config_r16__list_type) : Prop :=
        (seq_cond BAP_Config_r16__root_list (fst z)) /\ (seq_ext_cond BAP_Config_r16__ext_list (snd z)).
Definition BAP_Config_r16__list_format : T_Format BAP_Config_r16__list_type BAP_Config_r16__list_cond :=
 (* Eval compute in *) seq_ext_format BAP_Config_r16__root_list BAP_Config_r16__root_Format_list BAP_Config_r16__ext_list BAP_Config_r16__ext_Format_list.

Opaque BAP_Config_r16__list_format.
Definition BAP_Config_r16__F1 (z : BAP_Config_r16__Type) : BAP_Config_r16__list_type :=
  (((BAP_Config_r16__bap_Address_r16 z, (BAP_Config_r16__defaultUL_BAP_RoutingID_r16 z, (BAP_Config_r16__defaultUL_BH_RLC_Channel_r16 z, (BAP_Config_r16__flowControlFeedbackType_r16 z, tt))))), (
tt)).
Definition BAP_Config_r16__F2 (y : BAP_Config_r16__list_type) : BAP_Config_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__BAP_Config_r16__Type j0 j1 j2 j3
  end.
Definition BAP_Config_r16__helper1 : (forall a : BAP_Config_r16__Type, BAP_Config_r16__cond a -> BAP_Config_r16__list_cond (BAP_Config_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BAP_Config_r16__helper2 : (forall a : BAP_Config_r16__Type, BAP_Config_r16__F2 (BAP_Config_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BAP_Config_r16__helper3 : (forall b : BAP_Config_r16__list_type, BAP_Config_r16__list_cond b -> BAP_Config_r16__cond (BAP_Config_r16__F2 b) /\ BAP_Config_r16__F1 (BAP_Config_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BAP_Config_r16__cond, BAP_Config_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BAP_Config_r16__Format : T_Format BAP_Config_r16__Type BAP_Config_r16__cond :=
 proj2_format BAP_Config_r16__cond BAP_Config_r16__list_format  BAP_Config_r16__F1 BAP_Config_r16__F2 BAP_Config_r16__helper1 BAP_Config_r16__helper2 BAP_Config_r16__helper3.

Opaque BAP_Config_r16__cond BAP_Config_r16__Format.

