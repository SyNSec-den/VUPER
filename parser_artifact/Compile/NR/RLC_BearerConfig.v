Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Require Import NR.SRB_Identity.

Opaque SRB_Identity__cond SRB_Identity__Format.

Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.


Inductive RLC_BearerConfig__servedRadioBearer__Type : Set :=
  | RLC_BearerConfig__servedRadioBearer__srb_Identity : SRB_Identity__Type -> RLC_BearerConfig__servedRadioBearer__Type
  | RLC_BearerConfig__servedRadioBearer__drb_Identity : DRB_Identity__Type -> RLC_BearerConfig__servedRadioBearer__Type
.
Definition RLC_BearerConfig__servedRadioBearer__list : list typ := (
typ_cons SRB_Identity__Type SRB_Identity__cond ::
typ_cons DRB_Identity__Type DRB_Identity__cond ::
 nil).
Definition RLC_BearerConfig__servedRadioBearer__cond (c : RLC_BearerConfig__servedRadioBearer__Type) := 
  match c with
  | RLC_BearerConfig__servedRadioBearer__srb_Identity t => SRB_Identity__cond t 
  | RLC_BearerConfig__servedRadioBearer__drb_Identity t => DRB_Identity__cond t 
  end.

Lemma RLC_BearerConfig__servedRadioBearer__len_helper1 : to_bit_sz (length RLC_BearerConfig__servedRadioBearer__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLC_BearerConfig__servedRadioBearer__len_helper2 : 2 <= length2 RLC_BearerConfig__servedRadioBearer__list.
 simpl. lia. Qed.
Inductive RLC_BearerConfig__reestablishRLC__Type : Set :=
 | RLC_BearerConfig__reestablishRLC__true
.
Definition RLC_BearerConfig__reestablishRLC__cond := (fun (_ : RLC_BearerConfig__reestablishRLC__Type) => True).
Lemma RLC_BearerConfig__reestablishRLC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_BearerConfig__reestablishRLC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_BearerConfig__reestablishRLC__nat__helper.

Definition RLC_BearerConfig__reestablishRLC__F1 t :=
  match t with
  | RLC_BearerConfig__reestablishRLC__true => 0
  end.
Definition RLC_BearerConfig__reestablishRLC__F2 n :=
  match n with
  | 0 => RLC_BearerConfig__reestablishRLC__true
  | _ => RLC_BearerConfig__reestablishRLC__true
  end.
Lemma RLC_BearerConfig__reestablishRLC__F1F2 : forall x : RLC_BearerConfig__reestablishRLC__Type, (RLC_BearerConfig__reestablishRLC__F1 x <= 0) /\ RLC_BearerConfig__reestablishRLC__F2 (RLC_BearerConfig__reestablishRLC__F1 x) = x. imp_solve. Qed.
Lemma RLC_BearerConfig__reestablishRLC__F2F1 : forall (y : nat) (H : y <= 0), RLC_BearerConfig__reestablishRLC__F1 (RLC_BearerConfig__reestablishRLC__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RLC_Config.

Opaque RLC_Config__cond RLC_Config__Format.

Require Import NR.LogicalChannelConfig.

Opaque LogicalChannelConfig__cond LogicalChannelConfig__Format.

Require Import NR.RLC_Config_v1610.

Opaque RLC_Config_v1610__cond RLC_Config_v1610__Format.

Record RLC_BearerConfig__ext0O__Type : Set :=
  make__RLC_BearerConfig__ext0O__Type {
    RLC_BearerConfig__ext0O__rlc_Config_v1610 : option RLC_Config_v1610__Type ;
}.
Definition RLC_BearerConfig__ext0O__list := (
 Opt RLC_Config_v1610__Type RLC_Config_v1610__cond ::
 nil).
Definition RLC_BearerConfig__ext0O__cond z := 
  opt_cond RLC_Config_v1610__cond (RLC_BearerConfig__ext0O__rlc_Config_v1610 z) /\
  True.

Definition RLC_BearerConfig__ext0__Type := RLC_BearerConfig__ext0O__Type.
Definition RLC_BearerConfig__ext0__cond := RLC_BearerConfig__ext0O__cond.

Require Import NR.RLC_Config_v1700.

Opaque RLC_Config_v1700__cond RLC_Config_v1700__Format.

Require Import NR.LogicalChannelIdentityExt_r17.

Opaque LogicalChannelIdentityExt_r17__cond LogicalChannelIdentityExt_r17__Format.

Require Import NR.MulticastRLC_BearerConfig_r17.

Opaque MulticastRLC_BearerConfig_r17__cond MulticastRLC_BearerConfig_r17__Format.

Require Import NR.SRB_Identity_v1700.

Opaque SRB_Identity_v1700__cond SRB_Identity_v1700__Format.

Record RLC_BearerConfig__ext1O__Type : Set :=
  make__RLC_BearerConfig__ext1O__Type {
    RLC_BearerConfig__ext1O__rlc_Config_v1700 : option RLC_Config_v1700__Type ;
    RLC_BearerConfig__ext1O__logicalChannelIdentityExt_r17 : option LogicalChannelIdentityExt_r17__Type ;
    RLC_BearerConfig__ext1O__multicastRLC_BearerConfig_r17 : option MulticastRLC_BearerConfig_r17__Type ;
    RLC_BearerConfig__ext1O__servedRadioBearerSRB4_r17 : option SRB_Identity_v1700__Type ;
}.
Definition RLC_BearerConfig__ext1O__list := (
 Opt RLC_Config_v1700__Type RLC_Config_v1700__cond ::
 Opt LogicalChannelIdentityExt_r17__Type LogicalChannelIdentityExt_r17__cond ::
 Opt MulticastRLC_BearerConfig_r17__Type MulticastRLC_BearerConfig_r17__cond ::
 Opt SRB_Identity_v1700__Type SRB_Identity_v1700__cond ::
 nil).
Definition RLC_BearerConfig__ext1O__cond z := 
  opt_cond RLC_Config_v1700__cond (RLC_BearerConfig__ext1O__rlc_Config_v1700 z) /\
  opt_cond LogicalChannelIdentityExt_r17__cond (RLC_BearerConfig__ext1O__logicalChannelIdentityExt_r17 z) /\
  opt_cond MulticastRLC_BearerConfig_r17__cond (RLC_BearerConfig__ext1O__multicastRLC_BearerConfig_r17 z) /\
  opt_cond SRB_Identity_v1700__cond (RLC_BearerConfig__ext1O__servedRadioBearerSRB4_r17 z) /\
  True.

Definition RLC_BearerConfig__ext1__Type := RLC_BearerConfig__ext1O__Type.
Definition RLC_BearerConfig__ext1__cond := RLC_BearerConfig__ext1O__cond.

Record RLC_BearerConfig__Type : Set :=
  make__RLC_BearerConfig__Type {
    RLC_BearerConfig__logicalChannelIdentity : LogicalChannelIdentity__Type ;
    RLC_BearerConfig__servedRadioBearer : option RLC_BearerConfig__servedRadioBearer__Type ;
    RLC_BearerConfig__reestablishRLC : option RLC_BearerConfig__reestablishRLC__Type ;
    RLC_BearerConfig__rlc_Config : option RLC_Config__Type ;
    RLC_BearerConfig__mac_LogicalChannelConfig : option LogicalChannelConfig__Type ;
    RLC_BearerConfig__ext0 : option RLC_BearerConfig__ext0__Type ;
    RLC_BearerConfig__ext1 : option RLC_BearerConfig__ext1__Type ;
}.
Definition RLC_BearerConfig__root_list : list seq_elem := (
 Nor LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
 Opt RLC_BearerConfig__servedRadioBearer__Type RLC_BearerConfig__servedRadioBearer__cond ::
 Opt RLC_BearerConfig__reestablishRLC__Type RLC_BearerConfig__reestablishRLC__cond ::
 Opt RLC_Config__Type RLC_Config__cond ::
 Opt LogicalChannelConfig__Type LogicalChannelConfig__cond ::
 nil).
Definition RLC_BearerConfig__ext_list : list typ := (
  typ_cons RLC_BearerConfig__ext0__Type RLC_BearerConfig__ext0__cond ::
  typ_cons RLC_BearerConfig__ext1__Type RLC_BearerConfig__ext1__cond ::
  nil).
Definition RLC_BearerConfig__cond (z : RLC_BearerConfig__Type) := 
(  LogicalChannelIdentity__cond (RLC_BearerConfig__logicalChannelIdentity z) /\
  opt_cond RLC_BearerConfig__servedRadioBearer__cond (RLC_BearerConfig__servedRadioBearer z) /\
  opt_cond RLC_BearerConfig__reestablishRLC__cond (RLC_BearerConfig__reestablishRLC z) /\
  opt_cond RLC_Config__cond (RLC_BearerConfig__rlc_Config z) /\
  opt_cond LogicalChannelConfig__cond (RLC_BearerConfig__mac_LogicalChannelConfig z) /\
  True) /\ 
(  opt_cond RLC_BearerConfig__ext0__cond (RLC_BearerConfig__ext0 z) /\
  opt_cond RLC_BearerConfig__ext1__cond (RLC_BearerConfig__ext1 z) /\
  True).


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

Definition RLC_BearerConfig__servedRadioBearer__Format_Type := Eval cbn in get_formats RLC_BearerConfig__servedRadioBearer__list.
Definition RLC_BearerConfig__servedRadioBearer__Format_list : RLC_BearerConfig__servedRadioBearer__Format_Type :=
  (SRB_Identity__Format, (DRB_Identity__Format, unit__Format)).
Definition RLC_BearerConfig__servedRadioBearer__list__Format := Eval compute in choice_format RLC_BearerConfig__servedRadioBearer__list RLC_BearerConfig__servedRadioBearer__len_helper1 RLC_BearerConfig__servedRadioBearer__len_helper2  RLC_BearerConfig__servedRadioBearer__Format_list.
Definition RLC_BearerConfig__servedRadioBearer__F1 (z : RLC_BearerConfig__servedRadioBearer__Type) : (choice RLC_BearerConfig__servedRadioBearer__list) :=
  match z with
   | RLC_BearerConfig__servedRadioBearer__srb_Identity t => existT _ 0 t
  | RLC_BearerConfig__servedRadioBearer__drb_Identity t => existT _ 1 t
  end.
Definition RLC_BearerConfig__servedRadioBearer__g := (fun n => typ_set (get_nth_typ RLC_BearerConfig__servedRadioBearer__list n)).
Definition RLC_BearerConfig__servedRadioBearer__F2 (y : choice RLC_BearerConfig__servedRadioBearer__list) : RLC_BearerConfig__servedRadioBearer__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLC_BearerConfig__servedRadioBearer__g n -> RLC_BearerConfig__servedRadioBearer__Type) with
    | 0 => fun (t : SRB_Identity__Type) => RLC_BearerConfig__servedRadioBearer__srb_Identity t 
    | 1 => fun (t : DRB_Identity__Type) => RLC_BearerConfig__servedRadioBearer__drb_Identity t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLC_BearerConfig__servedRadioBearer__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLC_BearerConfig__servedRadioBearer__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLC_BearerConfig__servedRadioBearer__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLC_BearerConfig__servedRadioBearer__Type with end) n0
           end t0).

Lemma RLC_BearerConfig__servedRadioBearer__helper2 :  forall (y : RLC_BearerConfig__servedRadioBearer__Type), RLC_BearerConfig__servedRadioBearer__cond y -> choice_cond RLC_BearerConfig__servedRadioBearer__list (RLC_BearerConfig__servedRadioBearer__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLC_BearerConfig__servedRadioBearer__helper3 :  forall (y : RLC_BearerConfig__servedRadioBearer__Type), RLC_BearerConfig__servedRadioBearer__F2 (RLC_BearerConfig__servedRadioBearer__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLC_BearerConfig__servedRadioBearer__helper4 : (forall b : choice RLC_BearerConfig__servedRadioBearer__list, choice_cond RLC_BearerConfig__servedRadioBearer__list b -> RLC_BearerConfig__servedRadioBearer__cond (RLC_BearerConfig__servedRadioBearer__F2 b) /\ RLC_BearerConfig__servedRadioBearer__F1 (RLC_BearerConfig__servedRadioBearer__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLC_BearerConfig__servedRadioBearer__F1 RLC_BearerConfig__servedRadioBearer__F2.
Definition RLC_BearerConfig__servedRadioBearer__Format : T_Format RLC_BearerConfig__servedRadioBearer__Type RLC_BearerConfig__servedRadioBearer__cond :=
  (* Eval compute in *) proj2_format RLC_BearerConfig__servedRadioBearer__cond RLC_BearerConfig__servedRadioBearer__list__Format RLC_BearerConfig__servedRadioBearer__F1 RLC_BearerConfig__servedRadioBearer__F2 RLC_BearerConfig__servedRadioBearer__helper2 RLC_BearerConfig__servedRadioBearer__helper3 RLC_BearerConfig__servedRadioBearer__helper4.
Opaque RLC_BearerConfig__servedRadioBearer__cond RLC_BearerConfig__servedRadioBearer__Format.

Definition RLC_BearerConfig__reestablishRLC__Format : T_Format RLC_BearerConfig__reestablishRLC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_BearerConfig__reestablishRLC__nat__Format RLC_BearerConfig__reestablishRLC__F1 RLC_BearerConfig__reestablishRLC__F2 RLC_BearerConfig__reestablishRLC__F1F2 RLC_BearerConfig__reestablishRLC__F2F1.

Opaque RLC_BearerConfig__reestablishRLC__cond RLC_BearerConfig__reestablishRLC__Format.


Definition RLC_BearerConfig__ext0O__Format_Type := Eval cbn in seq_format_prod RLC_BearerConfig__ext0O__list.
Definition RLC_BearerConfig__ext0O__Format_list : RLC_BearerConfig__ext0O__Format_Type :=
  (RLC_Config_v1610__Format, unit_format).
Definition RLC_BearerConfig__ext0O__list__Format := (*Eval compute in *) seq_format RLC_BearerConfig__ext0O__list RLC_BearerConfig__ext0O__Format_list.
Definition RLC_BearerConfig__ext0O__F1 z :=
  (RLC_BearerConfig__ext0O__rlc_Config_v1610 z, tt).
Definition RLC_BearerConfig__ext0O__F2 (y : seq_type RLC_BearerConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RLC_BearerConfig__ext0O__Type i0
  end.
Lemma RLC_BearerConfig__ext0O__F1F2_cond (z : RLC_BearerConfig__ext0O__Type)
  : RLC_BearerConfig__ext0O__cond z ->
  (seq_cond RLC_BearerConfig__ext0O__list (RLC_BearerConfig__ext0O__F1 z)).
intro H. unfold RLC_BearerConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma RLC_BearerConfig__ext0O__F1F2_cond2 (z : RLC_BearerConfig__ext0O__Type)
 : RLC_BearerConfig__ext0O__F2 (RLC_BearerConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_BearerConfig__ext0O__F2F1_cond (y : seq_type RLC_BearerConfig__ext0O__list)
  : seq_cond RLC_BearerConfig__ext0O__list y ->
 (RLC_BearerConfig__ext0O__cond (RLC_BearerConfig__ext0O__F2 y)) /\  RLC_BearerConfig__ext0O__F1 (RLC_BearerConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_BearerConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold RLC_BearerConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_BearerConfig__ext0O__Format : T_Format RLC_BearerConfig__ext0O__Type RLC_BearerConfig__ext0O__cond :=
        proj2_format  RLC_BearerConfig__ext0O__cond RLC_BearerConfig__ext0O__list__Format
    RLC_BearerConfig__ext0O__F1 RLC_BearerConfig__ext0O__F2 RLC_BearerConfig__ext0O__F1F2_cond  RLC_BearerConfig__ext0O__F1F2_cond2 RLC_BearerConfig__ext0O__F2F1_cond.
Opaque RLC_BearerConfig__ext0O__cond RLC_BearerConfig__ext0O__Format.

Definition RLC_BearerConfig__ext0__check_all_none (b : RLC_BearerConfig__ext0O__Type) : bool :=
match b with 
  | make__RLC_BearerConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RLC_BearerConfig__ext0__Format : T_Format RLC_BearerConfig__ext0__Type RLC_BearerConfig__ext0__cond :=
  restrict_add_format RLC_BearerConfig__ext0__check_all_none RLC_BearerConfig__ext0O__Format.

Opaque RLC_BearerConfig__ext0__cond RLC_BearerConfig__ext0__Format.


Definition RLC_BearerConfig__ext1O__Format_Type := Eval cbn in seq_format_prod RLC_BearerConfig__ext1O__list.
Definition RLC_BearerConfig__ext1O__Format_list : RLC_BearerConfig__ext1O__Format_Type :=
  (RLC_Config_v1700__Format, (LogicalChannelIdentityExt_r17__Format, (MulticastRLC_BearerConfig_r17__Format, (SRB_Identity_v1700__Format, unit_format)))).
Definition RLC_BearerConfig__ext1O__list__Format := (*Eval compute in *) seq_format RLC_BearerConfig__ext1O__list RLC_BearerConfig__ext1O__Format_list.
Definition RLC_BearerConfig__ext1O__F1 z :=
  (RLC_BearerConfig__ext1O__rlc_Config_v1700 z, (RLC_BearerConfig__ext1O__logicalChannelIdentityExt_r17 z, (RLC_BearerConfig__ext1O__multicastRLC_BearerConfig_r17 z, (RLC_BearerConfig__ext1O__servedRadioBearerSRB4_r17 z, tt)))).
Definition RLC_BearerConfig__ext1O__F2 (y : seq_type RLC_BearerConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RLC_BearerConfig__ext1O__Type i0 i1 i2 i3
  end.
Lemma RLC_BearerConfig__ext1O__F1F2_cond (z : RLC_BearerConfig__ext1O__Type)
  : RLC_BearerConfig__ext1O__cond z ->
  (seq_cond RLC_BearerConfig__ext1O__list (RLC_BearerConfig__ext1O__F1 z)).
intro H. unfold RLC_BearerConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma RLC_BearerConfig__ext1O__F1F2_cond2 (z : RLC_BearerConfig__ext1O__Type)
 : RLC_BearerConfig__ext1O__F2 (RLC_BearerConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_BearerConfig__ext1O__F2F1_cond (y : seq_type RLC_BearerConfig__ext1O__list)
  : seq_cond RLC_BearerConfig__ext1O__list y ->
 (RLC_BearerConfig__ext1O__cond (RLC_BearerConfig__ext1O__F2 y)) /\  RLC_BearerConfig__ext1O__F1 (RLC_BearerConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_BearerConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold RLC_BearerConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_BearerConfig__ext1O__Format : T_Format RLC_BearerConfig__ext1O__Type RLC_BearerConfig__ext1O__cond :=
        proj2_format  RLC_BearerConfig__ext1O__cond RLC_BearerConfig__ext1O__list__Format
    RLC_BearerConfig__ext1O__F1 RLC_BearerConfig__ext1O__F2 RLC_BearerConfig__ext1O__F1F2_cond  RLC_BearerConfig__ext1O__F1F2_cond2 RLC_BearerConfig__ext1O__F2F1_cond.
Opaque RLC_BearerConfig__ext1O__cond RLC_BearerConfig__ext1O__Format.

Definition RLC_BearerConfig__ext1__check_all_none (b : RLC_BearerConfig__ext1O__Type) : bool :=
match b with 
  | make__RLC_BearerConfig__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition RLC_BearerConfig__ext1__Format : T_Format RLC_BearerConfig__ext1__Type RLC_BearerConfig__ext1__cond :=
  restrict_add_format RLC_BearerConfig__ext1__check_all_none RLC_BearerConfig__ext1O__Format.

Opaque RLC_BearerConfig__ext1__cond RLC_BearerConfig__ext1__Format.


Definition RLC_BearerConfig__root_Format_Type := Eval cbn in seq_format_prod RLC_BearerConfig__root_list.
Definition RLC_BearerConfig__root_Format_list : RLC_BearerConfig__root_Format_Type :=
  (LogicalChannelIdentity__Format, (RLC_BearerConfig__servedRadioBearer__Format, (RLC_BearerConfig__reestablishRLC__Format, (RLC_Config__Format, (LogicalChannelConfig__Format, unit_format))))).

Definition RLC_BearerConfig__ext_Format_Type := Eval cbn in get_formats RLC_BearerConfig__ext_list.
Definition RLC_BearerConfig__ext_Format_list : RLC_BearerConfig__ext_Format_Type :=
  (RLC_BearerConfig__ext0__Format, (RLC_BearerConfig__ext1__Format, unit__Format)).

Definition RLC_BearerConfig__list_type : Set := (seq_type RLC_BearerConfig__root_list) * (seq_ext_type RLC_BearerConfig__ext_list).
Definition RLC_BearerConfig__list_cond (z : RLC_BearerConfig__list_type) : Prop :=
        (seq_cond RLC_BearerConfig__root_list (fst z)) /\ (seq_ext_cond RLC_BearerConfig__ext_list (snd z)).
Definition RLC_BearerConfig__list_format : T_Format RLC_BearerConfig__list_type RLC_BearerConfig__list_cond :=
 (* Eval compute in *) seq_ext_format RLC_BearerConfig__root_list RLC_BearerConfig__root_Format_list RLC_BearerConfig__ext_list RLC_BearerConfig__ext_Format_list.

Opaque RLC_BearerConfig__list_format.
Definition RLC_BearerConfig__F1 (z : RLC_BearerConfig__Type) : RLC_BearerConfig__list_type :=
  (((RLC_BearerConfig__logicalChannelIdentity z, (RLC_BearerConfig__servedRadioBearer z, (RLC_BearerConfig__reestablishRLC z, (RLC_BearerConfig__rlc_Config z, (RLC_BearerConfig__mac_LogicalChannelConfig z, tt)))))), (
(RLC_BearerConfig__ext0 z, (RLC_BearerConfig__ext1 z, tt)))).
Definition RLC_BearerConfig__F2 (y : RLC_BearerConfig__list_type) : RLC_BearerConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, _)))=>
    make__RLC_BearerConfig__Type j0 j1 j2 j3 j4 i0 i1
  end.
Definition RLC_BearerConfig__helper1 : (forall a : RLC_BearerConfig__Type, RLC_BearerConfig__cond a -> RLC_BearerConfig__list_cond (RLC_BearerConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RLC_BearerConfig__helper2 : (forall a : RLC_BearerConfig__Type, RLC_BearerConfig__F2 (RLC_BearerConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RLC_BearerConfig__helper3 : (forall b : RLC_BearerConfig__list_type, RLC_BearerConfig__list_cond b -> RLC_BearerConfig__cond (RLC_BearerConfig__F2 b) /\ RLC_BearerConfig__F1 (RLC_BearerConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RLC_BearerConfig__cond, RLC_BearerConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RLC_BearerConfig__Format : T_Format RLC_BearerConfig__Type RLC_BearerConfig__cond :=
 proj2_format RLC_BearerConfig__cond RLC_BearerConfig__list_format  RLC_BearerConfig__F1 RLC_BearerConfig__F2 RLC_BearerConfig__helper1 RLC_BearerConfig__helper2 RLC_BearerConfig__helper3.

Opaque RLC_BearerConfig__cond RLC_BearerConfig__Format.

