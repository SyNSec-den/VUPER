Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RACH_ConfigGeneric.

Opaque RACH_ConfigGeneric__cond RACH_ConfigGeneric__Format.

Inductive SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Type : Set :=
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneEighth
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneFourth
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneHalf
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__one
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__two
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__four
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__eight
 | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__sixteen
.
Definition SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__cond := (fun (_ : SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Type) => True).
Lemma SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__nat__helper.

Definition SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1 t :=
  match t with
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneEighth => 0
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneFourth => 1
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneHalf => 2
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__one => 3
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__two => 4
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__four => 5
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__eight => 6
  | SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__sixteen => 7
  end.
Definition SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F2 n :=
  match n with
  | 0 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneEighth
  | 1 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneFourth
  | 2 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneHalf
  | 3 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__one
  | 4 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__two
  | 5 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__four
  | 6 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__eight
  | 7 => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__sixteen
  | _ => SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__oneEighth
  end.
Lemma SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1F2 : forall x : SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Type, (SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1 x <= 7) /\ SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F2 (SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1 x) = x. imp_solve. Qed.
Lemma SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F2F1 : forall (y : nat) (H : y <= 7), SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1 (SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F2 y) = y. enum_solve H y. Qed.

Record SI_RequestConfig__rach_OccasionsSI__Type : Set :=
  make__SI_RequestConfig__rach_OccasionsSI__Type {
    SI_RequestConfig__rach_OccasionsSI__rach_ConfigSI : RACH_ConfigGeneric__Type ;
    SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion : SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Type ;
}.
Definition SI_RequestConfig__rach_OccasionsSI__list := (
 Nor RACH_ConfigGeneric__Type RACH_ConfigGeneric__cond ::
 Nor SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Type SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__cond ::
 nil).
Definition SI_RequestConfig__rach_OccasionsSI__cond z := 
  RACH_ConfigGeneric__cond (SI_RequestConfig__rach_OccasionsSI__rach_ConfigSI z) /\
  SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__cond (SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion z) /\
  True.

Inductive SI_RequestConfig__si_RequestPeriod__Type : Set :=
 | SI_RequestConfig__si_RequestPeriod__one
 | SI_RequestConfig__si_RequestPeriod__two
 | SI_RequestConfig__si_RequestPeriod__four
 | SI_RequestConfig__si_RequestPeriod__six
 | SI_RequestConfig__si_RequestPeriod__eight
 | SI_RequestConfig__si_RequestPeriod__ten
 | SI_RequestConfig__si_RequestPeriod__twelve
 | SI_RequestConfig__si_RequestPeriod__sixteen
.
Definition SI_RequestConfig__si_RequestPeriod__cond := (fun (_ : SI_RequestConfig__si_RequestPeriod__Type) => True).
Lemma SI_RequestConfig__si_RequestPeriod__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SI_RequestConfig__si_RequestPeriod__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SI_RequestConfig__si_RequestPeriod__nat__helper.

Definition SI_RequestConfig__si_RequestPeriod__F1 t :=
  match t with
  | SI_RequestConfig__si_RequestPeriod__one => 0
  | SI_RequestConfig__si_RequestPeriod__two => 1
  | SI_RequestConfig__si_RequestPeriod__four => 2
  | SI_RequestConfig__si_RequestPeriod__six => 3
  | SI_RequestConfig__si_RequestPeriod__eight => 4
  | SI_RequestConfig__si_RequestPeriod__ten => 5
  | SI_RequestConfig__si_RequestPeriod__twelve => 6
  | SI_RequestConfig__si_RequestPeriod__sixteen => 7
  end.
Definition SI_RequestConfig__si_RequestPeriod__F2 n :=
  match n with
  | 0 => SI_RequestConfig__si_RequestPeriod__one
  | 1 => SI_RequestConfig__si_RequestPeriod__two
  | 2 => SI_RequestConfig__si_RequestPeriod__four
  | 3 => SI_RequestConfig__si_RequestPeriod__six
  | 4 => SI_RequestConfig__si_RequestPeriod__eight
  | 5 => SI_RequestConfig__si_RequestPeriod__ten
  | 6 => SI_RequestConfig__si_RequestPeriod__twelve
  | 7 => SI_RequestConfig__si_RequestPeriod__sixteen
  | _ => SI_RequestConfig__si_RequestPeriod__one
  end.
Lemma SI_RequestConfig__si_RequestPeriod__F1F2 : forall x : SI_RequestConfig__si_RequestPeriod__Type, (SI_RequestConfig__si_RequestPeriod__F1 x <= 7) /\ SI_RequestConfig__si_RequestPeriod__F2 (SI_RequestConfig__si_RequestPeriod__F1 x) = x. imp_solve. Qed.
Lemma SI_RequestConfig__si_RequestPeriod__F2F1 : forall (y : nat) (H : y <= 7), SI_RequestConfig__si_RequestPeriod__F1 (SI_RequestConfig__si_RequestPeriod__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SI_RequestResources.

Opaque SI_RequestResources__cond SI_RequestResources__Format.

Definition SI_RequestConfig__si_RequestResources__Type := list SI_RequestResources__Type.

Lemma SI_RequestConfig__si_RequestResources__helper1 : (0 <= 1 <= maxSI_Message)%Z. unfold maxSI_Message.
 lia. Qed.
Lemma SI_RequestConfig__si_RequestResources__helper2 : to_bit_sz (Z.to_nat (maxSI_Message - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSI_Message - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SI_RequestConfig__si_RequestResources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SI_RequestConfig__si_RequestResources__cond (z : SI_RequestConfig__si_RequestResources__Type) :=  (1 <= Z.of_nat (length z) <= maxSI_Message)%Z /\ (list_and SI_RequestResources__cond z) .

Record SI_RequestConfig__Type : Set :=
  make__SI_RequestConfig__Type {
    SI_RequestConfig__rach_OccasionsSI : option SI_RequestConfig__rach_OccasionsSI__Type ;
    SI_RequestConfig__si_RequestPeriod : option SI_RequestConfig__si_RequestPeriod__Type ;
    SI_RequestConfig__si_RequestResources : SI_RequestConfig__si_RequestResources__Type ;
}.
Definition SI_RequestConfig__list := (
 Opt SI_RequestConfig__rach_OccasionsSI__Type SI_RequestConfig__rach_OccasionsSI__cond ::
 Opt SI_RequestConfig__si_RequestPeriod__Type SI_RequestConfig__si_RequestPeriod__cond ::
 Nor SI_RequestConfig__si_RequestResources__Type SI_RequestConfig__si_RequestResources__cond ::
 nil).
Definition SI_RequestConfig__cond z := 
  opt_cond SI_RequestConfig__rach_OccasionsSI__cond (SI_RequestConfig__rach_OccasionsSI z) /\
  opt_cond SI_RequestConfig__si_RequestPeriod__cond (SI_RequestConfig__si_RequestPeriod z) /\
  SI_RequestConfig__si_RequestResources__cond (SI_RequestConfig__si_RequestResources z) /\
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
Definition SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Format : T_Format SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__nat__Format SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1 SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F2 SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F1F2 SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__F2F1.

Opaque SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__cond SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Format.


Definition SI_RequestConfig__rach_OccasionsSI__Format_Type := Eval cbn in seq_format_prod SI_RequestConfig__rach_OccasionsSI__list.
Definition SI_RequestConfig__rach_OccasionsSI__Format_list : SI_RequestConfig__rach_OccasionsSI__Format_Type :=
  (RACH_ConfigGeneric__Format, (SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion__Format, unit_format)).
Definition SI_RequestConfig__rach_OccasionsSI__list__Format := (*Eval compute in *) seq_format SI_RequestConfig__rach_OccasionsSI__list SI_RequestConfig__rach_OccasionsSI__Format_list.
Definition SI_RequestConfig__rach_OccasionsSI__F1 z :=
  (SI_RequestConfig__rach_OccasionsSI__rach_ConfigSI z, (SI_RequestConfig__rach_OccasionsSI__ssb_perRACH_Occasion z, tt)).
Definition SI_RequestConfig__rach_OccasionsSI__F2 (y : seq_type SI_RequestConfig__rach_OccasionsSI__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SI_RequestConfig__rach_OccasionsSI__Type i0 i1
  end.
Lemma SI_RequestConfig__rach_OccasionsSI__F1F2_cond (z : SI_RequestConfig__rach_OccasionsSI__Type)
  : SI_RequestConfig__rach_OccasionsSI__cond z ->
  (seq_cond SI_RequestConfig__rach_OccasionsSI__list (SI_RequestConfig__rach_OccasionsSI__F1 z)).
intro H. unfold SI_RequestConfig__rach_OccasionsSI__cond in H. simpl. auto. Qed.
Lemma SI_RequestConfig__rach_OccasionsSI__F1F2_cond2 (z : SI_RequestConfig__rach_OccasionsSI__Type)
 : SI_RequestConfig__rach_OccasionsSI__F2 (SI_RequestConfig__rach_OccasionsSI__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SI_RequestConfig__rach_OccasionsSI__F2F1_cond (y : seq_type SI_RequestConfig__rach_OccasionsSI__list)
  : seq_cond SI_RequestConfig__rach_OccasionsSI__list y ->
 (SI_RequestConfig__rach_OccasionsSI__cond (SI_RequestConfig__rach_OccasionsSI__F2 y)) /\  SI_RequestConfig__rach_OccasionsSI__F1 (SI_RequestConfig__rach_OccasionsSI__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SI_RequestConfig__rach_OccasionsSI__cond. simpl in *. auto.
 - simpl. unfold SI_RequestConfig__rach_OccasionsSI__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SI_RequestConfig__rach_OccasionsSI__Format : T_Format SI_RequestConfig__rach_OccasionsSI__Type SI_RequestConfig__rach_OccasionsSI__cond :=
        proj2_format  SI_RequestConfig__rach_OccasionsSI__cond SI_RequestConfig__rach_OccasionsSI__list__Format
    SI_RequestConfig__rach_OccasionsSI__F1 SI_RequestConfig__rach_OccasionsSI__F2 SI_RequestConfig__rach_OccasionsSI__F1F2_cond  SI_RequestConfig__rach_OccasionsSI__F1F2_cond2 SI_RequestConfig__rach_OccasionsSI__F2F1_cond.
Opaque SI_RequestConfig__rach_OccasionsSI__cond SI_RequestConfig__rach_OccasionsSI__Format.

Definition SI_RequestConfig__si_RequestPeriod__Format : T_Format SI_RequestConfig__si_RequestPeriod__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SI_RequestConfig__si_RequestPeriod__nat__Format SI_RequestConfig__si_RequestPeriod__F1 SI_RequestConfig__si_RequestPeriod__F2 SI_RequestConfig__si_RequestPeriod__F1F2 SI_RequestConfig__si_RequestPeriod__F2F1.

Opaque SI_RequestConfig__si_RequestPeriod__cond SI_RequestConfig__si_RequestPeriod__Format.

Definition SI_RequestConfig__si_RequestResources__Format : T_Format SI_RequestConfig__si_RequestResources__Type SI_RequestConfig__si_RequestResources__cond := seq_of_format SI_RequestResources__Format 1 maxSI_Message SI_RequestConfig__si_RequestResources__helper1 SI_RequestConfig__si_RequestResources__helper2.

Opaque SI_RequestConfig__si_RequestResources__cond SI_RequestConfig__si_RequestResources__Format.


Definition SI_RequestConfig__Format_Type := Eval cbn in seq_format_prod SI_RequestConfig__list.
Definition SI_RequestConfig__Format_list : SI_RequestConfig__Format_Type :=
  (SI_RequestConfig__rach_OccasionsSI__Format, (SI_RequestConfig__si_RequestPeriod__Format, (SI_RequestConfig__si_RequestResources__Format, unit_format))).
Definition SI_RequestConfig__list__Format := (*Eval compute in *) seq_format SI_RequestConfig__list SI_RequestConfig__Format_list.
Definition SI_RequestConfig__F1 z :=
  (SI_RequestConfig__rach_OccasionsSI z, (SI_RequestConfig__si_RequestPeriod z, (SI_RequestConfig__si_RequestResources z, tt))).
Definition SI_RequestConfig__F2 (y : seq_type SI_RequestConfig__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SI_RequestConfig__Type i0 i1 i2
  end.
Lemma SI_RequestConfig__F1F2_cond (z : SI_RequestConfig__Type)
  : SI_RequestConfig__cond z ->
  (seq_cond SI_RequestConfig__list (SI_RequestConfig__F1 z)).
intro H. unfold SI_RequestConfig__cond in H. simpl. auto. Qed.
Lemma SI_RequestConfig__F1F2_cond2 (z : SI_RequestConfig__Type)
 : SI_RequestConfig__F2 (SI_RequestConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SI_RequestConfig__F2F1_cond (y : seq_type SI_RequestConfig__list)
  : seq_cond SI_RequestConfig__list y ->
 (SI_RequestConfig__cond (SI_RequestConfig__F2 y)) /\  SI_RequestConfig__F1 (SI_RequestConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SI_RequestConfig__cond. simpl in *. auto.
 - simpl. unfold SI_RequestConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SI_RequestConfig__Format : T_Format SI_RequestConfig__Type SI_RequestConfig__cond :=
        proj2_format  SI_RequestConfig__cond SI_RequestConfig__list__Format
    SI_RequestConfig__F1 SI_RequestConfig__F2 SI_RequestConfig__F1F2_cond  SI_RequestConfig__F1F2_cond2 SI_RequestConfig__F2F1_cond.
Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

