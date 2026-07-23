Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasConfigAppLayerId_r17.

Opaque MeasConfigAppLayerId_r17__cond MeasConfigAppLayerId_r17__Format.

Lemma MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__helper1 : (0 <= 1 <= 8000)%Z.  lia. Qed.
Lemma MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__helper2 : to_bit_sz (Z.to_nat (8000 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8000 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Type := octet_string.
Definition MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__cond := (fun bs : octet_string => (1 <= Z.of_nat (length bs) <= 8000)%Z).
Inductive MeasConfigAppLayer_r17__serviceType_r17__Type : Set :=
 | MeasConfigAppLayer_r17__serviceType_r17__streaming
 | MeasConfigAppLayer_r17__serviceType_r17__mtsi
 | MeasConfigAppLayer_r17__serviceType_r17__vr
 | MeasConfigAppLayer_r17__serviceType_r17__spare5
 | MeasConfigAppLayer_r17__serviceType_r17__spare4
 | MeasConfigAppLayer_r17__serviceType_r17__spare3
 | MeasConfigAppLayer_r17__serviceType_r17__spare2
 | MeasConfigAppLayer_r17__serviceType_r17__spare1
.
Definition MeasConfigAppLayer_r17__serviceType_r17__cond := (fun (_ : MeasConfigAppLayer_r17__serviceType_r17__Type) => True).
Lemma MeasConfigAppLayer_r17__serviceType_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasConfigAppLayer_r17__serviceType_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MeasConfigAppLayer_r17__serviceType_r17__nat__helper.

Definition MeasConfigAppLayer_r17__serviceType_r17__F1 t :=
  match t with
  | MeasConfigAppLayer_r17__serviceType_r17__streaming => 0
  | MeasConfigAppLayer_r17__serviceType_r17__mtsi => 1
  | MeasConfigAppLayer_r17__serviceType_r17__vr => 2
  | MeasConfigAppLayer_r17__serviceType_r17__spare5 => 3
  | MeasConfigAppLayer_r17__serviceType_r17__spare4 => 4
  | MeasConfigAppLayer_r17__serviceType_r17__spare3 => 5
  | MeasConfigAppLayer_r17__serviceType_r17__spare2 => 6
  | MeasConfigAppLayer_r17__serviceType_r17__spare1 => 7
  end.
Definition MeasConfigAppLayer_r17__serviceType_r17__F2 n :=
  match n with
  | 0 => MeasConfigAppLayer_r17__serviceType_r17__streaming
  | 1 => MeasConfigAppLayer_r17__serviceType_r17__mtsi
  | 2 => MeasConfigAppLayer_r17__serviceType_r17__vr
  | 3 => MeasConfigAppLayer_r17__serviceType_r17__spare5
  | 4 => MeasConfigAppLayer_r17__serviceType_r17__spare4
  | 5 => MeasConfigAppLayer_r17__serviceType_r17__spare3
  | 6 => MeasConfigAppLayer_r17__serviceType_r17__spare2
  | 7 => MeasConfigAppLayer_r17__serviceType_r17__spare1
  | _ => MeasConfigAppLayer_r17__serviceType_r17__streaming
  end.
Lemma MeasConfigAppLayer_r17__serviceType_r17__F1F2 : forall x : MeasConfigAppLayer_r17__serviceType_r17__Type, (MeasConfigAppLayer_r17__serviceType_r17__F1 x <= 7) /\ MeasConfigAppLayer_r17__serviceType_r17__F2 (MeasConfigAppLayer_r17__serviceType_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasConfigAppLayer_r17__serviceType_r17__F2F1 : forall (y : nat) (H : y <= 7), MeasConfigAppLayer_r17__serviceType_r17__F1 (MeasConfigAppLayer_r17__serviceType_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.RAN_VisibleParameters_r17.
Definition MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Type := SetupRelease__Type RAN_VisibleParameters_r17__Type.
Definition MeasConfigAppLayer_r17__ran_VisibleParameters_r17__cond := SetupRelease__cond _ RAN_VisibleParameters_r17__cond.
Definition MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Format : T_Format MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Type MeasConfigAppLayer_r17__ran_VisibleParameters_r17__cond := SetupRelease__Format _ _ RAN_VisibleParameters_r17__Format.
Opaque MeasConfigAppLayer_r17__ran_VisibleParameters_r17__cond MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Format.

Record MeasConfigAppLayer_r17__Type : Set :=
  make__MeasConfigAppLayer_r17__Type {
    MeasConfigAppLayer_r17__measConfigAppLayerId_r17 : MeasConfigAppLayerId_r17__Type ;
    MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17 : option MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Type ;
    MeasConfigAppLayer_r17__serviceType_r17 : option MeasConfigAppLayer_r17__serviceType_r17__Type ;
    MeasConfigAppLayer_r17__pauseReporting_r17 : option bool ;
    MeasConfigAppLayer_r17__transmissionOfSessionStartStop_r17 : option bool ;
    MeasConfigAppLayer_r17__ran_VisibleParameters_r17 : option MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Type ;
}.
Definition MeasConfigAppLayer_r17__root_list : list seq_elem := (
 Nor MeasConfigAppLayerId_r17__Type MeasConfigAppLayerId_r17__cond ::
 Opt MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Type MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__cond ::
 Opt MeasConfigAppLayer_r17__serviceType_r17__Type MeasConfigAppLayer_r17__serviceType_r17__cond ::
 Opt bool (fun _ => True) ::
 Opt bool (fun _ => True) ::
 Opt MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Type MeasConfigAppLayer_r17__ran_VisibleParameters_r17__cond ::
 nil).
Definition MeasConfigAppLayer_r17__ext_list : list typ := (
  nil).
Definition MeasConfigAppLayer_r17__cond (z : MeasConfigAppLayer_r17__Type) := 
(  MeasConfigAppLayerId_r17__cond (MeasConfigAppLayer_r17__measConfigAppLayerId_r17 z) /\
  opt_cond MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__cond (MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17 z) /\
  opt_cond MeasConfigAppLayer_r17__serviceType_r17__cond (MeasConfigAppLayer_r17__serviceType_r17 z) /\
  opt_cond (fun _ => True) (MeasConfigAppLayer_r17__pauseReporting_r17 z) /\
  opt_cond (fun _ => True) (MeasConfigAppLayer_r17__transmissionOfSessionStartStop_r17 z) /\
  opt_cond MeasConfigAppLayer_r17__ran_VisibleParameters_r17__cond (MeasConfigAppLayer_r17__ran_VisibleParameters_r17 z) /\
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
Definition MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Format : T_Format MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Type MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__cond := (* Eval compute in *) octet_string_ranged_format 1 8000 MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__helper1 MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__helper2.
Opaque MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__cond MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Format.

Definition MeasConfigAppLayer_r17__serviceType_r17__Format : T_Format MeasConfigAppLayer_r17__serviceType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasConfigAppLayer_r17__serviceType_r17__nat__Format MeasConfigAppLayer_r17__serviceType_r17__F1 MeasConfigAppLayer_r17__serviceType_r17__F2 MeasConfigAppLayer_r17__serviceType_r17__F1F2 MeasConfigAppLayer_r17__serviceType_r17__F2F1.

Opaque MeasConfigAppLayer_r17__serviceType_r17__cond MeasConfigAppLayer_r17__serviceType_r17__Format.

Opaque MeasConfigAppLayer_r17__ran_VisibleParameters_r17__cond MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Format.


Definition MeasConfigAppLayer_r17__root_Format_Type := Eval cbn in seq_format_prod MeasConfigAppLayer_r17__root_list.
Definition MeasConfigAppLayer_r17__root_Format_list : MeasConfigAppLayer_r17__root_Format_Type :=
  (MeasConfigAppLayerId_r17__Format, (MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17__Format, (MeasConfigAppLayer_r17__serviceType_r17__Format, (bool__Format, (bool__Format, (MeasConfigAppLayer_r17__ran_VisibleParameters_r17__Format, unit_format)))))).

Definition MeasConfigAppLayer_r17__ext_Format_Type := Eval cbn in get_formats MeasConfigAppLayer_r17__ext_list.
Definition MeasConfigAppLayer_r17__ext_Format_list : MeasConfigAppLayer_r17__ext_Format_Type :=
  unit__Format.

Definition MeasConfigAppLayer_r17__list_type : Set := (seq_type MeasConfigAppLayer_r17__root_list) * (seq_ext_type MeasConfigAppLayer_r17__ext_list).
Definition MeasConfigAppLayer_r17__list_cond (z : MeasConfigAppLayer_r17__list_type) : Prop :=
        (seq_cond MeasConfigAppLayer_r17__root_list (fst z)) /\ (seq_ext_cond MeasConfigAppLayer_r17__ext_list (snd z)).
Definition MeasConfigAppLayer_r17__list_format : T_Format MeasConfigAppLayer_r17__list_type MeasConfigAppLayer_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MeasConfigAppLayer_r17__root_list MeasConfigAppLayer_r17__root_Format_list MeasConfigAppLayer_r17__ext_list MeasConfigAppLayer_r17__ext_Format_list.

Opaque MeasConfigAppLayer_r17__list_format.
Definition MeasConfigAppLayer_r17__F1 (z : MeasConfigAppLayer_r17__Type) : MeasConfigAppLayer_r17__list_type :=
  (((MeasConfigAppLayer_r17__measConfigAppLayerId_r17 z, (MeasConfigAppLayer_r17__measConfigAppLayerContainer_r17 z, (MeasConfigAppLayer_r17__serviceType_r17 z, (MeasConfigAppLayer_r17__pauseReporting_r17 z, (MeasConfigAppLayer_r17__transmissionOfSessionStartStop_r17 z, (MeasConfigAppLayer_r17__ran_VisibleParameters_r17 z, tt))))))), (
tt)).
Definition MeasConfigAppLayer_r17__F2 (y : MeasConfigAppLayer_r17__list_type) : MeasConfigAppLayer_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__MeasConfigAppLayer_r17__Type j0 j1 j2 j3 j4 j5
  end.
Definition MeasConfigAppLayer_r17__helper1 : (forall a : MeasConfigAppLayer_r17__Type, MeasConfigAppLayer_r17__cond a -> MeasConfigAppLayer_r17__list_cond (MeasConfigAppLayer_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasConfigAppLayer_r17__helper2 : (forall a : MeasConfigAppLayer_r17__Type, MeasConfigAppLayer_r17__F2 (MeasConfigAppLayer_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasConfigAppLayer_r17__helper3 : (forall b : MeasConfigAppLayer_r17__list_type, MeasConfigAppLayer_r17__list_cond b -> MeasConfigAppLayer_r17__cond (MeasConfigAppLayer_r17__F2 b) /\ MeasConfigAppLayer_r17__F1 (MeasConfigAppLayer_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasConfigAppLayer_r17__cond, MeasConfigAppLayer_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasConfigAppLayer_r17__Format : T_Format MeasConfigAppLayer_r17__Type MeasConfigAppLayer_r17__cond :=
 proj2_format MeasConfigAppLayer_r17__cond MeasConfigAppLayer_r17__list_format  MeasConfigAppLayer_r17__F1 MeasConfigAppLayer_r17__F2 MeasConfigAppLayer_r17__helper1 MeasConfigAppLayer_r17__helper2 MeasConfigAppLayer_r17__helper3.

Opaque MeasConfigAppLayer_r17__cond MeasConfigAppLayer_r17__Format.

