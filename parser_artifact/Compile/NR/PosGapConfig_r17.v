Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasPosPreConfigGapId_r17.

Opaque MeasPosPreConfigGapId_r17__cond MeasPosPreConfigGapId_r17__Format.

Lemma PosGapConfig_r17__gapOffset_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma PosGapConfig_r17__gapOffset_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PosGapConfig_r17__gapOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PosGapConfig_r17__gapOffset_r17__Type := Z.
Definition PosGapConfig_r17__gapOffset_r17__cond := (fun z => (0 <= z <= 159)%Z).
Inductive PosGapConfig_r17__mgl_r17__Type : Set :=
 | PosGapConfig_r17__mgl_r17__ms1dot5
 | PosGapConfig_r17__mgl_r17__ms3
 | PosGapConfig_r17__mgl_r17__ms3dot5
 | PosGapConfig_r17__mgl_r17__ms4
 | PosGapConfig_r17__mgl_r17__ms5dot5
 | PosGapConfig_r17__mgl_r17__ms6
 | PosGapConfig_r17__mgl_r17__ms10
 | PosGapConfig_r17__mgl_r17__ms20
.
Definition PosGapConfig_r17__mgl_r17__cond := (fun (_ : PosGapConfig_r17__mgl_r17__Type) => True).
Lemma PosGapConfig_r17__mgl_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosGapConfig_r17__mgl_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PosGapConfig_r17__mgl_r17__nat__helper.

Definition PosGapConfig_r17__mgl_r17__F1 t :=
  match t with
  | PosGapConfig_r17__mgl_r17__ms1dot5 => 0
  | PosGapConfig_r17__mgl_r17__ms3 => 1
  | PosGapConfig_r17__mgl_r17__ms3dot5 => 2
  | PosGapConfig_r17__mgl_r17__ms4 => 3
  | PosGapConfig_r17__mgl_r17__ms5dot5 => 4
  | PosGapConfig_r17__mgl_r17__ms6 => 5
  | PosGapConfig_r17__mgl_r17__ms10 => 6
  | PosGapConfig_r17__mgl_r17__ms20 => 7
  end.
Definition PosGapConfig_r17__mgl_r17__F2 n :=
  match n with
  | 0 => PosGapConfig_r17__mgl_r17__ms1dot5
  | 1 => PosGapConfig_r17__mgl_r17__ms3
  | 2 => PosGapConfig_r17__mgl_r17__ms3dot5
  | 3 => PosGapConfig_r17__mgl_r17__ms4
  | 4 => PosGapConfig_r17__mgl_r17__ms5dot5
  | 5 => PosGapConfig_r17__mgl_r17__ms6
  | 6 => PosGapConfig_r17__mgl_r17__ms10
  | 7 => PosGapConfig_r17__mgl_r17__ms20
  | _ => PosGapConfig_r17__mgl_r17__ms1dot5
  end.
Lemma PosGapConfig_r17__mgl_r17__F1F2 : forall x : PosGapConfig_r17__mgl_r17__Type, (PosGapConfig_r17__mgl_r17__F1 x <= 7) /\ PosGapConfig_r17__mgl_r17__F2 (PosGapConfig_r17__mgl_r17__F1 x) = x. imp_solve. Qed.
Lemma PosGapConfig_r17__mgl_r17__F2F1 : forall (y : nat) (H : y <= 7), PosGapConfig_r17__mgl_r17__F1 (PosGapConfig_r17__mgl_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PosGapConfig_r17__mgrp_r17__Type : Set :=
 | PosGapConfig_r17__mgrp_r17__ms20
 | PosGapConfig_r17__mgrp_r17__ms40
 | PosGapConfig_r17__mgrp_r17__ms80
 | PosGapConfig_r17__mgrp_r17__ms160
.
Definition PosGapConfig_r17__mgrp_r17__cond := (fun (_ : PosGapConfig_r17__mgrp_r17__Type) => True).
Lemma PosGapConfig_r17__mgrp_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosGapConfig_r17__mgrp_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PosGapConfig_r17__mgrp_r17__nat__helper.

Definition PosGapConfig_r17__mgrp_r17__F1 t :=
  match t with
  | PosGapConfig_r17__mgrp_r17__ms20 => 0
  | PosGapConfig_r17__mgrp_r17__ms40 => 1
  | PosGapConfig_r17__mgrp_r17__ms80 => 2
  | PosGapConfig_r17__mgrp_r17__ms160 => 3
  end.
Definition PosGapConfig_r17__mgrp_r17__F2 n :=
  match n with
  | 0 => PosGapConfig_r17__mgrp_r17__ms20
  | 1 => PosGapConfig_r17__mgrp_r17__ms40
  | 2 => PosGapConfig_r17__mgrp_r17__ms80
  | 3 => PosGapConfig_r17__mgrp_r17__ms160
  | _ => PosGapConfig_r17__mgrp_r17__ms20
  end.
Lemma PosGapConfig_r17__mgrp_r17__F1F2 : forall x : PosGapConfig_r17__mgrp_r17__Type, (PosGapConfig_r17__mgrp_r17__F1 x <= 3) /\ PosGapConfig_r17__mgrp_r17__F2 (PosGapConfig_r17__mgrp_r17__F1 x) = x. imp_solve. Qed.
Lemma PosGapConfig_r17__mgrp_r17__F2F1 : forall (y : nat) (H : y <= 3), PosGapConfig_r17__mgrp_r17__F1 (PosGapConfig_r17__mgrp_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PosGapConfig_r17__mgta_r17__Type : Set :=
 | PosGapConfig_r17__mgta_r17__ms0
 | PosGapConfig_r17__mgta_r17__ms0dot25
 | PosGapConfig_r17__mgta_r17__ms0dot5
.
Definition PosGapConfig_r17__mgta_r17__cond := (fun (_ : PosGapConfig_r17__mgta_r17__Type) => True).
Lemma PosGapConfig_r17__mgta_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosGapConfig_r17__mgta_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PosGapConfig_r17__mgta_r17__nat__helper.

Definition PosGapConfig_r17__mgta_r17__F1 t :=
  match t with
  | PosGapConfig_r17__mgta_r17__ms0 => 0
  | PosGapConfig_r17__mgta_r17__ms0dot25 => 1
  | PosGapConfig_r17__mgta_r17__ms0dot5 => 2
  end.
Definition PosGapConfig_r17__mgta_r17__F2 n :=
  match n with
  | 0 => PosGapConfig_r17__mgta_r17__ms0
  | 1 => PosGapConfig_r17__mgta_r17__ms0dot25
  | 2 => PosGapConfig_r17__mgta_r17__ms0dot5
  | _ => PosGapConfig_r17__mgta_r17__ms0
  end.
Lemma PosGapConfig_r17__mgta_r17__F1F2 : forall x : PosGapConfig_r17__mgta_r17__Type, (PosGapConfig_r17__mgta_r17__F1 x <= 2) /\ PosGapConfig_r17__mgta_r17__F2 (PosGapConfig_r17__mgta_r17__F1 x) = x. imp_solve. Qed.
Lemma PosGapConfig_r17__mgta_r17__F2F1 : forall (y : nat) (H : y <= 2), PosGapConfig_r17__mgta_r17__F1 (PosGapConfig_r17__mgta_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PosGapConfig_r17__gapType_r17__Type : Set :=
 | PosGapConfig_r17__gapType_r17__perUE
 | PosGapConfig_r17__gapType_r17__perFR1
 | PosGapConfig_r17__gapType_r17__perFR2
.
Definition PosGapConfig_r17__gapType_r17__cond := (fun (_ : PosGapConfig_r17__gapType_r17__Type) => True).
Lemma PosGapConfig_r17__gapType_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosGapConfig_r17__gapType_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PosGapConfig_r17__gapType_r17__nat__helper.

Definition PosGapConfig_r17__gapType_r17__F1 t :=
  match t with
  | PosGapConfig_r17__gapType_r17__perUE => 0
  | PosGapConfig_r17__gapType_r17__perFR1 => 1
  | PosGapConfig_r17__gapType_r17__perFR2 => 2
  end.
Definition PosGapConfig_r17__gapType_r17__F2 n :=
  match n with
  | 0 => PosGapConfig_r17__gapType_r17__perUE
  | 1 => PosGapConfig_r17__gapType_r17__perFR1
  | 2 => PosGapConfig_r17__gapType_r17__perFR2
  | _ => PosGapConfig_r17__gapType_r17__perUE
  end.
Lemma PosGapConfig_r17__gapType_r17__F1F2 : forall x : PosGapConfig_r17__gapType_r17__Type, (PosGapConfig_r17__gapType_r17__F1 x <= 2) /\ PosGapConfig_r17__gapType_r17__F2 (PosGapConfig_r17__gapType_r17__F1 x) = x. imp_solve. Qed.
Lemma PosGapConfig_r17__gapType_r17__F2F1 : forall (y : nat) (H : y <= 2), PosGapConfig_r17__gapType_r17__F1 (PosGapConfig_r17__gapType_r17__F2 y) = y. enum_solve H y. Qed.

Record PosGapConfig_r17__Type : Set :=
  make__PosGapConfig_r17__Type {
    PosGapConfig_r17__measPosPreConfigGapId_r17 : MeasPosPreConfigGapId_r17__Type ;
    PosGapConfig_r17__gapOffset_r17 : Z ;
    PosGapConfig_r17__mgl_r17 : PosGapConfig_r17__mgl_r17__Type ;
    PosGapConfig_r17__mgrp_r17 : PosGapConfig_r17__mgrp_r17__Type ;
    PosGapConfig_r17__mgta_r17 : PosGapConfig_r17__mgta_r17__Type ;
    PosGapConfig_r17__gapType_r17 : PosGapConfig_r17__gapType_r17__Type ;
}.
Definition PosGapConfig_r17__root_list : list seq_elem := (
 Nor MeasPosPreConfigGapId_r17__Type MeasPosPreConfigGapId_r17__cond ::
 Nor Z PosGapConfig_r17__gapOffset_r17__cond ::
 Nor PosGapConfig_r17__mgl_r17__Type PosGapConfig_r17__mgl_r17__cond ::
 Nor PosGapConfig_r17__mgrp_r17__Type PosGapConfig_r17__mgrp_r17__cond ::
 Nor PosGapConfig_r17__mgta_r17__Type PosGapConfig_r17__mgta_r17__cond ::
 Nor PosGapConfig_r17__gapType_r17__Type PosGapConfig_r17__gapType_r17__cond ::
 nil).
Definition PosGapConfig_r17__ext_list : list typ := (
  nil).
Definition PosGapConfig_r17__cond (z : PosGapConfig_r17__Type) := 
(  MeasPosPreConfigGapId_r17__cond (PosGapConfig_r17__measPosPreConfigGapId_r17 z) /\
  PosGapConfig_r17__gapOffset_r17__cond (PosGapConfig_r17__gapOffset_r17 z) /\
  PosGapConfig_r17__mgl_r17__cond (PosGapConfig_r17__mgl_r17 z) /\
  PosGapConfig_r17__mgrp_r17__cond (PosGapConfig_r17__mgrp_r17 z) /\
  PosGapConfig_r17__mgta_r17__cond (PosGapConfig_r17__mgta_r17 z) /\
  PosGapConfig_r17__gapType_r17__cond (PosGapConfig_r17__gapType_r17 z) /\
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
Definition PosGapConfig_r17__gapOffset_r17__Format : T_Format Z PosGapConfig_r17__gapOffset_r17__cond :=
 ranged_int_format (0) (159) PosGapConfig_r17__gapOffset_r17__helper1 PosGapConfig_r17__gapOffset_r17__helper2.

Opaque PosGapConfig_r17__gapOffset_r17__cond PosGapConfig_r17__gapOffset_r17__Format.

Definition PosGapConfig_r17__mgl_r17__Format : T_Format PosGapConfig_r17__mgl_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosGapConfig_r17__mgl_r17__nat__Format PosGapConfig_r17__mgl_r17__F1 PosGapConfig_r17__mgl_r17__F2 PosGapConfig_r17__mgl_r17__F1F2 PosGapConfig_r17__mgl_r17__F2F1.

Opaque PosGapConfig_r17__mgl_r17__cond PosGapConfig_r17__mgl_r17__Format.

Definition PosGapConfig_r17__mgrp_r17__Format : T_Format PosGapConfig_r17__mgrp_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosGapConfig_r17__mgrp_r17__nat__Format PosGapConfig_r17__mgrp_r17__F1 PosGapConfig_r17__mgrp_r17__F2 PosGapConfig_r17__mgrp_r17__F1F2 PosGapConfig_r17__mgrp_r17__F2F1.

Opaque PosGapConfig_r17__mgrp_r17__cond PosGapConfig_r17__mgrp_r17__Format.

Definition PosGapConfig_r17__mgta_r17__Format : T_Format PosGapConfig_r17__mgta_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosGapConfig_r17__mgta_r17__nat__Format PosGapConfig_r17__mgta_r17__F1 PosGapConfig_r17__mgta_r17__F2 PosGapConfig_r17__mgta_r17__F1F2 PosGapConfig_r17__mgta_r17__F2F1.

Opaque PosGapConfig_r17__mgta_r17__cond PosGapConfig_r17__mgta_r17__Format.

Definition PosGapConfig_r17__gapType_r17__Format : T_Format PosGapConfig_r17__gapType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosGapConfig_r17__gapType_r17__nat__Format PosGapConfig_r17__gapType_r17__F1 PosGapConfig_r17__gapType_r17__F2 PosGapConfig_r17__gapType_r17__F1F2 PosGapConfig_r17__gapType_r17__F2F1.

Opaque PosGapConfig_r17__gapType_r17__cond PosGapConfig_r17__gapType_r17__Format.


Definition PosGapConfig_r17__root_Format_Type := Eval cbn in seq_format_prod PosGapConfig_r17__root_list.
Definition PosGapConfig_r17__root_Format_list : PosGapConfig_r17__root_Format_Type :=
  (MeasPosPreConfigGapId_r17__Format, (PosGapConfig_r17__gapOffset_r17__Format, (PosGapConfig_r17__mgl_r17__Format, (PosGapConfig_r17__mgrp_r17__Format, (PosGapConfig_r17__mgta_r17__Format, (PosGapConfig_r17__gapType_r17__Format, unit_format)))))).

Definition PosGapConfig_r17__ext_Format_Type := Eval cbn in get_formats PosGapConfig_r17__ext_list.
Definition PosGapConfig_r17__ext_Format_list : PosGapConfig_r17__ext_Format_Type :=
  unit__Format.

Definition PosGapConfig_r17__list_type : Set := (seq_type PosGapConfig_r17__root_list) * (seq_ext_type PosGapConfig_r17__ext_list).
Definition PosGapConfig_r17__list_cond (z : PosGapConfig_r17__list_type) : Prop :=
        (seq_cond PosGapConfig_r17__root_list (fst z)) /\ (seq_ext_cond PosGapConfig_r17__ext_list (snd z)).
Definition PosGapConfig_r17__list_format : T_Format PosGapConfig_r17__list_type PosGapConfig_r17__list_cond :=
 (* Eval compute in *) seq_ext_format PosGapConfig_r17__root_list PosGapConfig_r17__root_Format_list PosGapConfig_r17__ext_list PosGapConfig_r17__ext_Format_list.

Opaque PosGapConfig_r17__list_format.
Definition PosGapConfig_r17__F1 (z : PosGapConfig_r17__Type) : PosGapConfig_r17__list_type :=
  (((PosGapConfig_r17__measPosPreConfigGapId_r17 z, (PosGapConfig_r17__gapOffset_r17 z, (PosGapConfig_r17__mgl_r17 z, (PosGapConfig_r17__mgrp_r17 z, (PosGapConfig_r17__mgta_r17 z, (PosGapConfig_r17__gapType_r17 z, tt))))))), (
tt)).
Definition PosGapConfig_r17__F2 (y : PosGapConfig_r17__list_type) : PosGapConfig_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__PosGapConfig_r17__Type j0 j1 j2 j3 j4 j5
  end.
Definition PosGapConfig_r17__helper1 : (forall a : PosGapConfig_r17__Type, PosGapConfig_r17__cond a -> PosGapConfig_r17__list_cond (PosGapConfig_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PosGapConfig_r17__helper2 : (forall a : PosGapConfig_r17__Type, PosGapConfig_r17__F2 (PosGapConfig_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PosGapConfig_r17__helper3 : (forall b : PosGapConfig_r17__list_type, PosGapConfig_r17__list_cond b -> PosGapConfig_r17__cond (PosGapConfig_r17__F2 b) /\ PosGapConfig_r17__F1 (PosGapConfig_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PosGapConfig_r17__cond, PosGapConfig_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PosGapConfig_r17__Format : T_Format PosGapConfig_r17__Type PosGapConfig_r17__cond :=
 proj2_format PosGapConfig_r17__cond PosGapConfig_r17__list_format  PosGapConfig_r17__F1 PosGapConfig_r17__F2 PosGapConfig_r17__helper1 PosGapConfig_r17__helper2 PosGapConfig_r17__helper3.

Opaque PosGapConfig_r17__cond PosGapConfig_r17__Format.

