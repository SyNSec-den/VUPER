Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.VictimSystemType.

Opaque VictimSystemType__cond VictimSystemType__Format.

Inductive AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Type : Set :=
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__eutra_nr
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nr
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__other
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__utra_nr_other
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nr_other
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare3
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare2
 | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare1
.
Definition AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__cond := (fun (_ : AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Type) => True).
Lemma AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nat__helper.

Definition AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1 t :=
  match t with
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__eutra_nr => 0
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nr => 1
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__other => 2
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__utra_nr_other => 3
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nr_other => 4
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare3 => 5
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare2 => 6
  | AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare1 => 7
  end.
Definition AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F2 n :=
  match n with
  | 0 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__eutra_nr
  | 1 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nr
  | 2 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__other
  | 3 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__utra_nr_other
  | 4 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nr_other
  | 5 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare3
  | 6 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare2
  | 7 => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__spare1
  | _ => AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__eutra_nr
  end.
Lemma AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1F2 : forall x : AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Type, (AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1 x <= 7) /\ AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F2 (AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1 x) = x. imp_solve. Qed.
Lemma AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F2F1 : forall (y : nat) (H : y <= 7), AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1 (AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F2 y) = y. enum_solve H y. Qed.

Require Import NR.AffectedCarrierFreqCombEUTRA.

Opaque AffectedCarrierFreqCombEUTRA__cond AffectedCarrierFreqCombEUTRA__Format.

Require Import NR.AffectedCarrierFreqCombNR.

Opaque AffectedCarrierFreqCombNR__cond AffectedCarrierFreqCombNR__Format.

Record AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type : Set :=
  make__AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type {
    AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__affectedCarrierFreqCombEUTRA : option AffectedCarrierFreqCombEUTRA__Type ;
    AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__affectedCarrierFreqCombNR : AffectedCarrierFreqCombNR__Type ;
}.
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list := (
 Opt AffectedCarrierFreqCombEUTRA__Type AffectedCarrierFreqCombEUTRA__cond ::
 Nor AffectedCarrierFreqCombNR__Type AffectedCarrierFreqCombNR__cond ::
 nil).
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond z := 
  opt_cond AffectedCarrierFreqCombEUTRA__cond (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__affectedCarrierFreqCombEUTRA z) /\
  AffectedCarrierFreqCombNR__cond (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__affectedCarrierFreqCombNR z) /\
  True.

Record AffectedCarrierFreqCombInfoMRDC__Type : Set :=
  make__AffectedCarrierFreqCombInfoMRDC__Type {
    AffectedCarrierFreqCombInfoMRDC__victimSystemType : VictimSystemType__Type ;
    AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC : AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Type ;
    AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC : option AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type ;
}.
Definition AffectedCarrierFreqCombInfoMRDC__list := (
 Nor VictimSystemType__Type VictimSystemType__cond ::
 Nor AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Type AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__cond ::
 Opt AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond ::
 nil).
Definition AffectedCarrierFreqCombInfoMRDC__cond z := 
  VictimSystemType__cond (AffectedCarrierFreqCombInfoMRDC__victimSystemType z) /\
  AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__cond (AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC z) /\
  opt_cond AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC z) /\
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
Definition AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Format : T_Format AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__nat__Format AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1 AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F2 AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F1F2 AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__F2F1.

Opaque AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__cond AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Format.


Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format_Type := Eval cbn in seq_format_prod AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list.
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format_list : AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format_Type :=
  (AffectedCarrierFreqCombEUTRA__Format, (AffectedCarrierFreqCombNR__Format, unit_format)).
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list__Format := (*Eval compute in *) seq_format AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format_list.
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1 z :=
  (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__affectedCarrierFreqCombEUTRA z, (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__affectedCarrierFreqCombNR z, tt)).
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2 (y : seq_type AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list) :=
  match y with
  | (i0, (i1, _))=>
    make__AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type i0 i1
  end.
Lemma AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1F2_cond (z : AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type)
  : AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond z ->
  (seq_cond AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1 z)).
intro H. unfold AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond in H. simpl. auto. Qed.
Lemma AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1F2_cond2 (z : AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type)
 : AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2 (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2F1_cond (y : seq_type AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list)
  : seq_cond AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list y ->
 (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2 y)) /\  AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1 (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond. simpl in *. auto.
 - simpl. unfold AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format : T_Format AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Type AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond :=
        proj2_format  AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__list__Format
    AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1 AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2 AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1F2_cond  AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F1F2_cond2 AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__F2F1_cond.
Opaque AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__cond AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format.


Definition AffectedCarrierFreqCombInfoMRDC__Format_Type := Eval cbn in seq_format_prod AffectedCarrierFreqCombInfoMRDC__list.
Definition AffectedCarrierFreqCombInfoMRDC__Format_list : AffectedCarrierFreqCombInfoMRDC__Format_Type :=
  (VictimSystemType__Format, (AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC__Format, (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC__Format, unit_format))).
Definition AffectedCarrierFreqCombInfoMRDC__list__Format := (*Eval compute in *) seq_format AffectedCarrierFreqCombInfoMRDC__list AffectedCarrierFreqCombInfoMRDC__Format_list.
Definition AffectedCarrierFreqCombInfoMRDC__F1 z :=
  (AffectedCarrierFreqCombInfoMRDC__victimSystemType z, (AffectedCarrierFreqCombInfoMRDC__interferenceDirectionMRDC z, (AffectedCarrierFreqCombInfoMRDC__affectedCarrierFreqCombMRDC z, tt))).
Definition AffectedCarrierFreqCombInfoMRDC__F2 (y : seq_type AffectedCarrierFreqCombInfoMRDC__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__AffectedCarrierFreqCombInfoMRDC__Type i0 i1 i2
  end.
Lemma AffectedCarrierFreqCombInfoMRDC__F1F2_cond (z : AffectedCarrierFreqCombInfoMRDC__Type)
  : AffectedCarrierFreqCombInfoMRDC__cond z ->
  (seq_cond AffectedCarrierFreqCombInfoMRDC__list (AffectedCarrierFreqCombInfoMRDC__F1 z)).
intro H. unfold AffectedCarrierFreqCombInfoMRDC__cond in H. simpl. auto. Qed.
Lemma AffectedCarrierFreqCombInfoMRDC__F1F2_cond2 (z : AffectedCarrierFreqCombInfoMRDC__Type)
 : AffectedCarrierFreqCombInfoMRDC__F2 (AffectedCarrierFreqCombInfoMRDC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AffectedCarrierFreqCombInfoMRDC__F2F1_cond (y : seq_type AffectedCarrierFreqCombInfoMRDC__list)
  : seq_cond AffectedCarrierFreqCombInfoMRDC__list y ->
 (AffectedCarrierFreqCombInfoMRDC__cond (AffectedCarrierFreqCombInfoMRDC__F2 y)) /\  AffectedCarrierFreqCombInfoMRDC__F1 (AffectedCarrierFreqCombInfoMRDC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AffectedCarrierFreqCombInfoMRDC__cond. simpl in *. auto.
 - simpl. unfold AffectedCarrierFreqCombInfoMRDC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AffectedCarrierFreqCombInfoMRDC__Format : T_Format AffectedCarrierFreqCombInfoMRDC__Type AffectedCarrierFreqCombInfoMRDC__cond :=
        proj2_format  AffectedCarrierFreqCombInfoMRDC__cond AffectedCarrierFreqCombInfoMRDC__list__Format
    AffectedCarrierFreqCombInfoMRDC__F1 AffectedCarrierFreqCombInfoMRDC__F2 AffectedCarrierFreqCombInfoMRDC__F1F2_cond  AffectedCarrierFreqCombInfoMRDC__F1F2_cond2 AffectedCarrierFreqCombInfoMRDC__F2F1_cond.
Opaque AffectedCarrierFreqCombInfoMRDC__cond AffectedCarrierFreqCombInfoMRDC__Format.

