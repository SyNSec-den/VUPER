Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Type : Set :=
 | Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__supported
.
Definition Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__cond := (fun (_ : Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Type) => True).
Lemma Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__nat__helper.

Definition Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1 t :=
  match t with
  | Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__supported => 0
  end.
Definition Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__supported
  | _ => Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__supported
  end.
Lemma Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1F2 : forall x : Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Type, (Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1 x <= 0) /\ Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F2 (Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1 (Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon_v16a0__Type : Set :=
  make__Phy_ParametersCommon_v16a0__Type {
    Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16 : option Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Type ;
}.
Definition Phy_ParametersCommon_v16a0__list := (
 Opt Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Type Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__cond ::
 nil).
Definition Phy_ParametersCommon_v16a0__cond z := 
  opt_cond Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__cond (Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16 z) /\
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
Definition Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Format : T_Format Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__nat__Format Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1 Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F2 Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F1F2 Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__F2F1.

Opaque Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__cond Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Format.


Definition Phy_ParametersCommon_v16a0__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon_v16a0__list.
Definition Phy_ParametersCommon_v16a0__Format_list : Phy_ParametersCommon_v16a0__Format_Type :=
  (Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16__Format, unit_format).
Definition Phy_ParametersCommon_v16a0__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon_v16a0__list Phy_ParametersCommon_v16a0__Format_list.
Definition Phy_ParametersCommon_v16a0__F1 z :=
  (Phy_ParametersCommon_v16a0__srs_PeriodicityAndOffsetExt_r16 z, tt).
Definition Phy_ParametersCommon_v16a0__F2 (y : seq_type Phy_ParametersCommon_v16a0__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersCommon_v16a0__Type i0
  end.
Lemma Phy_ParametersCommon_v16a0__F1F2_cond (z : Phy_ParametersCommon_v16a0__Type)
  : Phy_ParametersCommon_v16a0__cond z ->
  (seq_cond Phy_ParametersCommon_v16a0__list (Phy_ParametersCommon_v16a0__F1 z)).
intro H. unfold Phy_ParametersCommon_v16a0__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon_v16a0__F1F2_cond2 (z : Phy_ParametersCommon_v16a0__Type)
 : Phy_ParametersCommon_v16a0__F2 (Phy_ParametersCommon_v16a0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon_v16a0__F2F1_cond (y : seq_type Phy_ParametersCommon_v16a0__list)
  : seq_cond Phy_ParametersCommon_v16a0__list y ->
 (Phy_ParametersCommon_v16a0__cond (Phy_ParametersCommon_v16a0__F2 y)) /\  Phy_ParametersCommon_v16a0__F1 (Phy_ParametersCommon_v16a0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon_v16a0__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon_v16a0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon_v16a0__Format : T_Format Phy_ParametersCommon_v16a0__Type Phy_ParametersCommon_v16a0__cond :=
        proj2_format  Phy_ParametersCommon_v16a0__cond Phy_ParametersCommon_v16a0__list__Format
    Phy_ParametersCommon_v16a0__F1 Phy_ParametersCommon_v16a0__F2 Phy_ParametersCommon_v16a0__F1F2_cond  Phy_ParametersCommon_v16a0__F1F2_cond2 Phy_ParametersCommon_v16a0__F2F1_cond.
Opaque Phy_ParametersCommon_v16a0__cond Phy_ParametersCommon_v16a0__Format.

