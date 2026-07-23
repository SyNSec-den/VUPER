Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UAC_BarringInfoSet__uac_BarringFactor__Type : Set :=
 | UAC_BarringInfoSet__uac_BarringFactor__p00
 | UAC_BarringInfoSet__uac_BarringFactor__p05
 | UAC_BarringInfoSet__uac_BarringFactor__p10
 | UAC_BarringInfoSet__uac_BarringFactor__p15
 | UAC_BarringInfoSet__uac_BarringFactor__p20
 | UAC_BarringInfoSet__uac_BarringFactor__p25
 | UAC_BarringInfoSet__uac_BarringFactor__p30
 | UAC_BarringInfoSet__uac_BarringFactor__p40
 | UAC_BarringInfoSet__uac_BarringFactor__p50
 | UAC_BarringInfoSet__uac_BarringFactor__p60
 | UAC_BarringInfoSet__uac_BarringFactor__p70
 | UAC_BarringInfoSet__uac_BarringFactor__p75
 | UAC_BarringInfoSet__uac_BarringFactor__p80
 | UAC_BarringInfoSet__uac_BarringFactor__p85
 | UAC_BarringInfoSet__uac_BarringFactor__p90
 | UAC_BarringInfoSet__uac_BarringFactor__p95
.
Definition UAC_BarringInfoSet__uac_BarringFactor__cond := (fun (_ : UAC_BarringInfoSet__uac_BarringFactor__Type) => True).
Lemma UAC_BarringInfoSet__uac_BarringFactor__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UAC_BarringInfoSet__uac_BarringFactor__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 UAC_BarringInfoSet__uac_BarringFactor__nat__helper.

Definition UAC_BarringInfoSet__uac_BarringFactor__F1 t :=
  match t with
  | UAC_BarringInfoSet__uac_BarringFactor__p00 => 0
  | UAC_BarringInfoSet__uac_BarringFactor__p05 => 1
  | UAC_BarringInfoSet__uac_BarringFactor__p10 => 2
  | UAC_BarringInfoSet__uac_BarringFactor__p15 => 3
  | UAC_BarringInfoSet__uac_BarringFactor__p20 => 4
  | UAC_BarringInfoSet__uac_BarringFactor__p25 => 5
  | UAC_BarringInfoSet__uac_BarringFactor__p30 => 6
  | UAC_BarringInfoSet__uac_BarringFactor__p40 => 7
  | UAC_BarringInfoSet__uac_BarringFactor__p50 => 8
  | UAC_BarringInfoSet__uac_BarringFactor__p60 => 9
  | UAC_BarringInfoSet__uac_BarringFactor__p70 => 10
  | UAC_BarringInfoSet__uac_BarringFactor__p75 => 11
  | UAC_BarringInfoSet__uac_BarringFactor__p80 => 12
  | UAC_BarringInfoSet__uac_BarringFactor__p85 => 13
  | UAC_BarringInfoSet__uac_BarringFactor__p90 => 14
  | UAC_BarringInfoSet__uac_BarringFactor__p95 => 15
  end.
Definition UAC_BarringInfoSet__uac_BarringFactor__F2 n :=
  match n with
  | 0 => UAC_BarringInfoSet__uac_BarringFactor__p00
  | 1 => UAC_BarringInfoSet__uac_BarringFactor__p05
  | 2 => UAC_BarringInfoSet__uac_BarringFactor__p10
  | 3 => UAC_BarringInfoSet__uac_BarringFactor__p15
  | 4 => UAC_BarringInfoSet__uac_BarringFactor__p20
  | 5 => UAC_BarringInfoSet__uac_BarringFactor__p25
  | 6 => UAC_BarringInfoSet__uac_BarringFactor__p30
  | 7 => UAC_BarringInfoSet__uac_BarringFactor__p40
  | 8 => UAC_BarringInfoSet__uac_BarringFactor__p50
  | 9 => UAC_BarringInfoSet__uac_BarringFactor__p60
  | 10 => UAC_BarringInfoSet__uac_BarringFactor__p70
  | 11 => UAC_BarringInfoSet__uac_BarringFactor__p75
  | 12 => UAC_BarringInfoSet__uac_BarringFactor__p80
  | 13 => UAC_BarringInfoSet__uac_BarringFactor__p85
  | 14 => UAC_BarringInfoSet__uac_BarringFactor__p90
  | 15 => UAC_BarringInfoSet__uac_BarringFactor__p95
  | _ => UAC_BarringInfoSet__uac_BarringFactor__p00
  end.
Lemma UAC_BarringInfoSet__uac_BarringFactor__F1F2 : forall x : UAC_BarringInfoSet__uac_BarringFactor__Type, (UAC_BarringInfoSet__uac_BarringFactor__F1 x <= 15) /\ UAC_BarringInfoSet__uac_BarringFactor__F2 (UAC_BarringInfoSet__uac_BarringFactor__F1 x) = x. imp_solve. Qed.
Lemma UAC_BarringInfoSet__uac_BarringFactor__F2F1 : forall (y : nat) (H : y <= 15), UAC_BarringInfoSet__uac_BarringFactor__F1 (UAC_BarringInfoSet__uac_BarringFactor__F2 y) = y. enum_solve H y. Qed.

Inductive UAC_BarringInfoSet__uac_BarringTime__Type : Set :=
 | UAC_BarringInfoSet__uac_BarringTime__s4
 | UAC_BarringInfoSet__uac_BarringTime__s8
 | UAC_BarringInfoSet__uac_BarringTime__s16
 | UAC_BarringInfoSet__uac_BarringTime__s32
 | UAC_BarringInfoSet__uac_BarringTime__s64
 | UAC_BarringInfoSet__uac_BarringTime__s128
 | UAC_BarringInfoSet__uac_BarringTime__s256
 | UAC_BarringInfoSet__uac_BarringTime__s512
.
Definition UAC_BarringInfoSet__uac_BarringTime__cond := (fun (_ : UAC_BarringInfoSet__uac_BarringTime__Type) => True).
Lemma UAC_BarringInfoSet__uac_BarringTime__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UAC_BarringInfoSet__uac_BarringTime__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UAC_BarringInfoSet__uac_BarringTime__nat__helper.

Definition UAC_BarringInfoSet__uac_BarringTime__F1 t :=
  match t with
  | UAC_BarringInfoSet__uac_BarringTime__s4 => 0
  | UAC_BarringInfoSet__uac_BarringTime__s8 => 1
  | UAC_BarringInfoSet__uac_BarringTime__s16 => 2
  | UAC_BarringInfoSet__uac_BarringTime__s32 => 3
  | UAC_BarringInfoSet__uac_BarringTime__s64 => 4
  | UAC_BarringInfoSet__uac_BarringTime__s128 => 5
  | UAC_BarringInfoSet__uac_BarringTime__s256 => 6
  | UAC_BarringInfoSet__uac_BarringTime__s512 => 7
  end.
Definition UAC_BarringInfoSet__uac_BarringTime__F2 n :=
  match n with
  | 0 => UAC_BarringInfoSet__uac_BarringTime__s4
  | 1 => UAC_BarringInfoSet__uac_BarringTime__s8
  | 2 => UAC_BarringInfoSet__uac_BarringTime__s16
  | 3 => UAC_BarringInfoSet__uac_BarringTime__s32
  | 4 => UAC_BarringInfoSet__uac_BarringTime__s64
  | 5 => UAC_BarringInfoSet__uac_BarringTime__s128
  | 6 => UAC_BarringInfoSet__uac_BarringTime__s256
  | 7 => UAC_BarringInfoSet__uac_BarringTime__s512
  | _ => UAC_BarringInfoSet__uac_BarringTime__s4
  end.
Lemma UAC_BarringInfoSet__uac_BarringTime__F1F2 : forall x : UAC_BarringInfoSet__uac_BarringTime__Type, (UAC_BarringInfoSet__uac_BarringTime__F1 x <= 7) /\ UAC_BarringInfoSet__uac_BarringTime__F2 (UAC_BarringInfoSet__uac_BarringTime__F1 x) = x. imp_solve. Qed.
Lemma UAC_BarringInfoSet__uac_BarringTime__F2F1 : forall (y : nat) (H : y <= 7), UAC_BarringInfoSet__uac_BarringTime__F1 (UAC_BarringInfoSet__uac_BarringTime__F2 y) = y. enum_solve H y. Qed.

Definition UAC_BarringInfoSet__uac_BarringForAccessIdentity__Type := bit_string_fixed.
Definition UAC_BarringInfoSet__uac_BarringForAccessIdentity__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 7 /\ bit_string_len_prop (fst z) (snd z)).
Record UAC_BarringInfoSet__Type : Set :=
  make__UAC_BarringInfoSet__Type {
    UAC_BarringInfoSet__uac_BarringFactor : UAC_BarringInfoSet__uac_BarringFactor__Type ;
    UAC_BarringInfoSet__uac_BarringTime : UAC_BarringInfoSet__uac_BarringTime__Type ;
    UAC_BarringInfoSet__uac_BarringForAccessIdentity : UAC_BarringInfoSet__uac_BarringForAccessIdentity__Type ;
}.
Definition UAC_BarringInfoSet__list := (
 Nor UAC_BarringInfoSet__uac_BarringFactor__Type UAC_BarringInfoSet__uac_BarringFactor__cond ::
 Nor UAC_BarringInfoSet__uac_BarringTime__Type UAC_BarringInfoSet__uac_BarringTime__cond ::
 Nor UAC_BarringInfoSet__uac_BarringForAccessIdentity__Type UAC_BarringInfoSet__uac_BarringForAccessIdentity__cond ::
 nil).
Definition UAC_BarringInfoSet__cond z := 
  UAC_BarringInfoSet__uac_BarringFactor__cond (UAC_BarringInfoSet__uac_BarringFactor z) /\
  UAC_BarringInfoSet__uac_BarringTime__cond (UAC_BarringInfoSet__uac_BarringTime z) /\
  UAC_BarringInfoSet__uac_BarringForAccessIdentity__cond (UAC_BarringInfoSet__uac_BarringForAccessIdentity z) /\
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
Definition UAC_BarringInfoSet__uac_BarringFactor__Format : T_Format UAC_BarringInfoSet__uac_BarringFactor__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UAC_BarringInfoSet__uac_BarringFactor__nat__Format UAC_BarringInfoSet__uac_BarringFactor__F1 UAC_BarringInfoSet__uac_BarringFactor__F2 UAC_BarringInfoSet__uac_BarringFactor__F1F2 UAC_BarringInfoSet__uac_BarringFactor__F2F1.

Opaque UAC_BarringInfoSet__uac_BarringFactor__cond UAC_BarringInfoSet__uac_BarringFactor__Format.

Definition UAC_BarringInfoSet__uac_BarringTime__Format : T_Format UAC_BarringInfoSet__uac_BarringTime__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UAC_BarringInfoSet__uac_BarringTime__nat__Format UAC_BarringInfoSet__uac_BarringTime__F1 UAC_BarringInfoSet__uac_BarringTime__F2 UAC_BarringInfoSet__uac_BarringTime__F1F2 UAC_BarringInfoSet__uac_BarringTime__F2F1.

Opaque UAC_BarringInfoSet__uac_BarringTime__cond UAC_BarringInfoSet__uac_BarringTime__Format.

Definition UAC_BarringInfoSet__uac_BarringForAccessIdentity__Format : T_Format UAC_BarringInfoSet__uac_BarringForAccessIdentity__Type UAC_BarringInfoSet__uac_BarringForAccessIdentity__cond := (* Eval compute in *) bit_string_fixed_format 7.
Opaque UAC_BarringInfoSet__uac_BarringForAccessIdentity__cond UAC_BarringInfoSet__uac_BarringForAccessIdentity__Format.


Definition UAC_BarringInfoSet__Format_Type := Eval cbn in seq_format_prod UAC_BarringInfoSet__list.
Definition UAC_BarringInfoSet__Format_list : UAC_BarringInfoSet__Format_Type :=
  (UAC_BarringInfoSet__uac_BarringFactor__Format, (UAC_BarringInfoSet__uac_BarringTime__Format, (UAC_BarringInfoSet__uac_BarringForAccessIdentity__Format, unit_format))).
Definition UAC_BarringInfoSet__list__Format := (*Eval compute in *) seq_format UAC_BarringInfoSet__list UAC_BarringInfoSet__Format_list.
Definition UAC_BarringInfoSet__F1 z :=
  (UAC_BarringInfoSet__uac_BarringFactor z, (UAC_BarringInfoSet__uac_BarringTime z, (UAC_BarringInfoSet__uac_BarringForAccessIdentity z, tt))).
Definition UAC_BarringInfoSet__F2 (y : seq_type UAC_BarringInfoSet__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UAC_BarringInfoSet__Type i0 i1 i2
  end.
Lemma UAC_BarringInfoSet__F1F2_cond (z : UAC_BarringInfoSet__Type)
  : UAC_BarringInfoSet__cond z ->
  (seq_cond UAC_BarringInfoSet__list (UAC_BarringInfoSet__F1 z)).
intro H. unfold UAC_BarringInfoSet__cond in H. simpl. auto. Qed.
Lemma UAC_BarringInfoSet__F1F2_cond2 (z : UAC_BarringInfoSet__Type)
 : UAC_BarringInfoSet__F2 (UAC_BarringInfoSet__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UAC_BarringInfoSet__F2F1_cond (y : seq_type UAC_BarringInfoSet__list)
  : seq_cond UAC_BarringInfoSet__list y ->
 (UAC_BarringInfoSet__cond (UAC_BarringInfoSet__F2 y)) /\  UAC_BarringInfoSet__F1 (UAC_BarringInfoSet__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UAC_BarringInfoSet__cond. simpl in *. auto.
 - simpl. unfold UAC_BarringInfoSet__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UAC_BarringInfoSet__Format : T_Format UAC_BarringInfoSet__Type UAC_BarringInfoSet__cond :=
        proj2_format  UAC_BarringInfoSet__cond UAC_BarringInfoSet__list__Format
    UAC_BarringInfoSet__F1 UAC_BarringInfoSet__F2 UAC_BarringInfoSet__F1F2_cond  UAC_BarringInfoSet__F1F2_cond2 UAC_BarringInfoSet__F2F1_cond.
Opaque UAC_BarringInfoSet__cond UAC_BarringInfoSet__Format.

