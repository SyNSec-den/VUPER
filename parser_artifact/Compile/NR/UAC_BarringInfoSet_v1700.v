Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Type : Set :=
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p00
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p05
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p10
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p15
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p20
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p25
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p30
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p40
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p50
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p60
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p70
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p75
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p80
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p85
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p90
 | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p95
.
Definition UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__cond := (fun (_ : UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Type) => True).
Lemma UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__nat__helper.

Definition UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1 t :=
  match t with
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p00 => 0
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p05 => 1
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p10 => 2
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p15 => 3
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p20 => 4
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p25 => 5
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p30 => 6
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p40 => 7
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p50 => 8
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p60 => 9
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p70 => 10
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p75 => 11
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p80 => 12
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p85 => 13
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p90 => 14
  | UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p95 => 15
  end.
Definition UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F2 n :=
  match n with
  | 0 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p00
  | 1 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p05
  | 2 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p10
  | 3 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p15
  | 4 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p20
  | 5 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p25
  | 6 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p30
  | 7 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p40
  | 8 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p50
  | 9 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p60
  | 10 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p70
  | 11 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p75
  | 12 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p80
  | 13 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p85
  | 14 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p90
  | 15 => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p95
  | _ => UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__p00
  end.
Lemma UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1F2 : forall x : UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Type, (UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1 x <= 15) /\ UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F2 (UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1 x) = x. imp_solve. Qed.
Lemma UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F2F1 : forall (y : nat) (H : y <= 15), UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1 (UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F2 y) = y. enum_solve H y. Qed.

Record UAC_BarringInfoSet_v1700__Type : Set :=
  make__UAC_BarringInfoSet_v1700__Type {
    UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17 : option UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Type ;
}.
Definition UAC_BarringInfoSet_v1700__list := (
 Opt UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Type UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__cond ::
 nil).
Definition UAC_BarringInfoSet_v1700__cond z := 
  opt_cond UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__cond (UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17 z) /\
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
Definition UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Format : T_Format UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__nat__Format UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1 UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F2 UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F1F2 UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__F2F1.

Opaque UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__cond UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Format.


Definition UAC_BarringInfoSet_v1700__Format_Type := Eval cbn in seq_format_prod UAC_BarringInfoSet_v1700__list.
Definition UAC_BarringInfoSet_v1700__Format_list : UAC_BarringInfoSet_v1700__Format_Type :=
  (UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17__Format, unit_format).
Definition UAC_BarringInfoSet_v1700__list__Format := (*Eval compute in *) seq_format UAC_BarringInfoSet_v1700__list UAC_BarringInfoSet_v1700__Format_list.
Definition UAC_BarringInfoSet_v1700__F1 z :=
  (UAC_BarringInfoSet_v1700__uac_BarringFactorForAI3_r17 z, tt).
Definition UAC_BarringInfoSet_v1700__F2 (y : seq_type UAC_BarringInfoSet_v1700__list) :=
  match y with
  | (i0, _)=>
    make__UAC_BarringInfoSet_v1700__Type i0
  end.
Lemma UAC_BarringInfoSet_v1700__F1F2_cond (z : UAC_BarringInfoSet_v1700__Type)
  : UAC_BarringInfoSet_v1700__cond z ->
  (seq_cond UAC_BarringInfoSet_v1700__list (UAC_BarringInfoSet_v1700__F1 z)).
intro H. unfold UAC_BarringInfoSet_v1700__cond in H. simpl. auto. Qed.
Lemma UAC_BarringInfoSet_v1700__F1F2_cond2 (z : UAC_BarringInfoSet_v1700__Type)
 : UAC_BarringInfoSet_v1700__F2 (UAC_BarringInfoSet_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UAC_BarringInfoSet_v1700__F2F1_cond (y : seq_type UAC_BarringInfoSet_v1700__list)
  : seq_cond UAC_BarringInfoSet_v1700__list y ->
 (UAC_BarringInfoSet_v1700__cond (UAC_BarringInfoSet_v1700__F2 y)) /\  UAC_BarringInfoSet_v1700__F1 (UAC_BarringInfoSet_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UAC_BarringInfoSet_v1700__cond. simpl in *. auto.
 - simpl. unfold UAC_BarringInfoSet_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UAC_BarringInfoSet_v1700__Format : T_Format UAC_BarringInfoSet_v1700__Type UAC_BarringInfoSet_v1700__cond :=
        proj2_format  UAC_BarringInfoSet_v1700__cond UAC_BarringInfoSet_v1700__list__Format
    UAC_BarringInfoSet_v1700__F1 UAC_BarringInfoSet_v1700__F2 UAC_BarringInfoSet_v1700__F1F2_cond  UAC_BarringInfoSet_v1700__F1F2_cond2 UAC_BarringInfoSet_v1700__F2F1_cond.
Opaque UAC_BarringInfoSet_v1700__cond UAC_BarringInfoSet_v1700__Format.

