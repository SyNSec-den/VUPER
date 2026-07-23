Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Type : Set :=
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB2
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB4
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB6
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB8
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB10
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB14
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB18
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB22
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB26
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB30
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB34
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare5
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare4
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare3
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare2
 | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare1
.
Definition CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__cond := (fun (_ : CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Type) => True).
Lemma CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__nat__helper.

Definition CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1 t :=
  match t with
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB2 => 0
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB4 => 1
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB6 => 2
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB8 => 3
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB10 => 4
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB14 => 5
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB18 => 6
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB22 => 7
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB26 => 8
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB30 => 9
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB34 => 10
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare5 => 11
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare4 => 12
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare3 => 13
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare2 => 14
  | CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare1 => 15
  end.
Definition CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F2 n :=
  match n with
  | 0 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB2
  | 1 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB4
  | 2 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB6
  | 3 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB8
  | 4 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB10
  | 5 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB14
  | 6 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB18
  | 7 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB22
  | 8 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB26
  | 9 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB30
  | 10 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB34
  | 11 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare5
  | 12 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare4
  | 13 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare3
  | 14 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare2
  | 15 => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__spare1
  | _ => CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__dB2
  end.
Lemma CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1F2 : forall x : CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Type, (CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1 x <= 15) /\ CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F2 (CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1 x) = x. imp_solve. Qed.
Lemma CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F2F1 : forall (y : nat) (H : y <= 15), CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1 (CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F2 y) = y. enum_solve H y. Qed.

Record CG_SDT_TA_ValidationConfig_r17__Type : Set :=
  make__CG_SDT_TA_ValidationConfig_r17__Type {
    CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17 : CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Type ;
}.
Definition CG_SDT_TA_ValidationConfig_r17__list := (
 Nor CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Type CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__cond ::
 nil).
Definition CG_SDT_TA_ValidationConfig_r17__cond z := 
  CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__cond (CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17 z) /\
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
Definition CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Format : T_Format CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__nat__Format CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1 CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F2 CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F1F2 CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__F2F1.

Opaque CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__cond CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Format.


Definition CG_SDT_TA_ValidationConfig_r17__Format_Type := Eval cbn in seq_format_prod CG_SDT_TA_ValidationConfig_r17__list.
Definition CG_SDT_TA_ValidationConfig_r17__Format_list : CG_SDT_TA_ValidationConfig_r17__Format_Type :=
  (CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17__Format, unit_format).
Definition CG_SDT_TA_ValidationConfig_r17__list__Format := (*Eval compute in *) seq_format CG_SDT_TA_ValidationConfig_r17__list CG_SDT_TA_ValidationConfig_r17__Format_list.
Definition CG_SDT_TA_ValidationConfig_r17__F1 z :=
  (CG_SDT_TA_ValidationConfig_r17__cg_SDT_RSRP_ChangeThreshold_r17 z, tt).
Definition CG_SDT_TA_ValidationConfig_r17__F2 (y : seq_type CG_SDT_TA_ValidationConfig_r17__list) :=
  match y with
  | (i0, _)=>
    make__CG_SDT_TA_ValidationConfig_r17__Type i0
  end.
Lemma CG_SDT_TA_ValidationConfig_r17__F1F2_cond (z : CG_SDT_TA_ValidationConfig_r17__Type)
  : CG_SDT_TA_ValidationConfig_r17__cond z ->
  (seq_cond CG_SDT_TA_ValidationConfig_r17__list (CG_SDT_TA_ValidationConfig_r17__F1 z)).
intro H. unfold CG_SDT_TA_ValidationConfig_r17__cond in H. simpl. auto. Qed.
Lemma CG_SDT_TA_ValidationConfig_r17__F1F2_cond2 (z : CG_SDT_TA_ValidationConfig_r17__Type)
 : CG_SDT_TA_ValidationConfig_r17__F2 (CG_SDT_TA_ValidationConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_SDT_TA_ValidationConfig_r17__F2F1_cond (y : seq_type CG_SDT_TA_ValidationConfig_r17__list)
  : seq_cond CG_SDT_TA_ValidationConfig_r17__list y ->
 (CG_SDT_TA_ValidationConfig_r17__cond (CG_SDT_TA_ValidationConfig_r17__F2 y)) /\  CG_SDT_TA_ValidationConfig_r17__F1 (CG_SDT_TA_ValidationConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_SDT_TA_ValidationConfig_r17__cond. simpl in *. auto.
 - simpl. unfold CG_SDT_TA_ValidationConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_SDT_TA_ValidationConfig_r17__Format : T_Format CG_SDT_TA_ValidationConfig_r17__Type CG_SDT_TA_ValidationConfig_r17__cond :=
        proj2_format  CG_SDT_TA_ValidationConfig_r17__cond CG_SDT_TA_ValidationConfig_r17__list__Format
    CG_SDT_TA_ValidationConfig_r17__F1 CG_SDT_TA_ValidationConfig_r17__F2 CG_SDT_TA_ValidationConfig_r17__F1F2_cond  CG_SDT_TA_ValidationConfig_r17__F1F2_cond2 CG_SDT_TA_ValidationConfig_r17__F2F1_cond.
Opaque CG_SDT_TA_ValidationConfig_r17__cond CG_SDT_TA_ValidationConfig_r17__Format.

