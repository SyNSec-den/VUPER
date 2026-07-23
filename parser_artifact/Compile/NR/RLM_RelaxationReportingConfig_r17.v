Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Type : Set :=
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0dot5
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s1
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s2
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s5
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s10
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s20
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s30
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s60
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s90
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s120
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s300
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s600
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__infinity
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__spare2
 | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__spare1
.
Definition RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__cond := (fun (_ : RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Type) => True).
Lemma RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__nat__helper.

Definition RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1 t :=
  match t with
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0 => 0
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0dot5 => 1
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s1 => 2
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s2 => 3
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s5 => 4
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s10 => 5
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s20 => 6
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s30 => 7
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s60 => 8
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s90 => 9
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s120 => 10
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s300 => 11
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s600 => 12
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__infinity => 13
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__spare2 => 14
  | RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__spare1 => 15
  end.
Definition RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F2 n :=
  match n with
  | 0 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0
  | 1 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0dot5
  | 2 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s1
  | 3 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s2
  | 4 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s5
  | 5 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s10
  | 6 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s20
  | 7 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s30
  | 8 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s60
  | 9 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s90
  | 10 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s120
  | 11 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s300
  | 12 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s600
  | 13 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__infinity
  | 14 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__spare2
  | 15 => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__spare1
  | _ => RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__s0
  end.
Lemma RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1F2 : forall x : RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Type, (RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1 x <= 15) /\ RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F2 (RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F2F1 : forall (y : nat) (H : y <= 15), RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1 (RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Record RLM_RelaxationReportingConfig_r17__Type : Set :=
  make__RLM_RelaxationReportingConfig_r17__Type {
    RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer : RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Type ;
}.
Definition RLM_RelaxationReportingConfig_r17__list := (
 Nor RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Type RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__cond ::
 nil).
Definition RLM_RelaxationReportingConfig_r17__cond z := 
  RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__cond (RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer z) /\
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
Definition RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Format : T_Format RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__nat__Format RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1 RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F2 RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F1F2 RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__F2F1.

Opaque RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__cond RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Format.


Definition RLM_RelaxationReportingConfig_r17__Format_Type := Eval cbn in seq_format_prod RLM_RelaxationReportingConfig_r17__list.
Definition RLM_RelaxationReportingConfig_r17__Format_list : RLM_RelaxationReportingConfig_r17__Format_Type :=
  (RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer__Format, unit_format).
Definition RLM_RelaxationReportingConfig_r17__list__Format := (*Eval compute in *) seq_format RLM_RelaxationReportingConfig_r17__list RLM_RelaxationReportingConfig_r17__Format_list.
Definition RLM_RelaxationReportingConfig_r17__F1 z :=
  (RLM_RelaxationReportingConfig_r17__rlm_RelaxtionReportingProhibitTimer z, tt).
Definition RLM_RelaxationReportingConfig_r17__F2 (y : seq_type RLM_RelaxationReportingConfig_r17__list) :=
  match y with
  | (i0, _)=>
    make__RLM_RelaxationReportingConfig_r17__Type i0
  end.
Lemma RLM_RelaxationReportingConfig_r17__F1F2_cond (z : RLM_RelaxationReportingConfig_r17__Type)
  : RLM_RelaxationReportingConfig_r17__cond z ->
  (seq_cond RLM_RelaxationReportingConfig_r17__list (RLM_RelaxationReportingConfig_r17__F1 z)).
intro H. unfold RLM_RelaxationReportingConfig_r17__cond in H. simpl. auto. Qed.
Lemma RLM_RelaxationReportingConfig_r17__F1F2_cond2 (z : RLM_RelaxationReportingConfig_r17__Type)
 : RLM_RelaxationReportingConfig_r17__F2 (RLM_RelaxationReportingConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLM_RelaxationReportingConfig_r17__F2F1_cond (y : seq_type RLM_RelaxationReportingConfig_r17__list)
  : seq_cond RLM_RelaxationReportingConfig_r17__list y ->
 (RLM_RelaxationReportingConfig_r17__cond (RLM_RelaxationReportingConfig_r17__F2 y)) /\  RLM_RelaxationReportingConfig_r17__F1 (RLM_RelaxationReportingConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLM_RelaxationReportingConfig_r17__cond. simpl in *. auto.
 - simpl. unfold RLM_RelaxationReportingConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLM_RelaxationReportingConfig_r17__Format : T_Format RLM_RelaxationReportingConfig_r17__Type RLM_RelaxationReportingConfig_r17__cond :=
        proj2_format  RLM_RelaxationReportingConfig_r17__cond RLM_RelaxationReportingConfig_r17__list__Format
    RLM_RelaxationReportingConfig_r17__F1 RLM_RelaxationReportingConfig_r17__F2 RLM_RelaxationReportingConfig_r17__F1F2_cond  RLM_RelaxationReportingConfig_r17__F1F2_cond2 RLM_RelaxationReportingConfig_r17__F2F1_cond.
Opaque RLM_RelaxationReportingConfig_r17__cond RLM_RelaxationReportingConfig_r17__Format.

