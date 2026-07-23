Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Type : Set :=
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0dot5
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s1
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s2
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s3
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s4
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s5
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s6
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s7
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s8
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s9
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s10
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s20
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s30
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__infinity
 | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__spare1
.
Definition ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__cond := (fun (_ : ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Type) => True).
Lemma ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__nat__helper.

Definition ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1 t :=
  match t with
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0 => 0
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0dot5 => 1
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s1 => 2
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s2 => 3
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s3 => 4
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s4 => 5
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s5 => 6
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s6 => 7
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s7 => 8
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s8 => 9
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s9 => 10
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s10 => 11
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s20 => 12
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s30 => 13
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__infinity => 14
  | ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__spare1 => 15
  end.
Definition ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F2 n :=
  match n with
  | 0 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0
  | 1 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0dot5
  | 2 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s1
  | 3 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s2
  | 4 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s3
  | 5 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s4
  | 6 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s5
  | 7 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s6
  | 8 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s7
  | 9 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s8
  | 10 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s9
  | 11 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s10
  | 12 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s20
  | 13 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s30
  | 14 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__infinity
  | 15 => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__spare1
  | _ => ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__s0
  end.
Lemma ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1F2 : forall x : ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Type, (ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1 x <= 15) /\ ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F2 (ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F2F1 : forall (y : nat) (H : y <= 15), ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1 (ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ReleasePreferenceConfig_r16__connectedReporting__Type : Set :=
 | ReleasePreferenceConfig_r16__connectedReporting__true
.
Definition ReleasePreferenceConfig_r16__connectedReporting__cond := (fun (_ : ReleasePreferenceConfig_r16__connectedReporting__Type) => True).
Lemma ReleasePreferenceConfig_r16__connectedReporting__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReleasePreferenceConfig_r16__connectedReporting__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ReleasePreferenceConfig_r16__connectedReporting__nat__helper.

Definition ReleasePreferenceConfig_r16__connectedReporting__F1 t :=
  match t with
  | ReleasePreferenceConfig_r16__connectedReporting__true => 0
  end.
Definition ReleasePreferenceConfig_r16__connectedReporting__F2 n :=
  match n with
  | 0 => ReleasePreferenceConfig_r16__connectedReporting__true
  | _ => ReleasePreferenceConfig_r16__connectedReporting__true
  end.
Lemma ReleasePreferenceConfig_r16__connectedReporting__F1F2 : forall x : ReleasePreferenceConfig_r16__connectedReporting__Type, (ReleasePreferenceConfig_r16__connectedReporting__F1 x <= 0) /\ ReleasePreferenceConfig_r16__connectedReporting__F2 (ReleasePreferenceConfig_r16__connectedReporting__F1 x) = x. imp_solve. Qed.
Lemma ReleasePreferenceConfig_r16__connectedReporting__F2F1 : forall (y : nat) (H : y <= 0), ReleasePreferenceConfig_r16__connectedReporting__F1 (ReleasePreferenceConfig_r16__connectedReporting__F2 y) = y. enum_solve H y. Qed.

Record ReleasePreferenceConfig_r16__Type : Set :=
  make__ReleasePreferenceConfig_r16__Type {
    ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16 : ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Type ;
    ReleasePreferenceConfig_r16__connectedReporting : option ReleasePreferenceConfig_r16__connectedReporting__Type ;
}.
Definition ReleasePreferenceConfig_r16__list := (
 Nor ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Type ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__cond ::
 Opt ReleasePreferenceConfig_r16__connectedReporting__Type ReleasePreferenceConfig_r16__connectedReporting__cond ::
 nil).
Definition ReleasePreferenceConfig_r16__cond z := 
  ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__cond (ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16 z) /\
  opt_cond ReleasePreferenceConfig_r16__connectedReporting__cond (ReleasePreferenceConfig_r16__connectedReporting z) /\
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
Definition ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Format : T_Format ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__nat__Format ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1 ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F2 ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F1F2 ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__F2F1.

Opaque ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__cond ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Format.

Definition ReleasePreferenceConfig_r16__connectedReporting__Format : T_Format ReleasePreferenceConfig_r16__connectedReporting__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReleasePreferenceConfig_r16__connectedReporting__nat__Format ReleasePreferenceConfig_r16__connectedReporting__F1 ReleasePreferenceConfig_r16__connectedReporting__F2 ReleasePreferenceConfig_r16__connectedReporting__F1F2 ReleasePreferenceConfig_r16__connectedReporting__F2F1.

Opaque ReleasePreferenceConfig_r16__connectedReporting__cond ReleasePreferenceConfig_r16__connectedReporting__Format.


Definition ReleasePreferenceConfig_r16__Format_Type := Eval cbn in seq_format_prod ReleasePreferenceConfig_r16__list.
Definition ReleasePreferenceConfig_r16__Format_list : ReleasePreferenceConfig_r16__Format_Type :=
  (ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16__Format, (ReleasePreferenceConfig_r16__connectedReporting__Format, unit_format)).
Definition ReleasePreferenceConfig_r16__list__Format := (*Eval compute in *) seq_format ReleasePreferenceConfig_r16__list ReleasePreferenceConfig_r16__Format_list.
Definition ReleasePreferenceConfig_r16__F1 z :=
  (ReleasePreferenceConfig_r16__releasePreferenceProhibitTimer_r16 z, (ReleasePreferenceConfig_r16__connectedReporting z, tt)).
Definition ReleasePreferenceConfig_r16__F2 (y : seq_type ReleasePreferenceConfig_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ReleasePreferenceConfig_r16__Type i0 i1
  end.
Lemma ReleasePreferenceConfig_r16__F1F2_cond (z : ReleasePreferenceConfig_r16__Type)
  : ReleasePreferenceConfig_r16__cond z ->
  (seq_cond ReleasePreferenceConfig_r16__list (ReleasePreferenceConfig_r16__F1 z)).
intro H. unfold ReleasePreferenceConfig_r16__cond in H. simpl. auto. Qed.
Lemma ReleasePreferenceConfig_r16__F1F2_cond2 (z : ReleasePreferenceConfig_r16__Type)
 : ReleasePreferenceConfig_r16__F2 (ReleasePreferenceConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReleasePreferenceConfig_r16__F2F1_cond (y : seq_type ReleasePreferenceConfig_r16__list)
  : seq_cond ReleasePreferenceConfig_r16__list y ->
 (ReleasePreferenceConfig_r16__cond (ReleasePreferenceConfig_r16__F2 y)) /\  ReleasePreferenceConfig_r16__F1 (ReleasePreferenceConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReleasePreferenceConfig_r16__cond. simpl in *. auto.
 - simpl. unfold ReleasePreferenceConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReleasePreferenceConfig_r16__Format : T_Format ReleasePreferenceConfig_r16__Type ReleasePreferenceConfig_r16__cond :=
        proj2_format  ReleasePreferenceConfig_r16__cond ReleasePreferenceConfig_r16__list__Format
    ReleasePreferenceConfig_r16__F1 ReleasePreferenceConfig_r16__F2 ReleasePreferenceConfig_r16__F1F2_cond  ReleasePreferenceConfig_r16__F1F2_cond2 ReleasePreferenceConfig_r16__F2F1_cond.
Opaque ReleasePreferenceConfig_r16__cond ReleasePreferenceConfig_r16__Format.

