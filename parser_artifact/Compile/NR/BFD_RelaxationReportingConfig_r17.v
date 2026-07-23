Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Type : Set :=
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0dot5
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s1
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s2
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s5
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s10
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s20
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s30
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s60
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s90
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s120
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s300
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s600
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__infinity
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__spare2
 | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__spare1
.
Definition BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__cond := (fun (_ : BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Type) => True).
Lemma BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__nat__helper.

Definition BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1 t :=
  match t with
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0 => 0
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0dot5 => 1
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s1 => 2
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s2 => 3
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s5 => 4
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s10 => 5
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s20 => 6
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s30 => 7
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s60 => 8
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s90 => 9
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s120 => 10
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s300 => 11
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s600 => 12
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__infinity => 13
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__spare2 => 14
  | BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__spare1 => 15
  end.
Definition BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F2 n :=
  match n with
  | 0 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0
  | 1 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0dot5
  | 2 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s1
  | 3 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s2
  | 4 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s5
  | 5 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s10
  | 6 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s20
  | 7 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s30
  | 8 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s60
  | 9 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s90
  | 10 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s120
  | 11 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s300
  | 12 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s600
  | 13 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__infinity
  | 14 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__spare2
  | 15 => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__spare1
  | _ => BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__s0
  end.
Lemma BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1F2 : forall x : BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Type, (BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1 x <= 15) /\ BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F2 (BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F2F1 : forall (y : nat) (H : y <= 15), BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1 (BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Record BFD_RelaxationReportingConfig_r17__Type : Set :=
  make__BFD_RelaxationReportingConfig_r17__Type {
    BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer : BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Type ;
}.
Definition BFD_RelaxationReportingConfig_r17__list := (
 Nor BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Type BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__cond ::
 nil).
Definition BFD_RelaxationReportingConfig_r17__cond z := 
  BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__cond (BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer z) /\
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
Definition BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Format : T_Format BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__nat__Format BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1 BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F2 BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F1F2 BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__F2F1.

Opaque BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__cond BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Format.


Definition BFD_RelaxationReportingConfig_r17__Format_Type := Eval cbn in seq_format_prod BFD_RelaxationReportingConfig_r17__list.
Definition BFD_RelaxationReportingConfig_r17__Format_list : BFD_RelaxationReportingConfig_r17__Format_Type :=
  (BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer__Format, unit_format).
Definition BFD_RelaxationReportingConfig_r17__list__Format := (*Eval compute in *) seq_format BFD_RelaxationReportingConfig_r17__list BFD_RelaxationReportingConfig_r17__Format_list.
Definition BFD_RelaxationReportingConfig_r17__F1 z :=
  (BFD_RelaxationReportingConfig_r17__bfd_RelaxtionReportingProhibitTimer z, tt).
Definition BFD_RelaxationReportingConfig_r17__F2 (y : seq_type BFD_RelaxationReportingConfig_r17__list) :=
  match y with
  | (i0, _)=>
    make__BFD_RelaxationReportingConfig_r17__Type i0
  end.
Lemma BFD_RelaxationReportingConfig_r17__F1F2_cond (z : BFD_RelaxationReportingConfig_r17__Type)
  : BFD_RelaxationReportingConfig_r17__cond z ->
  (seq_cond BFD_RelaxationReportingConfig_r17__list (BFD_RelaxationReportingConfig_r17__F1 z)).
intro H. unfold BFD_RelaxationReportingConfig_r17__cond in H. simpl. auto. Qed.
Lemma BFD_RelaxationReportingConfig_r17__F1F2_cond2 (z : BFD_RelaxationReportingConfig_r17__Type)
 : BFD_RelaxationReportingConfig_r17__F2 (BFD_RelaxationReportingConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BFD_RelaxationReportingConfig_r17__F2F1_cond (y : seq_type BFD_RelaxationReportingConfig_r17__list)
  : seq_cond BFD_RelaxationReportingConfig_r17__list y ->
 (BFD_RelaxationReportingConfig_r17__cond (BFD_RelaxationReportingConfig_r17__F2 y)) /\  BFD_RelaxationReportingConfig_r17__F1 (BFD_RelaxationReportingConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BFD_RelaxationReportingConfig_r17__cond. simpl in *. auto.
 - simpl. unfold BFD_RelaxationReportingConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BFD_RelaxationReportingConfig_r17__Format : T_Format BFD_RelaxationReportingConfig_r17__Type BFD_RelaxationReportingConfig_r17__cond :=
        proj2_format  BFD_RelaxationReportingConfig_r17__cond BFD_RelaxationReportingConfig_r17__list__Format
    BFD_RelaxationReportingConfig_r17__F1 BFD_RelaxationReportingConfig_r17__F2 BFD_RelaxationReportingConfig_r17__F1F2_cond  BFD_RelaxationReportingConfig_r17__F1F2_cond2 BFD_RelaxationReportingConfig_r17__F2F1_cond.
Opaque BFD_RelaxationReportingConfig_r17__cond BFD_RelaxationReportingConfig_r17__Format.

