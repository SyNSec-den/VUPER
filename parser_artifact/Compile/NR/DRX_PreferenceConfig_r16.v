Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Type : Set :=
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0dot5
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s1
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s2
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s3
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s4
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s5
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s6
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s7
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s8
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s9
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s10
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s20
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s30
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__spare2
 | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__spare1
.
Definition DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__cond := (fun (_ : DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Type) => True).
Lemma DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__nat__helper.

Definition DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1 t :=
  match t with
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0 => 0
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0dot5 => 1
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s1 => 2
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s2 => 3
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s3 => 4
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s4 => 5
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s5 => 6
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s6 => 7
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s7 => 8
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s8 => 9
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s9 => 10
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s10 => 11
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s20 => 12
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s30 => 13
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__spare2 => 14
  | DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__spare1 => 15
  end.
Definition DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F2 n :=
  match n with
  | 0 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0
  | 1 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0dot5
  | 2 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s1
  | 3 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s2
  | 4 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s3
  | 5 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s4
  | 6 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s5
  | 7 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s6
  | 8 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s7
  | 9 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s8
  | 10 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s9
  | 11 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s10
  | 12 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s20
  | 13 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s30
  | 14 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__spare2
  | 15 => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__spare1
  | _ => DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__s0
  end.
Lemma DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1F2 : forall x : DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Type, (DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1 x <= 15) /\ DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F2 (DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F2F1 : forall (y : nat) (H : y <= 15), DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1 (DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F2 y) = y. enum_solve H y. Qed.

Record DRX_PreferenceConfig_r16__Type : Set :=
  make__DRX_PreferenceConfig_r16__Type {
    DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16 : DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Type ;
}.
Definition DRX_PreferenceConfig_r16__list := (
 Nor DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Type DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__cond ::
 nil).
Definition DRX_PreferenceConfig_r16__cond z := 
  DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__cond (DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16 z) /\
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
Definition DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Format : T_Format DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__nat__Format DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1 DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F2 DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F1F2 DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__F2F1.

Opaque DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__cond DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Format.


Definition DRX_PreferenceConfig_r16__Format_Type := Eval cbn in seq_format_prod DRX_PreferenceConfig_r16__list.
Definition DRX_PreferenceConfig_r16__Format_list : DRX_PreferenceConfig_r16__Format_Type :=
  (DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16__Format, unit_format).
Definition DRX_PreferenceConfig_r16__list__Format := (*Eval compute in *) seq_format DRX_PreferenceConfig_r16__list DRX_PreferenceConfig_r16__Format_list.
Definition DRX_PreferenceConfig_r16__F1 z :=
  (DRX_PreferenceConfig_r16__drx_PreferenceProhibitTimer_r16 z, tt).
Definition DRX_PreferenceConfig_r16__F2 (y : seq_type DRX_PreferenceConfig_r16__list) :=
  match y with
  | (i0, _)=>
    make__DRX_PreferenceConfig_r16__Type i0
  end.
Lemma DRX_PreferenceConfig_r16__F1F2_cond (z : DRX_PreferenceConfig_r16__Type)
  : DRX_PreferenceConfig_r16__cond z ->
  (seq_cond DRX_PreferenceConfig_r16__list (DRX_PreferenceConfig_r16__F1 z)).
intro H. unfold DRX_PreferenceConfig_r16__cond in H. simpl. auto. Qed.
Lemma DRX_PreferenceConfig_r16__F1F2_cond2 (z : DRX_PreferenceConfig_r16__Type)
 : DRX_PreferenceConfig_r16__F2 (DRX_PreferenceConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_PreferenceConfig_r16__F2F1_cond (y : seq_type DRX_PreferenceConfig_r16__list)
  : seq_cond DRX_PreferenceConfig_r16__list y ->
 (DRX_PreferenceConfig_r16__cond (DRX_PreferenceConfig_r16__F2 y)) /\  DRX_PreferenceConfig_r16__F1 (DRX_PreferenceConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_PreferenceConfig_r16__cond. simpl in *. auto.
 - simpl. unfold DRX_PreferenceConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_PreferenceConfig_r16__Format : T_Format DRX_PreferenceConfig_r16__Type DRX_PreferenceConfig_r16__cond :=
        proj2_format  DRX_PreferenceConfig_r16__cond DRX_PreferenceConfig_r16__list__Format
    DRX_PreferenceConfig_r16__F1 DRX_PreferenceConfig_r16__F2 DRX_PreferenceConfig_r16__F1F2_cond  DRX_PreferenceConfig_r16__F1F2_cond2 DRX_PreferenceConfig_r16__F2F1_cond.
Opaque DRX_PreferenceConfig_r16__cond DRX_PreferenceConfig_r16__Format.

