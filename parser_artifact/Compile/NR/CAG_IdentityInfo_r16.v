Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition CAG_IdentityInfo_r16__cag_Identity_r16__Type := bit_string_fixed.
Definition CAG_IdentityInfo_r16__cag_Identity_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 32 /\ bit_string_len_prop (fst z) (snd z)).
Inductive CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type : Set :=
 | CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__true
.
Definition CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__cond := (fun (_ : CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type) => True).
Lemma CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__nat__helper.

Definition CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1 t :=
  match t with
  | CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__true => 0
  end.
Definition CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2 n :=
  match n with
  | 0 => CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__true
  | _ => CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__true
  end.
Lemma CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1F2 : forall x : CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type, (CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1 x <= 0) /\ CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2 (CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1 x) = x. imp_solve. Qed.
Lemma CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2F1 : forall (y : nat) (H : y <= 0), CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1 (CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2 y) = y. enum_solve H y. Qed.

Record CAG_IdentityInfo_r16__Type : Set :=
  make__CAG_IdentityInfo_r16__Type {
    CAG_IdentityInfo_r16__cag_Identity_r16 : CAG_IdentityInfo_r16__cag_Identity_r16__Type ;
    CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16 : option CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type ;
}.
Definition CAG_IdentityInfo_r16__list := (
 Nor CAG_IdentityInfo_r16__cag_Identity_r16__Type CAG_IdentityInfo_r16__cag_Identity_r16__cond ::
 Opt CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__cond ::
 nil).
Definition CAG_IdentityInfo_r16__cond z := 
  CAG_IdentityInfo_r16__cag_Identity_r16__cond (CAG_IdentityInfo_r16__cag_Identity_r16 z) /\
  opt_cond CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__cond (CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16 z) /\
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
Definition CAG_IdentityInfo_r16__cag_Identity_r16__Format : T_Format CAG_IdentityInfo_r16__cag_Identity_r16__Type CAG_IdentityInfo_r16__cag_Identity_r16__cond := (* Eval compute in *) bit_string_fixed_format 32.
Opaque CAG_IdentityInfo_r16__cag_Identity_r16__cond CAG_IdentityInfo_r16__cag_Identity_r16__Format.

Definition CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Format : T_Format CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__nat__Format CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1 CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2 CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1F2 CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2F1.

Opaque CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__cond CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Format.


Definition CAG_IdentityInfo_r16__Format_Type := Eval cbn in seq_format_prod CAG_IdentityInfo_r16__list.
Definition CAG_IdentityInfo_r16__Format_list : CAG_IdentityInfo_r16__Format_Type :=
  (CAG_IdentityInfo_r16__cag_Identity_r16__Format, (CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Format, unit_format)).
Definition CAG_IdentityInfo_r16__list__Format := (*Eval compute in *) seq_format CAG_IdentityInfo_r16__list CAG_IdentityInfo_r16__Format_list.
Definition CAG_IdentityInfo_r16__F1 z :=
  (CAG_IdentityInfo_r16__cag_Identity_r16 z, (CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16 z, tt)).
Definition CAG_IdentityInfo_r16__F2 (y : seq_type CAG_IdentityInfo_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CAG_IdentityInfo_r16__Type i0 i1
  end.
Lemma CAG_IdentityInfo_r16__F1F2_cond (z : CAG_IdentityInfo_r16__Type)
  : CAG_IdentityInfo_r16__cond z ->
  (seq_cond CAG_IdentityInfo_r16__list (CAG_IdentityInfo_r16__F1 z)).
intro H. unfold CAG_IdentityInfo_r16__cond in H. simpl. auto. Qed.
Lemma CAG_IdentityInfo_r16__F1F2_cond2 (z : CAG_IdentityInfo_r16__Type)
 : CAG_IdentityInfo_r16__F2 (CAG_IdentityInfo_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CAG_IdentityInfo_r16__F2F1_cond (y : seq_type CAG_IdentityInfo_r16__list)
  : seq_cond CAG_IdentityInfo_r16__list y ->
 (CAG_IdentityInfo_r16__cond (CAG_IdentityInfo_r16__F2 y)) /\  CAG_IdentityInfo_r16__F1 (CAG_IdentityInfo_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CAG_IdentityInfo_r16__cond. simpl in *. auto.
 - simpl. unfold CAG_IdentityInfo_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CAG_IdentityInfo_r16__Format : T_Format CAG_IdentityInfo_r16__Type CAG_IdentityInfo_r16__cond :=
        proj2_format  CAG_IdentityInfo_r16__cond CAG_IdentityInfo_r16__list__Format
    CAG_IdentityInfo_r16__F1 CAG_IdentityInfo_r16__F2 CAG_IdentityInfo_r16__F1F2_cond  CAG_IdentityInfo_r16__F1F2_cond2 CAG_IdentityInfo_r16__F2F1_cond.
Opaque CAG_IdentityInfo_r16__cond CAG_IdentityInfo_r16__Format.

