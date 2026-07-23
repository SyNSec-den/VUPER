Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ShortI_RNTI_Value.

Opaque ShortI_RNTI_Value__cond ShortI_RNTI_Value__Format.

Definition RRCResumeRequest_IEs__resumeMAC_I__Type := bit_string_fixed.
Definition RRCResumeRequest_IEs__resumeMAC_I__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.ResumeCause.

Opaque ResumeCause__cond ResumeCause__Format.

Definition RRCResumeRequest_IEs__spare__Type := bit_string_fixed.
Definition RRCResumeRequest_IEs__spare__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 1 /\ bit_string_len_prop (fst z) (snd z)).
Record RRCResumeRequest_IEs__Type : Set :=
  make__RRCResumeRequest_IEs__Type {
    RRCResumeRequest_IEs__resumeIdentity : ShortI_RNTI_Value__Type ;
    RRCResumeRequest_IEs__resumeMAC_I : RRCResumeRequest_IEs__resumeMAC_I__Type ;
    RRCResumeRequest_IEs__resumeCause : ResumeCause__Type ;
    RRCResumeRequest_IEs__spare : RRCResumeRequest_IEs__spare__Type ;
}.
Definition RRCResumeRequest_IEs__list := (
 Nor ShortI_RNTI_Value__Type ShortI_RNTI_Value__cond ::
 Nor RRCResumeRequest_IEs__resumeMAC_I__Type RRCResumeRequest_IEs__resumeMAC_I__cond ::
 Nor ResumeCause__Type ResumeCause__cond ::
 Nor RRCResumeRequest_IEs__spare__Type RRCResumeRequest_IEs__spare__cond ::
 nil).
Definition RRCResumeRequest_IEs__cond z := 
  ShortI_RNTI_Value__cond (RRCResumeRequest_IEs__resumeIdentity z) /\
  RRCResumeRequest_IEs__resumeMAC_I__cond (RRCResumeRequest_IEs__resumeMAC_I z) /\
  ResumeCause__cond (RRCResumeRequest_IEs__resumeCause z) /\
  RRCResumeRequest_IEs__spare__cond (RRCResumeRequest_IEs__spare z) /\
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
Definition RRCResumeRequest_IEs__resumeMAC_I__Format : T_Format RRCResumeRequest_IEs__resumeMAC_I__Type RRCResumeRequest_IEs__resumeMAC_I__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque RRCResumeRequest_IEs__resumeMAC_I__cond RRCResumeRequest_IEs__resumeMAC_I__Format.

Definition RRCResumeRequest_IEs__spare__Format : T_Format RRCResumeRequest_IEs__spare__Type RRCResumeRequest_IEs__spare__cond := (* Eval compute in *) bit_string_fixed_format 1.
Opaque RRCResumeRequest_IEs__spare__cond RRCResumeRequest_IEs__spare__Format.


Definition RRCResumeRequest_IEs__Format_Type := Eval cbn in seq_format_prod RRCResumeRequest_IEs__list.
Definition RRCResumeRequest_IEs__Format_list : RRCResumeRequest_IEs__Format_Type :=
  (ShortI_RNTI_Value__Format, (RRCResumeRequest_IEs__resumeMAC_I__Format, (ResumeCause__Format, (RRCResumeRequest_IEs__spare__Format, unit_format)))).
Definition RRCResumeRequest_IEs__list__Format := (*Eval compute in *) seq_format RRCResumeRequest_IEs__list RRCResumeRequest_IEs__Format_list.
Definition RRCResumeRequest_IEs__F1 z :=
  (RRCResumeRequest_IEs__resumeIdentity z, (RRCResumeRequest_IEs__resumeMAC_I z, (RRCResumeRequest_IEs__resumeCause z, (RRCResumeRequest_IEs__spare z, tt)))).
Definition RRCResumeRequest_IEs__F2 (y : seq_type RRCResumeRequest_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RRCResumeRequest_IEs__Type i0 i1 i2 i3
  end.
Lemma RRCResumeRequest_IEs__F1F2_cond (z : RRCResumeRequest_IEs__Type)
  : RRCResumeRequest_IEs__cond z ->
  (seq_cond RRCResumeRequest_IEs__list (RRCResumeRequest_IEs__F1 z)).
intro H. unfold RRCResumeRequest_IEs__cond in H. simpl. auto. Qed.
Lemma RRCResumeRequest_IEs__F1F2_cond2 (z : RRCResumeRequest_IEs__Type)
 : RRCResumeRequest_IEs__F2 (RRCResumeRequest_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResumeRequest_IEs__F2F1_cond (y : seq_type RRCResumeRequest_IEs__list)
  : seq_cond RRCResumeRequest_IEs__list y ->
 (RRCResumeRequest_IEs__cond (RRCResumeRequest_IEs__F2 y)) /\  RRCResumeRequest_IEs__F1 (RRCResumeRequest_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResumeRequest_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCResumeRequest_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResumeRequest_IEs__Format : T_Format RRCResumeRequest_IEs__Type RRCResumeRequest_IEs__cond :=
        proj2_format  RRCResumeRequest_IEs__cond RRCResumeRequest_IEs__list__Format
    RRCResumeRequest_IEs__F1 RRCResumeRequest_IEs__F2 RRCResumeRequest_IEs__F1F2_cond  RRCResumeRequest_IEs__F1F2_cond2 RRCResumeRequest_IEs__F2F1_cond.
Opaque RRCResumeRequest_IEs__cond RRCResumeRequest_IEs__Format.

