Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.AdditionalSpectrumEmission.

Opaque AdditionalSpectrumEmission__cond AdditionalSpectrumEmission__Format.

Record NR_NS_PmaxValue__Type : Set :=
  make__NR_NS_PmaxValue__Type {
    NR_NS_PmaxValue__additionalPmax : option P_Max__Type ;
    NR_NS_PmaxValue__additionalSpectrumEmission : AdditionalSpectrumEmission__Type ;
}.
Definition NR_NS_PmaxValue__list := (
 Opt P_Max__Type P_Max__cond ::
 Nor AdditionalSpectrumEmission__Type AdditionalSpectrumEmission__cond ::
 nil).
Definition NR_NS_PmaxValue__cond z := 
  opt_cond P_Max__cond (NR_NS_PmaxValue__additionalPmax z) /\
  AdditionalSpectrumEmission__cond (NR_NS_PmaxValue__additionalSpectrumEmission z) /\
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

Definition NR_NS_PmaxValue__Format_Type := Eval cbn in seq_format_prod NR_NS_PmaxValue__list.
Definition NR_NS_PmaxValue__Format_list : NR_NS_PmaxValue__Format_Type :=
  (P_Max__Format, (AdditionalSpectrumEmission__Format, unit_format)).
Definition NR_NS_PmaxValue__list__Format := (*Eval compute in *) seq_format NR_NS_PmaxValue__list NR_NS_PmaxValue__Format_list.
Definition NR_NS_PmaxValue__F1 z :=
  (NR_NS_PmaxValue__additionalPmax z, (NR_NS_PmaxValue__additionalSpectrumEmission z, tt)).
Definition NR_NS_PmaxValue__F2 (y : seq_type NR_NS_PmaxValue__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NR_NS_PmaxValue__Type i0 i1
  end.
Lemma NR_NS_PmaxValue__F1F2_cond (z : NR_NS_PmaxValue__Type)
  : NR_NS_PmaxValue__cond z ->
  (seq_cond NR_NS_PmaxValue__list (NR_NS_PmaxValue__F1 z)).
intro H. unfold NR_NS_PmaxValue__cond in H. simpl. auto. Qed.
Lemma NR_NS_PmaxValue__F1F2_cond2 (z : NR_NS_PmaxValue__Type)
 : NR_NS_PmaxValue__F2 (NR_NS_PmaxValue__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NR_NS_PmaxValue__F2F1_cond (y : seq_type NR_NS_PmaxValue__list)
  : seq_cond NR_NS_PmaxValue__list y ->
 (NR_NS_PmaxValue__cond (NR_NS_PmaxValue__F2 y)) /\  NR_NS_PmaxValue__F1 (NR_NS_PmaxValue__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NR_NS_PmaxValue__cond. simpl in *. auto.
 - simpl. unfold NR_NS_PmaxValue__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NR_NS_PmaxValue__Format : T_Format NR_NS_PmaxValue__Type NR_NS_PmaxValue__cond :=
        proj2_format  NR_NS_PmaxValue__cond NR_NS_PmaxValue__list__Format
    NR_NS_PmaxValue__F1 NR_NS_PmaxValue__F2 NR_NS_PmaxValue__F1F2_cond  NR_NS_PmaxValue__F1F2_cond2 NR_NS_PmaxValue__F2F1_cond.
Opaque NR_NS_PmaxValue__cond NR_NS_PmaxValue__Format.

