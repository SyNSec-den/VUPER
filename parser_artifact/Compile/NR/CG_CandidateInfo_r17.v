Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.CG_CandidateInfoId_r17.

Opaque CG_CandidateInfoId_r17__cond CG_CandidateInfoId_r17__Format.

Record CG_CandidateInfo_r17__Type : Set :=
  make__CG_CandidateInfo_r17__Type {
    CG_CandidateInfo_r17__cg_CandidateInfoId_r17 : CG_CandidateInfoId_r17__Type ;
    CG_CandidateInfo_r17__candidateCG_Config_r17 : octet_string ;
}.
Definition CG_CandidateInfo_r17__list := (
 Nor CG_CandidateInfoId_r17__Type CG_CandidateInfoId_r17__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CG_CandidateInfo_r17__cond z := 
  CG_CandidateInfoId_r17__cond (CG_CandidateInfo_r17__cg_CandidateInfoId_r17 z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_CandidateInfo_r17__candidateCG_Config_r17 z) /\
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

Definition CG_CandidateInfo_r17__Format_Type := Eval cbn in seq_format_prod CG_CandidateInfo_r17__list.
Definition CG_CandidateInfo_r17__Format_list : CG_CandidateInfo_r17__Format_Type :=
  (CG_CandidateInfoId_r17__Format, (octet_string_nc__Format, unit_format)).
Definition CG_CandidateInfo_r17__list__Format := (*Eval compute in *) seq_format CG_CandidateInfo_r17__list CG_CandidateInfo_r17__Format_list.
Definition CG_CandidateInfo_r17__F1 z :=
  (CG_CandidateInfo_r17__cg_CandidateInfoId_r17 z, (CG_CandidateInfo_r17__candidateCG_Config_r17 z, tt)).
Definition CG_CandidateInfo_r17__F2 (y : seq_type CG_CandidateInfo_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_CandidateInfo_r17__Type i0 i1
  end.
Lemma CG_CandidateInfo_r17__F1F2_cond (z : CG_CandidateInfo_r17__Type)
  : CG_CandidateInfo_r17__cond z ->
  (seq_cond CG_CandidateInfo_r17__list (CG_CandidateInfo_r17__F1 z)).
intro H. unfold CG_CandidateInfo_r17__cond in H. simpl. auto. Qed.
Lemma CG_CandidateInfo_r17__F1F2_cond2 (z : CG_CandidateInfo_r17__Type)
 : CG_CandidateInfo_r17__F2 (CG_CandidateInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_CandidateInfo_r17__F2F1_cond (y : seq_type CG_CandidateInfo_r17__list)
  : seq_cond CG_CandidateInfo_r17__list y ->
 (CG_CandidateInfo_r17__cond (CG_CandidateInfo_r17__F2 y)) /\  CG_CandidateInfo_r17__F1 (CG_CandidateInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_CandidateInfo_r17__cond. simpl in *. auto.
 - simpl. unfold CG_CandidateInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_CandidateInfo_r17__Format : T_Format CG_CandidateInfo_r17__Type CG_CandidateInfo_r17__cond :=
        proj2_format  CG_CandidateInfo_r17__cond CG_CandidateInfo_r17__list__Format
    CG_CandidateInfo_r17__F1 CG_CandidateInfo_r17__F2 CG_CandidateInfo_r17__F1F2_cond  CG_CandidateInfo_r17__F1F2_cond2 CG_CandidateInfo_r17__F2F1_cond.
Opaque CG_CandidateInfo_r17__cond CG_CandidateInfo_r17__Format.

