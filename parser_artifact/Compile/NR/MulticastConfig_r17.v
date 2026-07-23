Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.PDSCH_HARQ_ACK_CodebookList_r16.
Definition MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Type := SetupRelease__Type PDSCH_HARQ_ACK_CodebookList_r16__Type.
Definition MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__cond := SetupRelease__cond _ PDSCH_HARQ_ACK_CodebookList_r16__cond.
Definition MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Format : T_Format MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Type MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__cond := SetupRelease__Format _ _ PDSCH_HARQ_ACK_CodebookList_r16__Format.
Opaque MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__cond MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Format.

Inductive MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Type : Set :=
 | MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode1
 | MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode2
.
Definition MulticastConfig_r17__type1_Codebook_GenerationMode_r17__cond := (fun (_ : MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Type) => True).
Lemma MulticastConfig_r17__type1_Codebook_GenerationMode_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MulticastConfig_r17__type1_Codebook_GenerationMode_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MulticastConfig_r17__type1_Codebook_GenerationMode_r17__nat__helper.

Definition MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1 t :=
  match t with
  | MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode1 => 0
  | MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode2 => 1
  end.
Definition MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F2 n :=
  match n with
  | 0 => MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode1
  | 1 => MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode2
  | _ => MulticastConfig_r17__type1_Codebook_GenerationMode_r17__mode1
  end.
Lemma MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1F2 : forall x : MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Type, (MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1 x <= 1) /\ MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F2 (MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1 x) = x. imp_solve. Qed.
Lemma MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F2F1 : forall (y : nat) (H : y <= 1), MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1 (MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F2 y) = y. enum_solve H y. Qed.

Record MulticastConfig_r17__Type : Set :=
  make__MulticastConfig_r17__Type {
    MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17 : option MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Type ;
    MulticastConfig_r17__type1_Codebook_GenerationMode_r17 : option MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Type ;
}.
Definition MulticastConfig_r17__list := (
 Opt MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Type MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__cond ::
 Opt MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Type MulticastConfig_r17__type1_Codebook_GenerationMode_r17__cond ::
 nil).
Definition MulticastConfig_r17__cond z := 
  opt_cond MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__cond (MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17 z) /\
  opt_cond MulticastConfig_r17__type1_Codebook_GenerationMode_r17__cond (MulticastConfig_r17__type1_Codebook_GenerationMode_r17 z) /\
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
Opaque MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__cond MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Format.

Definition MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Format : T_Format MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MulticastConfig_r17__type1_Codebook_GenerationMode_r17__nat__Format MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1 MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F2 MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F1F2 MulticastConfig_r17__type1_Codebook_GenerationMode_r17__F2F1.

Opaque MulticastConfig_r17__type1_Codebook_GenerationMode_r17__cond MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Format.


Definition MulticastConfig_r17__Format_Type := Eval cbn in seq_format_prod MulticastConfig_r17__list.
Definition MulticastConfig_r17__Format_list : MulticastConfig_r17__Format_Type :=
  (MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17__Format, (MulticastConfig_r17__type1_Codebook_GenerationMode_r17__Format, unit_format)).
Definition MulticastConfig_r17__list__Format := (*Eval compute in *) seq_format MulticastConfig_r17__list MulticastConfig_r17__Format_list.
Definition MulticastConfig_r17__F1 z :=
  (MulticastConfig_r17__pdsch_HARQ_ACK_CodebookListMulticast_r17 z, (MulticastConfig_r17__type1_Codebook_GenerationMode_r17 z, tt)).
Definition MulticastConfig_r17__F2 (y : seq_type MulticastConfig_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MulticastConfig_r17__Type i0 i1
  end.
Lemma MulticastConfig_r17__F1F2_cond (z : MulticastConfig_r17__Type)
  : MulticastConfig_r17__cond z ->
  (seq_cond MulticastConfig_r17__list (MulticastConfig_r17__F1 z)).
intro H. unfold MulticastConfig_r17__cond in H. simpl. auto. Qed.
Lemma MulticastConfig_r17__F1F2_cond2 (z : MulticastConfig_r17__Type)
 : MulticastConfig_r17__F2 (MulticastConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MulticastConfig_r17__F2F1_cond (y : seq_type MulticastConfig_r17__list)
  : seq_cond MulticastConfig_r17__list y ->
 (MulticastConfig_r17__cond (MulticastConfig_r17__F2 y)) /\  MulticastConfig_r17__F1 (MulticastConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MulticastConfig_r17__cond. simpl in *. auto.
 - simpl. unfold MulticastConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MulticastConfig_r17__Format : T_Format MulticastConfig_r17__Type MulticastConfig_r17__cond :=
        proj2_format  MulticastConfig_r17__cond MulticastConfig_r17__list__Format
    MulticastConfig_r17__F1 MulticastConfig_r17__F2 MulticastConfig_r17__F1F2_cond  MulticastConfig_r17__F1F2_cond2 MulticastConfig_r17__F2F1_cond.
Opaque MulticastConfig_r17__cond MulticastConfig_r17__Format.

