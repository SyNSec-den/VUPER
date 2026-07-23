Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRI_PUSCH_PowerControlId.

Opaque SRI_PUSCH_PowerControlId__cond SRI_PUSCH_PowerControlId__Format.

Require Import NR.PUSCH_PathlossReferenceRS_Id.

Opaque PUSCH_PathlossReferenceRS_Id__cond PUSCH_PathlossReferenceRS_Id__Format.

Require Import NR.P0_PUSCH_AlphaSetId.

Opaque P0_PUSCH_AlphaSetId__cond P0_PUSCH_AlphaSetId__Format.

Inductive SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Type : Set :=
 | SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i0
 | SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i1
.
Definition SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__cond := (fun (_ : SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Type) => True).
Lemma SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__nat__helper.

Definition SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1 t :=
  match t with
  | SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i0 => 0
  | SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i1 => 1
  end.
Definition SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F2 n :=
  match n with
  | 0 => SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i0
  | 1 => SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i1
  | _ => SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__i0
  end.
Lemma SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1F2 : forall x : SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Type, (SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1 x <= 1) /\ SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F2 (SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1 x) = x. imp_solve. Qed.
Lemma SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F2F1 : forall (y : nat) (H : y <= 1), SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1 (SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F2 y) = y. enum_solve H y. Qed.

Record SRI_PUSCH_PowerControl__Type : Set :=
  make__SRI_PUSCH_PowerControl__Type {
    SRI_PUSCH_PowerControl__sri_PUSCH_PowerControlId : SRI_PUSCH_PowerControlId__Type ;
    SRI_PUSCH_PowerControl__sri_PUSCH_PathlossReferenceRS_Id : PUSCH_PathlossReferenceRS_Id__Type ;
    SRI_PUSCH_PowerControl__sri_P0_PUSCH_AlphaSetId : P0_PUSCH_AlphaSetId__Type ;
    SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex : SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Type ;
}.
Definition SRI_PUSCH_PowerControl__list := (
 Nor SRI_PUSCH_PowerControlId__Type SRI_PUSCH_PowerControlId__cond ::
 Nor PUSCH_PathlossReferenceRS_Id__Type PUSCH_PathlossReferenceRS_Id__cond ::
 Nor P0_PUSCH_AlphaSetId__Type P0_PUSCH_AlphaSetId__cond ::
 Nor SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Type SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__cond ::
 nil).
Definition SRI_PUSCH_PowerControl__cond z := 
  SRI_PUSCH_PowerControlId__cond (SRI_PUSCH_PowerControl__sri_PUSCH_PowerControlId z) /\
  PUSCH_PathlossReferenceRS_Id__cond (SRI_PUSCH_PowerControl__sri_PUSCH_PathlossReferenceRS_Id z) /\
  P0_PUSCH_AlphaSetId__cond (SRI_PUSCH_PowerControl__sri_P0_PUSCH_AlphaSetId z) /\
  SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__cond (SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex z) /\
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
Definition SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Format : T_Format SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__nat__Format SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1 SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F2 SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F1F2 SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__F2F1.

Opaque SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__cond SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Format.


Definition SRI_PUSCH_PowerControl__Format_Type := Eval cbn in seq_format_prod SRI_PUSCH_PowerControl__list.
Definition SRI_PUSCH_PowerControl__Format_list : SRI_PUSCH_PowerControl__Format_Type :=
  (SRI_PUSCH_PowerControlId__Format, (PUSCH_PathlossReferenceRS_Id__Format, (P0_PUSCH_AlphaSetId__Format, (SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex__Format, unit_format)))).
Definition SRI_PUSCH_PowerControl__list__Format := (*Eval compute in *) seq_format SRI_PUSCH_PowerControl__list SRI_PUSCH_PowerControl__Format_list.
Definition SRI_PUSCH_PowerControl__F1 z :=
  (SRI_PUSCH_PowerControl__sri_PUSCH_PowerControlId z, (SRI_PUSCH_PowerControl__sri_PUSCH_PathlossReferenceRS_Id z, (SRI_PUSCH_PowerControl__sri_P0_PUSCH_AlphaSetId z, (SRI_PUSCH_PowerControl__sri_PUSCH_ClosedLoopIndex z, tt)))).
Definition SRI_PUSCH_PowerControl__F2 (y : seq_type SRI_PUSCH_PowerControl__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SRI_PUSCH_PowerControl__Type i0 i1 i2 i3
  end.
Lemma SRI_PUSCH_PowerControl__F1F2_cond (z : SRI_PUSCH_PowerControl__Type)
  : SRI_PUSCH_PowerControl__cond z ->
  (seq_cond SRI_PUSCH_PowerControl__list (SRI_PUSCH_PowerControl__F1 z)).
intro H. unfold SRI_PUSCH_PowerControl__cond in H. simpl. auto. Qed.
Lemma SRI_PUSCH_PowerControl__F1F2_cond2 (z : SRI_PUSCH_PowerControl__Type)
 : SRI_PUSCH_PowerControl__F2 (SRI_PUSCH_PowerControl__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRI_PUSCH_PowerControl__F2F1_cond (y : seq_type SRI_PUSCH_PowerControl__list)
  : seq_cond SRI_PUSCH_PowerControl__list y ->
 (SRI_PUSCH_PowerControl__cond (SRI_PUSCH_PowerControl__F2 y)) /\  SRI_PUSCH_PowerControl__F1 (SRI_PUSCH_PowerControl__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRI_PUSCH_PowerControl__cond. simpl in *. auto.
 - simpl. unfold SRI_PUSCH_PowerControl__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRI_PUSCH_PowerControl__Format : T_Format SRI_PUSCH_PowerControl__Type SRI_PUSCH_PowerControl__cond :=
        proj2_format  SRI_PUSCH_PowerControl__cond SRI_PUSCH_PowerControl__list__Format
    SRI_PUSCH_PowerControl__F1 SRI_PUSCH_PowerControl__F2 SRI_PUSCH_PowerControl__F1F2_cond  SRI_PUSCH_PowerControl__F1F2_cond2 SRI_PUSCH_PowerControl__F2F1_cond.
Opaque SRI_PUSCH_PowerControl__cond SRI_PUSCH_PowerControl__Format.

