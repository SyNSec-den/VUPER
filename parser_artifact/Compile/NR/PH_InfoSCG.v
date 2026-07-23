Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.PH_UplinkCarrierSCG.

Opaque PH_UplinkCarrierSCG__cond PH_UplinkCarrierSCG__Format.

Require Import NR.PH_UplinkCarrierSCG.

Opaque PH_UplinkCarrierSCG__cond PH_UplinkCarrierSCG__Format.

Inductive PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Type : Set :=
 | PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__enabled
.
Definition PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__cond := (fun (_ : PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Type) => True).
Lemma PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__nat__helper.

Definition PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1 t :=
  match t with
  | PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__enabled => 0
  end.
Definition PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F2 n :=
  match n with
  | 0 => PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__enabled
  | _ => PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__enabled
  end.
Lemma PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1F2 : forall x : PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Type, (PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1 x <= 0) /\ PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F2 (PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1 x) = x. imp_solve. Qed.
Lemma PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F2F1 : forall (y : nat) (H : y <= 0), PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1 (PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F2 y) = y. enum_solve H y. Qed.

Record PH_InfoSCG__ext0O__Type : Set :=
  make__PH_InfoSCG__ext0O__Type {
    PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17 : option PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Type ;
}.
Definition PH_InfoSCG__ext0O__list := (
 Opt PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Type PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__cond ::
 nil).
Definition PH_InfoSCG__ext0O__cond z := 
  opt_cond PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__cond (PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17 z) /\
  True.

Definition PH_InfoSCG__ext0__Type := PH_InfoSCG__ext0O__Type.
Definition PH_InfoSCG__ext0__cond := PH_InfoSCG__ext0O__cond.

Record PH_InfoSCG__Type : Set :=
  make__PH_InfoSCG__Type {
    PH_InfoSCG__servCellIndex : ServCellIndex__Type ;
    PH_InfoSCG__ph_Uplink : PH_UplinkCarrierSCG__Type ;
    PH_InfoSCG__ph_SupplementaryUplink : option PH_UplinkCarrierSCG__Type ;
    PH_InfoSCG__ext0 : option PH_InfoSCG__ext0__Type ;
}.
Definition PH_InfoSCG__root_list : list seq_elem := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor PH_UplinkCarrierSCG__Type PH_UplinkCarrierSCG__cond ::
 Opt PH_UplinkCarrierSCG__Type PH_UplinkCarrierSCG__cond ::
 nil).
Definition PH_InfoSCG__ext_list : list typ := (
  typ_cons PH_InfoSCG__ext0__Type PH_InfoSCG__ext0__cond ::
  nil).
Definition PH_InfoSCG__cond (z : PH_InfoSCG__Type) := 
(  ServCellIndex__cond (PH_InfoSCG__servCellIndex z) /\
  PH_UplinkCarrierSCG__cond (PH_InfoSCG__ph_Uplink z) /\
  opt_cond PH_UplinkCarrierSCG__cond (PH_InfoSCG__ph_SupplementaryUplink z) /\
  True) /\ 
(  opt_cond PH_InfoSCG__ext0__cond (PH_InfoSCG__ext0 z) /\
  True).


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
Definition PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Format : T_Format PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__nat__Format PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1 PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F2 PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F1F2 PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__F2F1.

Opaque PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__cond PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Format.


Definition PH_InfoSCG__ext0O__Format_Type := Eval cbn in seq_format_prod PH_InfoSCG__ext0O__list.
Definition PH_InfoSCG__ext0O__Format_list : PH_InfoSCG__ext0O__Format_Type :=
  (PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17__Format, unit_format).
Definition PH_InfoSCG__ext0O__list__Format := (*Eval compute in *) seq_format PH_InfoSCG__ext0O__list PH_InfoSCG__ext0O__Format_list.
Definition PH_InfoSCG__ext0O__F1 z :=
  (PH_InfoSCG__ext0O__twoSRS_PUSCH_Repetition_r17 z, tt).
Definition PH_InfoSCG__ext0O__F2 (y : seq_type PH_InfoSCG__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PH_InfoSCG__ext0O__Type i0
  end.
Lemma PH_InfoSCG__ext0O__F1F2_cond (z : PH_InfoSCG__ext0O__Type)
  : PH_InfoSCG__ext0O__cond z ->
  (seq_cond PH_InfoSCG__ext0O__list (PH_InfoSCG__ext0O__F1 z)).
intro H. unfold PH_InfoSCG__ext0O__cond in H. simpl. auto. Qed.
Lemma PH_InfoSCG__ext0O__F1F2_cond2 (z : PH_InfoSCG__ext0O__Type)
 : PH_InfoSCG__ext0O__F2 (PH_InfoSCG__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PH_InfoSCG__ext0O__F2F1_cond (y : seq_type PH_InfoSCG__ext0O__list)
  : seq_cond PH_InfoSCG__ext0O__list y ->
 (PH_InfoSCG__ext0O__cond (PH_InfoSCG__ext0O__F2 y)) /\  PH_InfoSCG__ext0O__F1 (PH_InfoSCG__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PH_InfoSCG__ext0O__cond. simpl in *. auto.
 - simpl. unfold PH_InfoSCG__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PH_InfoSCG__ext0O__Format : T_Format PH_InfoSCG__ext0O__Type PH_InfoSCG__ext0O__cond :=
        proj2_format  PH_InfoSCG__ext0O__cond PH_InfoSCG__ext0O__list__Format
    PH_InfoSCG__ext0O__F1 PH_InfoSCG__ext0O__F2 PH_InfoSCG__ext0O__F1F2_cond  PH_InfoSCG__ext0O__F1F2_cond2 PH_InfoSCG__ext0O__F2F1_cond.
Opaque PH_InfoSCG__ext0O__cond PH_InfoSCG__ext0O__Format.

Definition PH_InfoSCG__ext0__check_all_none (b : PH_InfoSCG__ext0O__Type) : bool :=
match b with 
  | make__PH_InfoSCG__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PH_InfoSCG__ext0__Format : T_Format PH_InfoSCG__ext0__Type PH_InfoSCG__ext0__cond :=
  restrict_add_format PH_InfoSCG__ext0__check_all_none PH_InfoSCG__ext0O__Format.

Opaque PH_InfoSCG__ext0__cond PH_InfoSCG__ext0__Format.


Definition PH_InfoSCG__root_Format_Type := Eval cbn in seq_format_prod PH_InfoSCG__root_list.
Definition PH_InfoSCG__root_Format_list : PH_InfoSCG__root_Format_Type :=
  (ServCellIndex__Format, (PH_UplinkCarrierSCG__Format, (PH_UplinkCarrierSCG__Format, unit_format))).

Definition PH_InfoSCG__ext_Format_Type := Eval cbn in get_formats PH_InfoSCG__ext_list.
Definition PH_InfoSCG__ext_Format_list : PH_InfoSCG__ext_Format_Type :=
  (PH_InfoSCG__ext0__Format, unit__Format).

Definition PH_InfoSCG__list_type : Set := (seq_type PH_InfoSCG__root_list) * (seq_ext_type PH_InfoSCG__ext_list).
Definition PH_InfoSCG__list_cond (z : PH_InfoSCG__list_type) : Prop :=
        (seq_cond PH_InfoSCG__root_list (fst z)) /\ (seq_ext_cond PH_InfoSCG__ext_list (snd z)).
Definition PH_InfoSCG__list_format : T_Format PH_InfoSCG__list_type PH_InfoSCG__list_cond :=
 (* Eval compute in *) seq_ext_format PH_InfoSCG__root_list PH_InfoSCG__root_Format_list PH_InfoSCG__ext_list PH_InfoSCG__ext_Format_list.

Opaque PH_InfoSCG__list_format.
Definition PH_InfoSCG__F1 (z : PH_InfoSCG__Type) : PH_InfoSCG__list_type :=
  (((PH_InfoSCG__servCellIndex z, (PH_InfoSCG__ph_Uplink z, (PH_InfoSCG__ph_SupplementaryUplink z, tt)))), (
(PH_InfoSCG__ext0 z, tt))).
Definition PH_InfoSCG__F2 (y : PH_InfoSCG__list_type) : PH_InfoSCG__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__PH_InfoSCG__Type j0 j1 j2 i0
  end.
Definition PH_InfoSCG__helper1 : (forall a : PH_InfoSCG__Type, PH_InfoSCG__cond a -> PH_InfoSCG__list_cond (PH_InfoSCG__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PH_InfoSCG__helper2 : (forall a : PH_InfoSCG__Type, PH_InfoSCG__F2 (PH_InfoSCG__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PH_InfoSCG__helper3 : (forall b : PH_InfoSCG__list_type, PH_InfoSCG__list_cond b -> PH_InfoSCG__cond (PH_InfoSCG__F2 b) /\ PH_InfoSCG__F1 (PH_InfoSCG__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PH_InfoSCG__cond, PH_InfoSCG__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PH_InfoSCG__Format : T_Format PH_InfoSCG__Type PH_InfoSCG__cond :=
 proj2_format PH_InfoSCG__cond PH_InfoSCG__list_format  PH_InfoSCG__F1 PH_InfoSCG__F2 PH_InfoSCG__helper1 PH_InfoSCG__helper2 PH_InfoSCG__helper3.

Opaque PH_InfoSCG__cond PH_InfoSCG__Format.

