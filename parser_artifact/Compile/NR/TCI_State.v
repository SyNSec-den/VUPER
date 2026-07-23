Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Require Import NR.QCL_Info.

Opaque QCL_Info__cond QCL_Info__Format.

Require Import NR.QCL_Info.

Opaque QCL_Info__cond QCL_Info__Format.

Require Import NR.AdditionalPCIIndex_r17.

Opaque AdditionalPCIIndex_r17__cond AdditionalPCIIndex_r17__Format.

Require Import NR.PathlossReferenceRS_Id_r17.

Opaque PathlossReferenceRS_Id_r17__cond PathlossReferenceRS_Id_r17__Format.

Require Import NR.Uplink_powerControlId_r17.

Opaque Uplink_powerControlId_r17__cond Uplink_powerControlId_r17__Format.

Record TCI_State__ext0O__Type : Set :=
  make__TCI_State__ext0O__Type {
    TCI_State__ext0O__additionalPCI_r17 : option AdditionalPCIIndex_r17__Type ;
    TCI_State__ext0O__pathlossReferenceRS_Id_r17 : option PathlossReferenceRS_Id_r17__Type ;
    TCI_State__ext0O__ul_powerControl_r17 : option Uplink_powerControlId_r17__Type ;
}.
Definition TCI_State__ext0O__list := (
 Opt AdditionalPCIIndex_r17__Type AdditionalPCIIndex_r17__cond ::
 Opt PathlossReferenceRS_Id_r17__Type PathlossReferenceRS_Id_r17__cond ::
 Opt Uplink_powerControlId_r17__Type Uplink_powerControlId_r17__cond ::
 nil).
Definition TCI_State__ext0O__cond z := 
  opt_cond AdditionalPCIIndex_r17__cond (TCI_State__ext0O__additionalPCI_r17 z) /\
  opt_cond PathlossReferenceRS_Id_r17__cond (TCI_State__ext0O__pathlossReferenceRS_Id_r17 z) /\
  opt_cond Uplink_powerControlId_r17__cond (TCI_State__ext0O__ul_powerControl_r17 z) /\
  True.

Definition TCI_State__ext0__Type := TCI_State__ext0O__Type.
Definition TCI_State__ext0__cond := TCI_State__ext0O__cond.

Record TCI_State__Type : Set :=
  make__TCI_State__Type {
    TCI_State__tci_StateId : TCI_StateId__Type ;
    TCI_State__qcl_Type1 : QCL_Info__Type ;
    TCI_State__qcl_Type2 : option QCL_Info__Type ;
    TCI_State__ext0 : option TCI_State__ext0__Type ;
}.
Definition TCI_State__root_list : list seq_elem := (
 Nor TCI_StateId__Type TCI_StateId__cond ::
 Nor QCL_Info__Type QCL_Info__cond ::
 Opt QCL_Info__Type QCL_Info__cond ::
 nil).
Definition TCI_State__ext_list : list typ := (
  typ_cons TCI_State__ext0__Type TCI_State__ext0__cond ::
  nil).
Definition TCI_State__cond (z : TCI_State__Type) := 
(  TCI_StateId__cond (TCI_State__tci_StateId z) /\
  QCL_Info__cond (TCI_State__qcl_Type1 z) /\
  opt_cond QCL_Info__cond (TCI_State__qcl_Type2 z) /\
  True) /\ 
(  opt_cond TCI_State__ext0__cond (TCI_State__ext0 z) /\
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

Definition TCI_State__ext0O__Format_Type := Eval cbn in seq_format_prod TCI_State__ext0O__list.
Definition TCI_State__ext0O__Format_list : TCI_State__ext0O__Format_Type :=
  (AdditionalPCIIndex_r17__Format, (PathlossReferenceRS_Id_r17__Format, (Uplink_powerControlId_r17__Format, unit_format))).
Definition TCI_State__ext0O__list__Format := (*Eval compute in *) seq_format TCI_State__ext0O__list TCI_State__ext0O__Format_list.
Definition TCI_State__ext0O__F1 z :=
  (TCI_State__ext0O__additionalPCI_r17 z, (TCI_State__ext0O__pathlossReferenceRS_Id_r17 z, (TCI_State__ext0O__ul_powerControl_r17 z, tt))).
Definition TCI_State__ext0O__F2 (y : seq_type TCI_State__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__TCI_State__ext0O__Type i0 i1 i2
  end.
Lemma TCI_State__ext0O__F1F2_cond (z : TCI_State__ext0O__Type)
  : TCI_State__ext0O__cond z ->
  (seq_cond TCI_State__ext0O__list (TCI_State__ext0O__F1 z)).
intro H. unfold TCI_State__ext0O__cond in H. simpl. auto. Qed.
Lemma TCI_State__ext0O__F1F2_cond2 (z : TCI_State__ext0O__Type)
 : TCI_State__ext0O__F2 (TCI_State__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TCI_State__ext0O__F2F1_cond (y : seq_type TCI_State__ext0O__list)
  : seq_cond TCI_State__ext0O__list y ->
 (TCI_State__ext0O__cond (TCI_State__ext0O__F2 y)) /\  TCI_State__ext0O__F1 (TCI_State__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TCI_State__ext0O__cond. simpl in *. auto.
 - simpl. unfold TCI_State__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TCI_State__ext0O__Format : T_Format TCI_State__ext0O__Type TCI_State__ext0O__cond :=
        proj2_format  TCI_State__ext0O__cond TCI_State__ext0O__list__Format
    TCI_State__ext0O__F1 TCI_State__ext0O__F2 TCI_State__ext0O__F1F2_cond  TCI_State__ext0O__F1F2_cond2 TCI_State__ext0O__F2F1_cond.
Opaque TCI_State__ext0O__cond TCI_State__ext0O__Format.

Definition TCI_State__ext0__check_all_none (b : TCI_State__ext0O__Type) : bool :=
match b with 
  | make__TCI_State__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition TCI_State__ext0__Format : T_Format TCI_State__ext0__Type TCI_State__ext0__cond :=
  restrict_add_format TCI_State__ext0__check_all_none TCI_State__ext0O__Format.

Opaque TCI_State__ext0__cond TCI_State__ext0__Format.


Definition TCI_State__root_Format_Type := Eval cbn in seq_format_prod TCI_State__root_list.
Definition TCI_State__root_Format_list : TCI_State__root_Format_Type :=
  (TCI_StateId__Format, (QCL_Info__Format, (QCL_Info__Format, unit_format))).

Definition TCI_State__ext_Format_Type := Eval cbn in get_formats TCI_State__ext_list.
Definition TCI_State__ext_Format_list : TCI_State__ext_Format_Type :=
  (TCI_State__ext0__Format, unit__Format).

Definition TCI_State__list_type : Set := (seq_type TCI_State__root_list) * (seq_ext_type TCI_State__ext_list).
Definition TCI_State__list_cond (z : TCI_State__list_type) : Prop :=
        (seq_cond TCI_State__root_list (fst z)) /\ (seq_ext_cond TCI_State__ext_list (snd z)).
Definition TCI_State__list_format : T_Format TCI_State__list_type TCI_State__list_cond :=
 (* Eval compute in *) seq_ext_format TCI_State__root_list TCI_State__root_Format_list TCI_State__ext_list TCI_State__ext_Format_list.

Opaque TCI_State__list_format.
Definition TCI_State__F1 (z : TCI_State__Type) : TCI_State__list_type :=
  (((TCI_State__tci_StateId z, (TCI_State__qcl_Type1 z, (TCI_State__qcl_Type2 z, tt)))), (
(TCI_State__ext0 z, tt))).
Definition TCI_State__F2 (y : TCI_State__list_type) : TCI_State__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__TCI_State__Type j0 j1 j2 i0
  end.
Definition TCI_State__helper1 : (forall a : TCI_State__Type, TCI_State__cond a -> TCI_State__list_cond (TCI_State__F1 a)).
                     intros. destruct a. auto. Qed.
Definition TCI_State__helper2 : (forall a : TCI_State__Type, TCI_State__F2 (TCI_State__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition TCI_State__helper3 : (forall b : TCI_State__list_type, TCI_State__list_cond b -> TCI_State__cond (TCI_State__F2 b) /\ TCI_State__F1 (TCI_State__F2 b) = b).
                     intros. destruct b as [y y1]. unfold TCI_State__cond, TCI_State__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition TCI_State__Format : T_Format TCI_State__Type TCI_State__cond :=
 proj2_format TCI_State__cond TCI_State__list_format  TCI_State__F1 TCI_State__F2 TCI_State__helper1 TCI_State__helper2 TCI_State__helper3.

Opaque TCI_State__cond TCI_State__Format.

