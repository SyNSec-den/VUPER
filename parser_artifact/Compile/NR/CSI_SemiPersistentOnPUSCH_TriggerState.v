Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_ReportConfigId.

Opaque CSI_ReportConfigId__cond CSI_ReportConfigId__Format.

Inductive CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Type : Set :=
 | CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__enabled
.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__cond := (fun (_ : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Type) => True).
Lemma CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__nat__helper.

Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1 t :=
  match t with
  | CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__enabled => 0
  end.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F2 n :=
  match n with
  | 0 => CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__enabled
  | _ => CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__enabled
  end.
Lemma CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1F2 : forall x : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Type, (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1 x <= 0) /\ CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F2 (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F2F1 : forall (y : nat) (H : y <= 0), CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1 (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F2 y) = y. enum_solve H y. Qed.

Record CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type : Set :=
  make__CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type {
    CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17 : option CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Type ;
}.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list := (
 Opt CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Type CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__cond ::
 nil).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond z := 
  opt_cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__cond (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17 z) /\
  True.

Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Type := CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0__cond := CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond.

Record CSI_SemiPersistentOnPUSCH_TriggerState__Type : Set :=
  make__CSI_SemiPersistentOnPUSCH_TriggerState__Type {
    CSI_SemiPersistentOnPUSCH_TriggerState__associatedReportConfigInfo : CSI_ReportConfigId__Type ;
    CSI_SemiPersistentOnPUSCH_TriggerState__ext0 : option CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Type ;
}.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__root_list : list seq_elem := (
 Nor CSI_ReportConfigId__Type CSI_ReportConfigId__cond ::
 nil).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext_list : list typ := (
  typ_cons CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Type CSI_SemiPersistentOnPUSCH_TriggerState__ext0__cond ::
  nil).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__cond (z : CSI_SemiPersistentOnPUSCH_TriggerState__Type) := 
(  CSI_ReportConfigId__cond (CSI_SemiPersistentOnPUSCH_TriggerState__associatedReportConfigInfo z) /\
  True) /\ 
(  opt_cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0__cond (CSI_SemiPersistentOnPUSCH_TriggerState__ext0 z) /\
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
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Format : T_Format CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__nat__Format CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F2 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F1F2 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__F2F1.

Opaque CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Format.


Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format_list : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format_Type :=
  (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17__Format, unit_format).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list__Format := (*Eval compute in *) seq_format CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format_list.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1 z :=
  (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__sp_CSI_MultiplexingMode_r17 z, tt).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2 (y : seq_type CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type i0
  end.
Lemma CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1F2_cond (z : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type)
  : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond z ->
  (seq_cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1 z)).
intro H. unfold CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1F2_cond2 (z : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type)
 : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2 (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2F1_cond (y : seq_type CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list)
  : seq_cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list y ->
 (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2 y)) /\  CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1 (CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format : T_Format CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond :=
        proj2_format  CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__list__Format
    CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1F2_cond  CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F1F2_cond2 CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__F2F1_cond.
Opaque CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format.

Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0__check_all_none (b : CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type) : bool :=
match b with 
  | make__CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Format : T_Format CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Type CSI_SemiPersistentOnPUSCH_TriggerState__ext0__cond :=
  restrict_add_format CSI_SemiPersistentOnPUSCH_TriggerState__ext0__check_all_none CSI_SemiPersistentOnPUSCH_TriggerState__ext0O__Format.

Opaque CSI_SemiPersistentOnPUSCH_TriggerState__ext0__cond CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Format.


Definition CSI_SemiPersistentOnPUSCH_TriggerState__root_Format_Type := Eval cbn in seq_format_prod CSI_SemiPersistentOnPUSCH_TriggerState__root_list.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__root_Format_list : CSI_SemiPersistentOnPUSCH_TriggerState__root_Format_Type :=
  (CSI_ReportConfigId__Format, unit_format).

Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext_Format_Type := Eval cbn in get_formats CSI_SemiPersistentOnPUSCH_TriggerState__ext_list.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__ext_Format_list : CSI_SemiPersistentOnPUSCH_TriggerState__ext_Format_Type :=
  (CSI_SemiPersistentOnPUSCH_TriggerState__ext0__Format, unit__Format).

Definition CSI_SemiPersistentOnPUSCH_TriggerState__list_type : Set := (seq_type CSI_SemiPersistentOnPUSCH_TriggerState__root_list) * (seq_ext_type CSI_SemiPersistentOnPUSCH_TriggerState__ext_list).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__list_cond (z : CSI_SemiPersistentOnPUSCH_TriggerState__list_type) : Prop :=
        (seq_cond CSI_SemiPersistentOnPUSCH_TriggerState__root_list (fst z)) /\ (seq_ext_cond CSI_SemiPersistentOnPUSCH_TriggerState__ext_list (snd z)).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__list_format : T_Format CSI_SemiPersistentOnPUSCH_TriggerState__list_type CSI_SemiPersistentOnPUSCH_TriggerState__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_SemiPersistentOnPUSCH_TriggerState__root_list CSI_SemiPersistentOnPUSCH_TriggerState__root_Format_list CSI_SemiPersistentOnPUSCH_TriggerState__ext_list CSI_SemiPersistentOnPUSCH_TriggerState__ext_Format_list.

Opaque CSI_SemiPersistentOnPUSCH_TriggerState__list_format.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__F1 (z : CSI_SemiPersistentOnPUSCH_TriggerState__Type) : CSI_SemiPersistentOnPUSCH_TriggerState__list_type :=
  (((CSI_SemiPersistentOnPUSCH_TriggerState__associatedReportConfigInfo z, tt)), (
(CSI_SemiPersistentOnPUSCH_TriggerState__ext0 z, tt))).
Definition CSI_SemiPersistentOnPUSCH_TriggerState__F2 (y : CSI_SemiPersistentOnPUSCH_TriggerState__list_type) : CSI_SemiPersistentOnPUSCH_TriggerState__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__CSI_SemiPersistentOnPUSCH_TriggerState__Type j0 i0
  end.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__helper1 : (forall a : CSI_SemiPersistentOnPUSCH_TriggerState__Type, CSI_SemiPersistentOnPUSCH_TriggerState__cond a -> CSI_SemiPersistentOnPUSCH_TriggerState__list_cond (CSI_SemiPersistentOnPUSCH_TriggerState__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__helper2 : (forall a : CSI_SemiPersistentOnPUSCH_TriggerState__Type, CSI_SemiPersistentOnPUSCH_TriggerState__F2 (CSI_SemiPersistentOnPUSCH_TriggerState__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__helper3 : (forall b : CSI_SemiPersistentOnPUSCH_TriggerState__list_type, CSI_SemiPersistentOnPUSCH_TriggerState__list_cond b -> CSI_SemiPersistentOnPUSCH_TriggerState__cond (CSI_SemiPersistentOnPUSCH_TriggerState__F2 b) /\ CSI_SemiPersistentOnPUSCH_TriggerState__F1 (CSI_SemiPersistentOnPUSCH_TriggerState__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_SemiPersistentOnPUSCH_TriggerState__cond, CSI_SemiPersistentOnPUSCH_TriggerState__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_SemiPersistentOnPUSCH_TriggerState__Format : T_Format CSI_SemiPersistentOnPUSCH_TriggerState__Type CSI_SemiPersistentOnPUSCH_TriggerState__cond :=
 proj2_format CSI_SemiPersistentOnPUSCH_TriggerState__cond CSI_SemiPersistentOnPUSCH_TriggerState__list_format  CSI_SemiPersistentOnPUSCH_TriggerState__F1 CSI_SemiPersistentOnPUSCH_TriggerState__F2 CSI_SemiPersistentOnPUSCH_TriggerState__helper1 CSI_SemiPersistentOnPUSCH_TriggerState__helper2 CSI_SemiPersistentOnPUSCH_TriggerState__helper3.

Opaque CSI_SemiPersistentOnPUSCH_TriggerState__cond CSI_SemiPersistentOnPUSCH_TriggerState__Format.

