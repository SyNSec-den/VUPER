Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.


Inductive QCL_Info__referenceSignal__Type : Set :=
  | QCL_Info__referenceSignal__csi_rs : NZP_CSI_RS_ResourceId__Type -> QCL_Info__referenceSignal__Type
  | QCL_Info__referenceSignal__ssb : SSB_Index__Type -> QCL_Info__referenceSignal__Type
.
Definition QCL_Info__referenceSignal__list : list typ := (
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
typ_cons SSB_Index__Type SSB_Index__cond ::
 nil).
Definition QCL_Info__referenceSignal__cond (c : QCL_Info__referenceSignal__Type) := 
  match c with
  | QCL_Info__referenceSignal__csi_rs t => NZP_CSI_RS_ResourceId__cond t 
  | QCL_Info__referenceSignal__ssb t => SSB_Index__cond t 
  end.

Lemma QCL_Info__referenceSignal__len_helper1 : to_bit_sz (length QCL_Info__referenceSignal__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma QCL_Info__referenceSignal__len_helper2 : 2 <= length2 QCL_Info__referenceSignal__list.
 simpl. lia. Qed.
Inductive QCL_Info__qcl_Type__Type : Set :=
 | QCL_Info__qcl_Type__typeA
 | QCL_Info__qcl_Type__typeB
 | QCL_Info__qcl_Type__typeC
 | QCL_Info__qcl_Type__typeD
.
Definition QCL_Info__qcl_Type__cond := (fun (_ : QCL_Info__qcl_Type__Type) => True).
Lemma QCL_Info__qcl_Type__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition QCL_Info__qcl_Type__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 QCL_Info__qcl_Type__nat__helper.

Definition QCL_Info__qcl_Type__F1 t :=
  match t with
  | QCL_Info__qcl_Type__typeA => 0
  | QCL_Info__qcl_Type__typeB => 1
  | QCL_Info__qcl_Type__typeC => 2
  | QCL_Info__qcl_Type__typeD => 3
  end.
Definition QCL_Info__qcl_Type__F2 n :=
  match n with
  | 0 => QCL_Info__qcl_Type__typeA
  | 1 => QCL_Info__qcl_Type__typeB
  | 2 => QCL_Info__qcl_Type__typeC
  | 3 => QCL_Info__qcl_Type__typeD
  | _ => QCL_Info__qcl_Type__typeA
  end.
Lemma QCL_Info__qcl_Type__F1F2 : forall x : QCL_Info__qcl_Type__Type, (QCL_Info__qcl_Type__F1 x <= 3) /\ QCL_Info__qcl_Type__F2 (QCL_Info__qcl_Type__F1 x) = x. imp_solve. Qed.
Lemma QCL_Info__qcl_Type__F2F1 : forall (y : nat) (H : y <= 3), QCL_Info__qcl_Type__F1 (QCL_Info__qcl_Type__F2 y) = y. enum_solve H y. Qed.

Record QCL_Info__Type : Set :=
  make__QCL_Info__Type {
    QCL_Info__cell : option ServCellIndex__Type ;
    QCL_Info__bwp_Id : option BWP_Id__Type ;
    QCL_Info__referenceSignal : QCL_Info__referenceSignal__Type ;
    QCL_Info__qcl_Type : QCL_Info__qcl_Type__Type ;
}.
Definition QCL_Info__root_list : list seq_elem := (
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Opt BWP_Id__Type BWP_Id__cond ::
 Nor QCL_Info__referenceSignal__Type QCL_Info__referenceSignal__cond ::
 Nor QCL_Info__qcl_Type__Type QCL_Info__qcl_Type__cond ::
 nil).
Definition QCL_Info__ext_list : list typ := (
  nil).
Definition QCL_Info__cond (z : QCL_Info__Type) := 
(  opt_cond ServCellIndex__cond (QCL_Info__cell z) /\
  opt_cond BWP_Id__cond (QCL_Info__bwp_Id z) /\
  QCL_Info__referenceSignal__cond (QCL_Info__referenceSignal z) /\
  QCL_Info__qcl_Type__cond (QCL_Info__qcl_Type z) /\
  True) /\ 
(  True).


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

Definition QCL_Info__referenceSignal__Format_Type := Eval cbn in get_formats QCL_Info__referenceSignal__list.
Definition QCL_Info__referenceSignal__Format_list : QCL_Info__referenceSignal__Format_Type :=
  (NZP_CSI_RS_ResourceId__Format, (SSB_Index__Format, unit__Format)).
Definition QCL_Info__referenceSignal__list__Format := Eval compute in choice_format QCL_Info__referenceSignal__list QCL_Info__referenceSignal__len_helper1 QCL_Info__referenceSignal__len_helper2  QCL_Info__referenceSignal__Format_list.
Definition QCL_Info__referenceSignal__F1 (z : QCL_Info__referenceSignal__Type) : (choice QCL_Info__referenceSignal__list) :=
  match z with
   | QCL_Info__referenceSignal__csi_rs t => existT _ 0 t
  | QCL_Info__referenceSignal__ssb t => existT _ 1 t
  end.
Definition QCL_Info__referenceSignal__g := (fun n => typ_set (get_nth_typ QCL_Info__referenceSignal__list n)).
Definition QCL_Info__referenceSignal__F2 (y : choice QCL_Info__referenceSignal__list) : QCL_Info__referenceSignal__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (QCL_Info__referenceSignal__g n -> QCL_Info__referenceSignal__Type) with
    | 0 => fun (t : NZP_CSI_RS_ResourceId__Type) => QCL_Info__referenceSignal__csi_rs t 
    | 1 => fun (t : SSB_Index__Type) => QCL_Info__referenceSignal__ssb t 
 | (S (S n0)) => (fun (x' : nat) (t'' : QCL_Info__referenceSignal__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ QCL_Info__referenceSignal__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len QCL_Info__referenceSignal__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return QCL_Info__referenceSignal__Type with end) n0
           end t0).

Lemma QCL_Info__referenceSignal__helper2 :  forall (y : QCL_Info__referenceSignal__Type), QCL_Info__referenceSignal__cond y -> choice_cond QCL_Info__referenceSignal__list (QCL_Info__referenceSignal__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma QCL_Info__referenceSignal__helper3 :  forall (y : QCL_Info__referenceSignal__Type), QCL_Info__referenceSignal__F2 (QCL_Info__referenceSignal__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma QCL_Info__referenceSignal__helper4 : (forall b : choice QCL_Info__referenceSignal__list, choice_cond QCL_Info__referenceSignal__list b -> QCL_Info__referenceSignal__cond (QCL_Info__referenceSignal__F2 b) /\ QCL_Info__referenceSignal__F1 (QCL_Info__referenceSignal__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length QCL_Info__referenceSignal__F1 QCL_Info__referenceSignal__F2.
Definition QCL_Info__referenceSignal__Format : T_Format QCL_Info__referenceSignal__Type QCL_Info__referenceSignal__cond :=
  (* Eval compute in *) proj2_format QCL_Info__referenceSignal__cond QCL_Info__referenceSignal__list__Format QCL_Info__referenceSignal__F1 QCL_Info__referenceSignal__F2 QCL_Info__referenceSignal__helper2 QCL_Info__referenceSignal__helper3 QCL_Info__referenceSignal__helper4.
Opaque QCL_Info__referenceSignal__cond QCL_Info__referenceSignal__Format.

Definition QCL_Info__qcl_Type__Format : T_Format QCL_Info__qcl_Type__Type (fun _ => True) :=
(* Eval compute in *) proj3_format QCL_Info__qcl_Type__nat__Format QCL_Info__qcl_Type__F1 QCL_Info__qcl_Type__F2 QCL_Info__qcl_Type__F1F2 QCL_Info__qcl_Type__F2F1.

Opaque QCL_Info__qcl_Type__cond QCL_Info__qcl_Type__Format.


Definition QCL_Info__root_Format_Type := Eval cbn in seq_format_prod QCL_Info__root_list.
Definition QCL_Info__root_Format_list : QCL_Info__root_Format_Type :=
  (ServCellIndex__Format, (BWP_Id__Format, (QCL_Info__referenceSignal__Format, (QCL_Info__qcl_Type__Format, unit_format)))).

Definition QCL_Info__ext_Format_Type := Eval cbn in get_formats QCL_Info__ext_list.
Definition QCL_Info__ext_Format_list : QCL_Info__ext_Format_Type :=
  unit__Format.

Definition QCL_Info__list_type : Set := (seq_type QCL_Info__root_list) * (seq_ext_type QCL_Info__ext_list).
Definition QCL_Info__list_cond (z : QCL_Info__list_type) : Prop :=
        (seq_cond QCL_Info__root_list (fst z)) /\ (seq_ext_cond QCL_Info__ext_list (snd z)).
Definition QCL_Info__list_format : T_Format QCL_Info__list_type QCL_Info__list_cond :=
 (* Eval compute in *) seq_ext_format QCL_Info__root_list QCL_Info__root_Format_list QCL_Info__ext_list QCL_Info__ext_Format_list.

Opaque QCL_Info__list_format.
Definition QCL_Info__F1 (z : QCL_Info__Type) : QCL_Info__list_type :=
  (((QCL_Info__cell z, (QCL_Info__bwp_Id z, (QCL_Info__referenceSignal z, (QCL_Info__qcl_Type z, tt))))), (
tt)).
Definition QCL_Info__F2 (y : QCL_Info__list_type) : QCL_Info__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__QCL_Info__Type j0 j1 j2 j3
  end.
Definition QCL_Info__helper1 : (forall a : QCL_Info__Type, QCL_Info__cond a -> QCL_Info__list_cond (QCL_Info__F1 a)).
                     intros. destruct a. auto. Qed.
Definition QCL_Info__helper2 : (forall a : QCL_Info__Type, QCL_Info__F2 (QCL_Info__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition QCL_Info__helper3 : (forall b : QCL_Info__list_type, QCL_Info__list_cond b -> QCL_Info__cond (QCL_Info__F2 b) /\ QCL_Info__F1 (QCL_Info__F2 b) = b).
                     intros. destruct b as [y y1]. unfold QCL_Info__cond, QCL_Info__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition QCL_Info__Format : T_Format QCL_Info__Type QCL_Info__cond :=
 proj2_format QCL_Info__cond QCL_Info__list_format  QCL_Info__F1 QCL_Info__F2 QCL_Info__helper1 QCL_Info__helper2 QCL_Info__helper3.

Opaque QCL_Info__cond QCL_Info__Format.

