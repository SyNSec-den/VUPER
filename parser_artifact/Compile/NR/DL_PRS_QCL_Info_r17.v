Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__Type := Z.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__cond := (fun z => (0 <= z <= 63)%Z).
Inductive DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Type : Set :=
 | DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC
 | DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeD
 | DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC_plus_typeD
.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__cond := (fun (_ : DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Type) => True).
Lemma DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__nat__helper.

Definition DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1 t :=
  match t with
  | DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC => 0
  | DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeD => 1
  | DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC_plus_typeD => 2
  end.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F2 n :=
  match n with
  | 0 => DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC
  | 1 => DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeD
  | 2 => DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC_plus_typeD
  | _ => DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__typeC
  end.
Lemma DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1F2 : forall x : DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Type, (DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1 x <= 2) /\ DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F2 (DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1 x) = x. imp_solve. Qed.
Lemma DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F2F1 : forall (y : nat) (H : y <= 2), DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1 (DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F2 y) = y. enum_solve H y. Qed.

Record DL_PRS_QCL_Info_r17__root__ssb_r17__Type : Set :=
  make__DL_PRS_QCL_Info_r17__root__ssb_r17__Type {
    DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17 : Z ;
    DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17 : DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Type ;
}.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__root_list : list seq_elem := (
 Nor Z DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__cond ::
 Nor DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Type DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__cond ::
 nil).
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__ext_list : list typ := (
  nil).
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__cond (z : DL_PRS_QCL_Info_r17__root__ssb_r17__Type) := 
(  DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__cond (DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17 z) /\
  DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__cond (DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17 z) /\
  True) /\ 
(  True).

Require Import NR.NR_DL_PRS_ResourceID_r17.

Opaque NR_DL_PRS_ResourceID_r17__cond NR_DL_PRS_ResourceID_r17__Format.

Record DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type : Set :=
  make__DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type {
    DL_PRS_QCL_Info_r17__root__dl_PRS_r17__qcl_DL_PRS_ResourceID_r17 : NR_DL_PRS_ResourceID_r17__Type ;
}.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_list : list seq_elem := (
 Nor NR_DL_PRS_ResourceID_r17__Type NR_DL_PRS_ResourceID_r17__cond ::
 nil).
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_list : list typ := (
  nil).
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond (z : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type) := 
(  NR_DL_PRS_ResourceID_r17__cond (DL_PRS_QCL_Info_r17__root__dl_PRS_r17__qcl_DL_PRS_ResourceID_r17 z) /\
  True) /\ 
(  True).


Inductive DL_PRS_QCL_Info_r17__root__Type : Set :=
  | DL_PRS_QCL_Info_r17__root__ssb_r17 : DL_PRS_QCL_Info_r17__root__ssb_r17__Type -> DL_PRS_QCL_Info_r17__root__Type
  | DL_PRS_QCL_Info_r17__root__dl_PRS_r17 : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type -> DL_PRS_QCL_Info_r17__root__Type
.
Definition DL_PRS_QCL_Info_r17__root__list : list typ := (
typ_cons DL_PRS_QCL_Info_r17__root__ssb_r17__Type DL_PRS_QCL_Info_r17__root__ssb_r17__cond ::
typ_cons DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond ::
 nil).
Definition DL_PRS_QCL_Info_r17__root__cond (c : DL_PRS_QCL_Info_r17__root__Type) := 
  match c with
  | DL_PRS_QCL_Info_r17__root__ssb_r17 t => DL_PRS_QCL_Info_r17__root__ssb_r17__cond t 
  | DL_PRS_QCL_Info_r17__root__dl_PRS_r17 t => DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond t 
  end.

Lemma DL_PRS_QCL_Info_r17__root__len_helper1 : to_bit_sz (length DL_PRS_QCL_Info_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_PRS_QCL_Info_r17__root__len_helper2 : 2 <= length2 DL_PRS_QCL_Info_r17__root__list.
 simpl. lia. Qed.

Definition DL_PRS_QCL_Info_r17__ext__Type : Set := Empty_set.
Definition DL_PRS_QCL_Info_r17__ext__cond (c : DL_PRS_QCL_Info_r17__ext__Type) := True.
Definition DL_PRS_QCL_Info_r17__Type : Set := DL_PRS_QCL_Info_r17__root__Type + DL_PRS_QCL_Info_r17__ext__Type.
Definition DL_PRS_QCL_Info_r17__cond :=
  sum_cond DL_PRS_QCL_Info_r17__root__cond DL_PRS_QCL_Info_r17__ext__cond.

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
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__Format : T_Format Z DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__cond :=
 ranged_int_format (0) (63) DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__helper1 DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__helper2.

Opaque DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__cond DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__Format.

Definition DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Format : T_Format DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__nat__Format DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1 DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F2 DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F1F2 DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__F2F1.

Opaque DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__cond DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Format.


Definition DL_PRS_QCL_Info_r17__root__ssb_r17__root_Format_Type := Eval cbn in seq_format_prod DL_PRS_QCL_Info_r17__root__ssb_r17__root_list.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__root_Format_list : DL_PRS_QCL_Info_r17__root__ssb_r17__root_Format_Type :=
  (DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17__Format, (DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17__Format, unit_format)).

Definition DL_PRS_QCL_Info_r17__root__ssb_r17__ext_Format_Type := Eval cbn in get_formats DL_PRS_QCL_Info_r17__root__ssb_r17__ext_list.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__ext_Format_list : DL_PRS_QCL_Info_r17__root__ssb_r17__ext_Format_Type :=
  unit__Format.

Definition DL_PRS_QCL_Info_r17__root__ssb_r17__list_type : Set := (seq_type DL_PRS_QCL_Info_r17__root__ssb_r17__root_list) * (seq_ext_type DL_PRS_QCL_Info_r17__root__ssb_r17__ext_list).
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__list_cond (z : DL_PRS_QCL_Info_r17__root__ssb_r17__list_type) : Prop :=
        (seq_cond DL_PRS_QCL_Info_r17__root__ssb_r17__root_list (fst z)) /\ (seq_ext_cond DL_PRS_QCL_Info_r17__root__ssb_r17__ext_list (snd z)).
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__list_format : T_Format DL_PRS_QCL_Info_r17__root__ssb_r17__list_type DL_PRS_QCL_Info_r17__root__ssb_r17__list_cond :=
 (* Eval compute in *) seq_ext_format DL_PRS_QCL_Info_r17__root__ssb_r17__root_list DL_PRS_QCL_Info_r17__root__ssb_r17__root_Format_list DL_PRS_QCL_Info_r17__root__ssb_r17__ext_list DL_PRS_QCL_Info_r17__root__ssb_r17__ext_Format_list.

Opaque DL_PRS_QCL_Info_r17__root__ssb_r17__list_format.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__F1 (z : DL_PRS_QCL_Info_r17__root__ssb_r17__Type) : DL_PRS_QCL_Info_r17__root__ssb_r17__list_type :=
  (((DL_PRS_QCL_Info_r17__root__ssb_r17__ssb_Index_r17 z, (DL_PRS_QCL_Info_r17__root__ssb_r17__rs_Type_r17 z, tt))), (
tt)).
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__F2 (y : DL_PRS_QCL_Info_r17__root__ssb_r17__list_type) : DL_PRS_QCL_Info_r17__root__ssb_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__DL_PRS_QCL_Info_r17__root__ssb_r17__Type j0 j1
  end.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__helper1 : (forall a : DL_PRS_QCL_Info_r17__root__ssb_r17__Type, DL_PRS_QCL_Info_r17__root__ssb_r17__cond a -> DL_PRS_QCL_Info_r17__root__ssb_r17__list_cond (DL_PRS_QCL_Info_r17__root__ssb_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__helper2 : (forall a : DL_PRS_QCL_Info_r17__root__ssb_r17__Type, DL_PRS_QCL_Info_r17__root__ssb_r17__F2 (DL_PRS_QCL_Info_r17__root__ssb_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__helper3 : (forall b : DL_PRS_QCL_Info_r17__root__ssb_r17__list_type, DL_PRS_QCL_Info_r17__root__ssb_r17__list_cond b -> DL_PRS_QCL_Info_r17__root__ssb_r17__cond (DL_PRS_QCL_Info_r17__root__ssb_r17__F2 b) /\ DL_PRS_QCL_Info_r17__root__ssb_r17__F1 (DL_PRS_QCL_Info_r17__root__ssb_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DL_PRS_QCL_Info_r17__root__ssb_r17__cond, DL_PRS_QCL_Info_r17__root__ssb_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DL_PRS_QCL_Info_r17__root__ssb_r17__Format : T_Format DL_PRS_QCL_Info_r17__root__ssb_r17__Type DL_PRS_QCL_Info_r17__root__ssb_r17__cond :=
 proj2_format DL_PRS_QCL_Info_r17__root__ssb_r17__cond DL_PRS_QCL_Info_r17__root__ssb_r17__list_format  DL_PRS_QCL_Info_r17__root__ssb_r17__F1 DL_PRS_QCL_Info_r17__root__ssb_r17__F2 DL_PRS_QCL_Info_r17__root__ssb_r17__helper1 DL_PRS_QCL_Info_r17__root__ssb_r17__helper2 DL_PRS_QCL_Info_r17__root__ssb_r17__helper3.

Opaque DL_PRS_QCL_Info_r17__root__ssb_r17__cond DL_PRS_QCL_Info_r17__root__ssb_r17__Format.


Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_Format_Type := Eval cbn in seq_format_prod DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_list.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_Format_list : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_Format_Type :=
  (NR_DL_PRS_ResourceID_r17__Format, unit_format).

Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_Format_Type := Eval cbn in get_formats DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_list.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_Format_list : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_Format_Type :=
  unit__Format.

Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_type : Set := (seq_type DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_list) * (seq_ext_type DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_list).
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_cond (z : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_type) : Prop :=
        (seq_cond DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_list (fst z)) /\ (seq_ext_cond DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_list (snd z)).
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_format : T_Format DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_type DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_cond :=
 (* Eval compute in *) seq_ext_format DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_list DL_PRS_QCL_Info_r17__root__dl_PRS_r17__root_Format_list DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_list DL_PRS_QCL_Info_r17__root__dl_PRS_r17__ext_Format_list.

Opaque DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_format.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F1 (z : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type) : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_type :=
  (((DL_PRS_QCL_Info_r17__root__dl_PRS_r17__qcl_DL_PRS_ResourceID_r17 z, tt)), (
tt)).
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F2 (y : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_type) : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type j0
  end.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__helper1 : (forall a : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type, DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond a -> DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_cond (DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__helper2 : (forall a : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type, DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F2 (DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__helper3 : (forall b : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_type, DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_cond b -> DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond (DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F2 b) /\ DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F1 (DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond, DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Format : T_Format DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond :=
 proj2_format DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond DL_PRS_QCL_Info_r17__root__dl_PRS_r17__list_format  DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F1 DL_PRS_QCL_Info_r17__root__dl_PRS_r17__F2 DL_PRS_QCL_Info_r17__root__dl_PRS_r17__helper1 DL_PRS_QCL_Info_r17__root__dl_PRS_r17__helper2 DL_PRS_QCL_Info_r17__root__dl_PRS_r17__helper3.

Opaque DL_PRS_QCL_Info_r17__root__dl_PRS_r17__cond DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Format.


Definition DL_PRS_QCL_Info_r17__root__Format_Type := Eval cbn in get_formats DL_PRS_QCL_Info_r17__root__list.
Definition DL_PRS_QCL_Info_r17__root__Format_list : DL_PRS_QCL_Info_r17__root__Format_Type :=
  (DL_PRS_QCL_Info_r17__root__ssb_r17__Format, (DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Format, unit__Format)).
Definition DL_PRS_QCL_Info_r17__root__list__Format := Eval compute in choice_format DL_PRS_QCL_Info_r17__root__list DL_PRS_QCL_Info_r17__root__len_helper1 DL_PRS_QCL_Info_r17__root__len_helper2  DL_PRS_QCL_Info_r17__root__Format_list.
Definition DL_PRS_QCL_Info_r17__root__F1 (z : DL_PRS_QCL_Info_r17__root__Type) : (choice DL_PRS_QCL_Info_r17__root__list) :=
  match z with
   | DL_PRS_QCL_Info_r17__root__ssb_r17 t => existT _ 0 t
  | DL_PRS_QCL_Info_r17__root__dl_PRS_r17 t => existT _ 1 t
  end.
Definition DL_PRS_QCL_Info_r17__root__g := (fun n => typ_set (get_nth_typ DL_PRS_QCL_Info_r17__root__list n)).
Definition DL_PRS_QCL_Info_r17__root__F2 (y : choice DL_PRS_QCL_Info_r17__root__list) : DL_PRS_QCL_Info_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_PRS_QCL_Info_r17__root__g n -> DL_PRS_QCL_Info_r17__root__Type) with
    | 0 => fun (t : DL_PRS_QCL_Info_r17__root__ssb_r17__Type) => DL_PRS_QCL_Info_r17__root__ssb_r17 t 
    | 1 => fun (t : DL_PRS_QCL_Info_r17__root__dl_PRS_r17__Type) => DL_PRS_QCL_Info_r17__root__dl_PRS_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DL_PRS_QCL_Info_r17__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DL_PRS_QCL_Info_r17__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_PRS_QCL_Info_r17__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DL_PRS_QCL_Info_r17__root__Type with end) n0
           end t0).

Lemma DL_PRS_QCL_Info_r17__root__helper2 :  forall (y : DL_PRS_QCL_Info_r17__root__Type), DL_PRS_QCL_Info_r17__root__cond y -> choice_cond DL_PRS_QCL_Info_r17__root__list (DL_PRS_QCL_Info_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_PRS_QCL_Info_r17__root__helper3 :  forall (y : DL_PRS_QCL_Info_r17__root__Type), DL_PRS_QCL_Info_r17__root__F2 (DL_PRS_QCL_Info_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_PRS_QCL_Info_r17__root__helper4 : (forall b : choice DL_PRS_QCL_Info_r17__root__list, choice_cond DL_PRS_QCL_Info_r17__root__list b -> DL_PRS_QCL_Info_r17__root__cond (DL_PRS_QCL_Info_r17__root__F2 b) /\ DL_PRS_QCL_Info_r17__root__F1 (DL_PRS_QCL_Info_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_PRS_QCL_Info_r17__root__F1 DL_PRS_QCL_Info_r17__root__F2.
Definition DL_PRS_QCL_Info_r17__root__Format : T_Format DL_PRS_QCL_Info_r17__root__Type DL_PRS_QCL_Info_r17__root__cond :=
  (* Eval compute in *) proj2_format DL_PRS_QCL_Info_r17__root__cond DL_PRS_QCL_Info_r17__root__list__Format DL_PRS_QCL_Info_r17__root__F1 DL_PRS_QCL_Info_r17__root__F2 DL_PRS_QCL_Info_r17__root__helper2 DL_PRS_QCL_Info_r17__root__helper3 DL_PRS_QCL_Info_r17__root__helper4.
Opaque DL_PRS_QCL_Info_r17__root__cond DL_PRS_QCL_Info_r17__root__Format.

Definition DL_PRS_QCL_Info_r17__ext__Format : T_Format DL_PRS_QCL_Info_r17__ext__Type DL_PRS_QCL_Info_r17__ext__cond := empty_format.
Opaque DL_PRS_QCL_Info_r17__ext__cond DL_PRS_QCL_Info_r17__ext__Format.

Definition DL_PRS_QCL_Info_r17__Format : T_Format DL_PRS_QCL_Info_r17__Type DL_PRS_QCL_Info_r17__cond := sum_format DL_PRS_QCL_Info_r17__root__Format DL_PRS_QCL_Info_r17__ext__Format.
Opaque DL_PRS_QCL_Info_r17__cond DL_PRS_QCL_Info_r17__Format.

