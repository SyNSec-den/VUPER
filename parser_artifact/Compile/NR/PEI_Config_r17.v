Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PEI_Config_r17__po_NumPerPEI_r17__Type : Set :=
 | PEI_Config_r17__po_NumPerPEI_r17__po1
 | PEI_Config_r17__po_NumPerPEI_r17__po2
 | PEI_Config_r17__po_NumPerPEI_r17__po4
 | PEI_Config_r17__po_NumPerPEI_r17__po8
.
Definition PEI_Config_r17__po_NumPerPEI_r17__cond := (fun (_ : PEI_Config_r17__po_NumPerPEI_r17__Type) => True).
Lemma PEI_Config_r17__po_NumPerPEI_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PEI_Config_r17__po_NumPerPEI_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PEI_Config_r17__po_NumPerPEI_r17__nat__helper.

Definition PEI_Config_r17__po_NumPerPEI_r17__F1 t :=
  match t with
  | PEI_Config_r17__po_NumPerPEI_r17__po1 => 0
  | PEI_Config_r17__po_NumPerPEI_r17__po2 => 1
  | PEI_Config_r17__po_NumPerPEI_r17__po4 => 2
  | PEI_Config_r17__po_NumPerPEI_r17__po8 => 3
  end.
Definition PEI_Config_r17__po_NumPerPEI_r17__F2 n :=
  match n with
  | 0 => PEI_Config_r17__po_NumPerPEI_r17__po1
  | 1 => PEI_Config_r17__po_NumPerPEI_r17__po2
  | 2 => PEI_Config_r17__po_NumPerPEI_r17__po4
  | 3 => PEI_Config_r17__po_NumPerPEI_r17__po8
  | _ => PEI_Config_r17__po_NumPerPEI_r17__po1
  end.
Lemma PEI_Config_r17__po_NumPerPEI_r17__F1F2 : forall x : PEI_Config_r17__po_NumPerPEI_r17__Type, (PEI_Config_r17__po_NumPerPEI_r17__F1 x <= 3) /\ PEI_Config_r17__po_NumPerPEI_r17__F2 (PEI_Config_r17__po_NumPerPEI_r17__F1 x) = x. imp_solve. Qed.
Lemma PEI_Config_r17__po_NumPerPEI_r17__F2F1 : forall (y : nat) (H : y <= 3), PEI_Config_r17__po_NumPerPEI_r17__F1 (PEI_Config_r17__po_NumPerPEI_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PEI_Config_r17__payloadSizeDCI_2_7_r17__helper1 : (1 <= maxDCI_2_7_Size_r17)%Z. unfold maxDCI_2_7_Size_r17.
 lia. Qed.
Lemma PEI_Config_r17__payloadSizeDCI_2_7_r17__helper2 : to_bit_sz (Z.to_nat (maxDCI_2_7_Size_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDCI_2_7_Size_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PEI_Config_r17__payloadSizeDCI_2_7_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PEI_Config_r17__payloadSizeDCI_2_7_r17__Type := Z.
Definition PEI_Config_r17__payloadSizeDCI_2_7_r17__cond := (fun z => (1 <= z <= maxDCI_2_7_Size_r17)%Z).
Lemma PEI_Config_r17__pei_FrameOffset_r17__helper1 : (0 <= 16)%Z.  lia. Qed.
Lemma PEI_Config_r17__pei_FrameOffset_r17__helper2 : to_bit_sz (Z.to_nat (16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PEI_Config_r17__pei_FrameOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PEI_Config_r17__pei_FrameOffset_r17__Type := Z.
Definition PEI_Config_r17__pei_FrameOffset_r17__cond := (fun z => (0 <= z <= 16)%Z).
Require Import NR.SubgroupConfig_r17.

Opaque SubgroupConfig_r17__cond SubgroupConfig_r17__Format.

Inductive PEI_Config_r17__lastUsedCellOnly_r17__Type : Set :=
 | PEI_Config_r17__lastUsedCellOnly_r17__true
.
Definition PEI_Config_r17__lastUsedCellOnly_r17__cond := (fun (_ : PEI_Config_r17__lastUsedCellOnly_r17__Type) => True).
Lemma PEI_Config_r17__lastUsedCellOnly_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PEI_Config_r17__lastUsedCellOnly_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PEI_Config_r17__lastUsedCellOnly_r17__nat__helper.

Definition PEI_Config_r17__lastUsedCellOnly_r17__F1 t :=
  match t with
  | PEI_Config_r17__lastUsedCellOnly_r17__true => 0
  end.
Definition PEI_Config_r17__lastUsedCellOnly_r17__F2 n :=
  match n with
  | 0 => PEI_Config_r17__lastUsedCellOnly_r17__true
  | _ => PEI_Config_r17__lastUsedCellOnly_r17__true
  end.
Lemma PEI_Config_r17__lastUsedCellOnly_r17__F1F2 : forall x : PEI_Config_r17__lastUsedCellOnly_r17__Type, (PEI_Config_r17__lastUsedCellOnly_r17__F1 x <= 0) /\ PEI_Config_r17__lastUsedCellOnly_r17__F2 (PEI_Config_r17__lastUsedCellOnly_r17__F1 x) = x. imp_solve. Qed.
Lemma PEI_Config_r17__lastUsedCellOnly_r17__F2F1 : forall (y : nat) (H : y <= 0), PEI_Config_r17__lastUsedCellOnly_r17__F1 (PEI_Config_r17__lastUsedCellOnly_r17__F2 y) = y. enum_solve H y. Qed.

Record PEI_Config_r17__Type : Set :=
  make__PEI_Config_r17__Type {
    PEI_Config_r17__po_NumPerPEI_r17 : PEI_Config_r17__po_NumPerPEI_r17__Type ;
    PEI_Config_r17__payloadSizeDCI_2_7_r17 : Z ;
    PEI_Config_r17__pei_FrameOffset_r17 : Z ;
    PEI_Config_r17__subgroupConfig_r17 : SubgroupConfig_r17__Type ;
    PEI_Config_r17__lastUsedCellOnly_r17 : option PEI_Config_r17__lastUsedCellOnly_r17__Type ;
}.
Definition PEI_Config_r17__root_list : list seq_elem := (
 Nor PEI_Config_r17__po_NumPerPEI_r17__Type PEI_Config_r17__po_NumPerPEI_r17__cond ::
 Nor Z PEI_Config_r17__payloadSizeDCI_2_7_r17__cond ::
 Nor Z PEI_Config_r17__pei_FrameOffset_r17__cond ::
 Nor SubgroupConfig_r17__Type SubgroupConfig_r17__cond ::
 Opt PEI_Config_r17__lastUsedCellOnly_r17__Type PEI_Config_r17__lastUsedCellOnly_r17__cond ::
 nil).
Definition PEI_Config_r17__ext_list : list typ := (
  nil).
Definition PEI_Config_r17__cond (z : PEI_Config_r17__Type) := 
(  PEI_Config_r17__po_NumPerPEI_r17__cond (PEI_Config_r17__po_NumPerPEI_r17 z) /\
  PEI_Config_r17__payloadSizeDCI_2_7_r17__cond (PEI_Config_r17__payloadSizeDCI_2_7_r17 z) /\
  PEI_Config_r17__pei_FrameOffset_r17__cond (PEI_Config_r17__pei_FrameOffset_r17 z) /\
  SubgroupConfig_r17__cond (PEI_Config_r17__subgroupConfig_r17 z) /\
  opt_cond PEI_Config_r17__lastUsedCellOnly_r17__cond (PEI_Config_r17__lastUsedCellOnly_r17 z) /\
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
Definition PEI_Config_r17__po_NumPerPEI_r17__Format : T_Format PEI_Config_r17__po_NumPerPEI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PEI_Config_r17__po_NumPerPEI_r17__nat__Format PEI_Config_r17__po_NumPerPEI_r17__F1 PEI_Config_r17__po_NumPerPEI_r17__F2 PEI_Config_r17__po_NumPerPEI_r17__F1F2 PEI_Config_r17__po_NumPerPEI_r17__F2F1.

Opaque PEI_Config_r17__po_NumPerPEI_r17__cond PEI_Config_r17__po_NumPerPEI_r17__Format.

Definition PEI_Config_r17__payloadSizeDCI_2_7_r17__Format : T_Format Z PEI_Config_r17__payloadSizeDCI_2_7_r17__cond :=
 ranged_int_format (1) (maxDCI_2_7_Size_r17) PEI_Config_r17__payloadSizeDCI_2_7_r17__helper1 PEI_Config_r17__payloadSizeDCI_2_7_r17__helper2.

Opaque PEI_Config_r17__payloadSizeDCI_2_7_r17__cond PEI_Config_r17__payloadSizeDCI_2_7_r17__Format.

Definition PEI_Config_r17__pei_FrameOffset_r17__Format : T_Format Z PEI_Config_r17__pei_FrameOffset_r17__cond :=
 ranged_int_format (0) (16) PEI_Config_r17__pei_FrameOffset_r17__helper1 PEI_Config_r17__pei_FrameOffset_r17__helper2.

Opaque PEI_Config_r17__pei_FrameOffset_r17__cond PEI_Config_r17__pei_FrameOffset_r17__Format.

Definition PEI_Config_r17__lastUsedCellOnly_r17__Format : T_Format PEI_Config_r17__lastUsedCellOnly_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PEI_Config_r17__lastUsedCellOnly_r17__nat__Format PEI_Config_r17__lastUsedCellOnly_r17__F1 PEI_Config_r17__lastUsedCellOnly_r17__F2 PEI_Config_r17__lastUsedCellOnly_r17__F1F2 PEI_Config_r17__lastUsedCellOnly_r17__F2F1.

Opaque PEI_Config_r17__lastUsedCellOnly_r17__cond PEI_Config_r17__lastUsedCellOnly_r17__Format.


Definition PEI_Config_r17__root_Format_Type := Eval cbn in seq_format_prod PEI_Config_r17__root_list.
Definition PEI_Config_r17__root_Format_list : PEI_Config_r17__root_Format_Type :=
  (PEI_Config_r17__po_NumPerPEI_r17__Format, (PEI_Config_r17__payloadSizeDCI_2_7_r17__Format, (PEI_Config_r17__pei_FrameOffset_r17__Format, (SubgroupConfig_r17__Format, (PEI_Config_r17__lastUsedCellOnly_r17__Format, unit_format))))).

Definition PEI_Config_r17__ext_Format_Type := Eval cbn in get_formats PEI_Config_r17__ext_list.
Definition PEI_Config_r17__ext_Format_list : PEI_Config_r17__ext_Format_Type :=
  unit__Format.

Definition PEI_Config_r17__list_type : Set := (seq_type PEI_Config_r17__root_list) * (seq_ext_type PEI_Config_r17__ext_list).
Definition PEI_Config_r17__list_cond (z : PEI_Config_r17__list_type) : Prop :=
        (seq_cond PEI_Config_r17__root_list (fst z)) /\ (seq_ext_cond PEI_Config_r17__ext_list (snd z)).
Definition PEI_Config_r17__list_format : T_Format PEI_Config_r17__list_type PEI_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format PEI_Config_r17__root_list PEI_Config_r17__root_Format_list PEI_Config_r17__ext_list PEI_Config_r17__ext_Format_list.

Opaque PEI_Config_r17__list_format.
Definition PEI_Config_r17__F1 (z : PEI_Config_r17__Type) : PEI_Config_r17__list_type :=
  (((PEI_Config_r17__po_NumPerPEI_r17 z, (PEI_Config_r17__payloadSizeDCI_2_7_r17 z, (PEI_Config_r17__pei_FrameOffset_r17 z, (PEI_Config_r17__subgroupConfig_r17 z, (PEI_Config_r17__lastUsedCellOnly_r17 z, tt)))))), (
tt)).
Definition PEI_Config_r17__F2 (y : PEI_Config_r17__list_type) : PEI_Config_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__PEI_Config_r17__Type j0 j1 j2 j3 j4
  end.
Definition PEI_Config_r17__helper1 : (forall a : PEI_Config_r17__Type, PEI_Config_r17__cond a -> PEI_Config_r17__list_cond (PEI_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PEI_Config_r17__helper2 : (forall a : PEI_Config_r17__Type, PEI_Config_r17__F2 (PEI_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PEI_Config_r17__helper3 : (forall b : PEI_Config_r17__list_type, PEI_Config_r17__list_cond b -> PEI_Config_r17__cond (PEI_Config_r17__F2 b) /\ PEI_Config_r17__F1 (PEI_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PEI_Config_r17__cond, PEI_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PEI_Config_r17__Format : T_Format PEI_Config_r17__Type PEI_Config_r17__cond :=
 proj2_format PEI_Config_r17__cond PEI_Config_r17__list_format  PEI_Config_r17__F1 PEI_Config_r17__F2 PEI_Config_r17__helper1 PEI_Config_r17__helper2 PEI_Config_r17__helper3.

Opaque PEI_Config_r17__cond PEI_Config_r17__Format.

