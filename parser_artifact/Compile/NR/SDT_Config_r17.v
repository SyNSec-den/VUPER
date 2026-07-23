Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.

Definition SDT_Config_r17__sdt_DRB_List_r17__Type := list DRB_Identity__Type.

Lemma SDT_Config_r17__sdt_DRB_List_r17__helper1 : (0 <= 0 <= maxDRB)%Z. unfold maxDRB.
 lia. Qed.
Lemma SDT_Config_r17__sdt_DRB_List_r17__helper2 : to_bit_sz (Z.to_nat (maxDRB - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDRB - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SDT_Config_r17__sdt_DRB_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SDT_Config_r17__sdt_DRB_List_r17__cond (z : SDT_Config_r17__sdt_DRB_List_r17__Type) :=  (0 <= Z.of_nat (length z) <= maxDRB)%Z /\ (list_and DRB_Identity__cond z) .

Inductive SDT_Config_r17__sdt_SRB2_Indication_r17__Type : Set :=
 | SDT_Config_r17__sdt_SRB2_Indication_r17__allowed
.
Definition SDT_Config_r17__sdt_SRB2_Indication_r17__cond := (fun (_ : SDT_Config_r17__sdt_SRB2_Indication_r17__Type) => True).
Lemma SDT_Config_r17__sdt_SRB2_Indication_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDT_Config_r17__sdt_SRB2_Indication_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SDT_Config_r17__sdt_SRB2_Indication_r17__nat__helper.

Definition SDT_Config_r17__sdt_SRB2_Indication_r17__F1 t :=
  match t with
  | SDT_Config_r17__sdt_SRB2_Indication_r17__allowed => 0
  end.
Definition SDT_Config_r17__sdt_SRB2_Indication_r17__F2 n :=
  match n with
  | 0 => SDT_Config_r17__sdt_SRB2_Indication_r17__allowed
  | _ => SDT_Config_r17__sdt_SRB2_Indication_r17__allowed
  end.
Lemma SDT_Config_r17__sdt_SRB2_Indication_r17__F1F2 : forall x : SDT_Config_r17__sdt_SRB2_Indication_r17__Type, (SDT_Config_r17__sdt_SRB2_Indication_r17__F1 x <= 0) /\ SDT_Config_r17__sdt_SRB2_Indication_r17__F2 (SDT_Config_r17__sdt_SRB2_Indication_r17__F1 x) = x. imp_solve. Qed.
Lemma SDT_Config_r17__sdt_SRB2_Indication_r17__F2F1 : forall (y : nat) (H : y <= 0), SDT_Config_r17__sdt_SRB2_Indication_r17__F1 (SDT_Config_r17__sdt_SRB2_Indication_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.SDT_CG_Config_r17.
Definition SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Type := SetupRelease__Type SDT_CG_Config_r17__Type.
Definition SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__cond := SetupRelease__cond _ SDT_CG_Config_r17__cond.
Definition SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Format : T_Format SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Type SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__cond := SetupRelease__Format _ _ SDT_CG_Config_r17__Format.
Opaque SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__cond SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Format.

Inductive SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Type : Set :=
 | SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cell
 | SDT_Config_r17__sdt_DRB_ContinueROHC_r17__rna
.
Definition SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cond := (fun (_ : SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Type) => True).
Lemma SDT_Config_r17__sdt_DRB_ContinueROHC_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDT_Config_r17__sdt_DRB_ContinueROHC_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SDT_Config_r17__sdt_DRB_ContinueROHC_r17__nat__helper.

Definition SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1 t :=
  match t with
  | SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cell => 0
  | SDT_Config_r17__sdt_DRB_ContinueROHC_r17__rna => 1
  end.
Definition SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F2 n :=
  match n with
  | 0 => SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cell
  | 1 => SDT_Config_r17__sdt_DRB_ContinueROHC_r17__rna
  | _ => SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cell
  end.
Lemma SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1F2 : forall x : SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Type, (SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1 x <= 1) /\ SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F2 (SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1 x) = x. imp_solve. Qed.
Lemma SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F2F1 : forall (y : nat) (H : y <= 1), SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1 (SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F2 y) = y. enum_solve H y. Qed.

Record SDT_Config_r17__Type : Set :=
  make__SDT_Config_r17__Type {
    SDT_Config_r17__sdt_DRB_List_r17 : option SDT_Config_r17__sdt_DRB_List_r17__Type ;
    SDT_Config_r17__sdt_SRB2_Indication_r17 : option SDT_Config_r17__sdt_SRB2_Indication_r17__Type ;
    SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17 : option SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Type ;
    SDT_Config_r17__sdt_DRB_ContinueROHC_r17 : option SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Type ;
}.
Definition SDT_Config_r17__list := (
 Opt SDT_Config_r17__sdt_DRB_List_r17__Type SDT_Config_r17__sdt_DRB_List_r17__cond ::
 Opt SDT_Config_r17__sdt_SRB2_Indication_r17__Type SDT_Config_r17__sdt_SRB2_Indication_r17__cond ::
 Opt SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Type SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__cond ::
 Opt SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Type SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cond ::
 nil).
Definition SDT_Config_r17__cond z := 
  opt_cond SDT_Config_r17__sdt_DRB_List_r17__cond (SDT_Config_r17__sdt_DRB_List_r17 z) /\
  opt_cond SDT_Config_r17__sdt_SRB2_Indication_r17__cond (SDT_Config_r17__sdt_SRB2_Indication_r17 z) /\
  opt_cond SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__cond (SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17 z) /\
  opt_cond SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cond (SDT_Config_r17__sdt_DRB_ContinueROHC_r17 z) /\
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
Definition SDT_Config_r17__sdt_DRB_List_r17__Format : T_Format SDT_Config_r17__sdt_DRB_List_r17__Type SDT_Config_r17__sdt_DRB_List_r17__cond := seq_of_format DRB_Identity__Format 0 maxDRB SDT_Config_r17__sdt_DRB_List_r17__helper1 SDT_Config_r17__sdt_DRB_List_r17__helper2.

Opaque SDT_Config_r17__sdt_DRB_List_r17__cond SDT_Config_r17__sdt_DRB_List_r17__Format.

Definition SDT_Config_r17__sdt_SRB2_Indication_r17__Format : T_Format SDT_Config_r17__sdt_SRB2_Indication_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDT_Config_r17__sdt_SRB2_Indication_r17__nat__Format SDT_Config_r17__sdt_SRB2_Indication_r17__F1 SDT_Config_r17__sdt_SRB2_Indication_r17__F2 SDT_Config_r17__sdt_SRB2_Indication_r17__F1F2 SDT_Config_r17__sdt_SRB2_Indication_r17__F2F1.

Opaque SDT_Config_r17__sdt_SRB2_Indication_r17__cond SDT_Config_r17__sdt_SRB2_Indication_r17__Format.

Opaque SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__cond SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Format.

Definition SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Format : T_Format SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDT_Config_r17__sdt_DRB_ContinueROHC_r17__nat__Format SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1 SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F2 SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F1F2 SDT_Config_r17__sdt_DRB_ContinueROHC_r17__F2F1.

Opaque SDT_Config_r17__sdt_DRB_ContinueROHC_r17__cond SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Format.


Definition SDT_Config_r17__Format_Type := Eval cbn in seq_format_prod SDT_Config_r17__list.
Definition SDT_Config_r17__Format_list : SDT_Config_r17__Format_Type :=
  (SDT_Config_r17__sdt_DRB_List_r17__Format, (SDT_Config_r17__sdt_SRB2_Indication_r17__Format, (SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17__Format, (SDT_Config_r17__sdt_DRB_ContinueROHC_r17__Format, unit_format)))).
Definition SDT_Config_r17__list__Format := (*Eval compute in *) seq_format SDT_Config_r17__list SDT_Config_r17__Format_list.
Definition SDT_Config_r17__F1 z :=
  (SDT_Config_r17__sdt_DRB_List_r17 z, (SDT_Config_r17__sdt_SRB2_Indication_r17 z, (SDT_Config_r17__sdt_MAC_PHY_CG_Config_r17 z, (SDT_Config_r17__sdt_DRB_ContinueROHC_r17 z, tt)))).
Definition SDT_Config_r17__F2 (y : seq_type SDT_Config_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SDT_Config_r17__Type i0 i1 i2 i3
  end.
Lemma SDT_Config_r17__F1F2_cond (z : SDT_Config_r17__Type)
  : SDT_Config_r17__cond z ->
  (seq_cond SDT_Config_r17__list (SDT_Config_r17__F1 z)).
intro H. unfold SDT_Config_r17__cond in H. simpl. auto. Qed.
Lemma SDT_Config_r17__F1F2_cond2 (z : SDT_Config_r17__Type)
 : SDT_Config_r17__F2 (SDT_Config_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SDT_Config_r17__F2F1_cond (y : seq_type SDT_Config_r17__list)
  : seq_cond SDT_Config_r17__list y ->
 (SDT_Config_r17__cond (SDT_Config_r17__F2 y)) /\  SDT_Config_r17__F1 (SDT_Config_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SDT_Config_r17__cond. simpl in *. auto.
 - simpl. unfold SDT_Config_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SDT_Config_r17__Format : T_Format SDT_Config_r17__Type SDT_Config_r17__cond :=
        proj2_format  SDT_Config_r17__cond SDT_Config_r17__list__Format
    SDT_Config_r17__F1 SDT_Config_r17__F2 SDT_Config_r17__F1F2_cond  SDT_Config_r17__F1F2_cond2 SDT_Config_r17__F2F1_cond.
Opaque SDT_Config_r17__cond SDT_Config_r17__Format.

