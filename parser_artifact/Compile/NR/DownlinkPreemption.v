Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Inductive DownlinkPreemption__timeFrequencySet__Type : Set :=
 | DownlinkPreemption__timeFrequencySet__set0
 | DownlinkPreemption__timeFrequencySet__set1
.
Definition DownlinkPreemption__timeFrequencySet__cond := (fun (_ : DownlinkPreemption__timeFrequencySet__Type) => True).
Lemma DownlinkPreemption__timeFrequencySet__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DownlinkPreemption__timeFrequencySet__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DownlinkPreemption__timeFrequencySet__nat__helper.

Definition DownlinkPreemption__timeFrequencySet__F1 t :=
  match t with
  | DownlinkPreemption__timeFrequencySet__set0 => 0
  | DownlinkPreemption__timeFrequencySet__set1 => 1
  end.
Definition DownlinkPreemption__timeFrequencySet__F2 n :=
  match n with
  | 0 => DownlinkPreemption__timeFrequencySet__set0
  | 1 => DownlinkPreemption__timeFrequencySet__set1
  | _ => DownlinkPreemption__timeFrequencySet__set0
  end.
Lemma DownlinkPreemption__timeFrequencySet__F1F2 : forall x : DownlinkPreemption__timeFrequencySet__Type, (DownlinkPreemption__timeFrequencySet__F1 x <= 1) /\ DownlinkPreemption__timeFrequencySet__F2 (DownlinkPreemption__timeFrequencySet__F1 x) = x. imp_solve. Qed.
Lemma DownlinkPreemption__timeFrequencySet__F2F1 : forall (y : nat) (H : y <= 1), DownlinkPreemption__timeFrequencySet__F1 (DownlinkPreemption__timeFrequencySet__F2 y) = y. enum_solve H y. Qed.

Lemma DownlinkPreemption__dci_PayloadSize__helper1 : (0 <= maxINT_DCI_PayloadSize)%Z. unfold maxINT_DCI_PayloadSize.
 lia. Qed.
Lemma DownlinkPreemption__dci_PayloadSize__helper2 : to_bit_sz (Z.to_nat (maxINT_DCI_PayloadSize - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxINT_DCI_PayloadSize - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DownlinkPreemption__dci_PayloadSize__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DownlinkPreemption__dci_PayloadSize__Type := Z.
Definition DownlinkPreemption__dci_PayloadSize__cond := (fun z => (0 <= z <= maxINT_DCI_PayloadSize)%Z).
Require Import NR.INT_ConfigurationPerServingCell.

Opaque INT_ConfigurationPerServingCell__cond INT_ConfigurationPerServingCell__Format.

Definition DownlinkPreemption__int_ConfigurationPerServingCell__Type := list INT_ConfigurationPerServingCell__Type.

Lemma DownlinkPreemption__int_ConfigurationPerServingCell__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma DownlinkPreemption__int_ConfigurationPerServingCell__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DownlinkPreemption__int_ConfigurationPerServingCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DownlinkPreemption__int_ConfigurationPerServingCell__cond (z : DownlinkPreemption__int_ConfigurationPerServingCell__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and INT_ConfigurationPerServingCell__cond z) .

Record DownlinkPreemption__Type : Set :=
  make__DownlinkPreemption__Type {
    DownlinkPreemption__int_RNTI : RNTI_Value__Type ;
    DownlinkPreemption__timeFrequencySet : DownlinkPreemption__timeFrequencySet__Type ;
    DownlinkPreemption__dci_PayloadSize : Z ;
    DownlinkPreemption__int_ConfigurationPerServingCell : DownlinkPreemption__int_ConfigurationPerServingCell__Type ;
}.
Definition DownlinkPreemption__root_list : list seq_elem := (
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor DownlinkPreemption__timeFrequencySet__Type DownlinkPreemption__timeFrequencySet__cond ::
 Nor Z DownlinkPreemption__dci_PayloadSize__cond ::
 Nor DownlinkPreemption__int_ConfigurationPerServingCell__Type DownlinkPreemption__int_ConfigurationPerServingCell__cond ::
 nil).
Definition DownlinkPreemption__ext_list : list typ := (
  nil).
Definition DownlinkPreemption__cond (z : DownlinkPreemption__Type) := 
(  RNTI_Value__cond (DownlinkPreemption__int_RNTI z) /\
  DownlinkPreemption__timeFrequencySet__cond (DownlinkPreemption__timeFrequencySet z) /\
  DownlinkPreemption__dci_PayloadSize__cond (DownlinkPreemption__dci_PayloadSize z) /\
  DownlinkPreemption__int_ConfigurationPerServingCell__cond (DownlinkPreemption__int_ConfigurationPerServingCell z) /\
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
Definition DownlinkPreemption__timeFrequencySet__Format : T_Format DownlinkPreemption__timeFrequencySet__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DownlinkPreemption__timeFrequencySet__nat__Format DownlinkPreemption__timeFrequencySet__F1 DownlinkPreemption__timeFrequencySet__F2 DownlinkPreemption__timeFrequencySet__F1F2 DownlinkPreemption__timeFrequencySet__F2F1.

Opaque DownlinkPreemption__timeFrequencySet__cond DownlinkPreemption__timeFrequencySet__Format.

Definition DownlinkPreemption__dci_PayloadSize__Format : T_Format Z DownlinkPreemption__dci_PayloadSize__cond :=
 ranged_int_format (0) (maxINT_DCI_PayloadSize) DownlinkPreemption__dci_PayloadSize__helper1 DownlinkPreemption__dci_PayloadSize__helper2.

Opaque DownlinkPreemption__dci_PayloadSize__cond DownlinkPreemption__dci_PayloadSize__Format.

Definition DownlinkPreemption__int_ConfigurationPerServingCell__Format : T_Format DownlinkPreemption__int_ConfigurationPerServingCell__Type DownlinkPreemption__int_ConfigurationPerServingCell__cond := seq_of_format INT_ConfigurationPerServingCell__Format 1 maxNrofServingCells DownlinkPreemption__int_ConfigurationPerServingCell__helper1 DownlinkPreemption__int_ConfigurationPerServingCell__helper2.

Opaque DownlinkPreemption__int_ConfigurationPerServingCell__cond DownlinkPreemption__int_ConfigurationPerServingCell__Format.


Definition DownlinkPreemption__root_Format_Type := Eval cbn in seq_format_prod DownlinkPreemption__root_list.
Definition DownlinkPreemption__root_Format_list : DownlinkPreemption__root_Format_Type :=
  (RNTI_Value__Format, (DownlinkPreemption__timeFrequencySet__Format, (DownlinkPreemption__dci_PayloadSize__Format, (DownlinkPreemption__int_ConfigurationPerServingCell__Format, unit_format)))).

Definition DownlinkPreemption__ext_Format_Type := Eval cbn in get_formats DownlinkPreemption__ext_list.
Definition DownlinkPreemption__ext_Format_list : DownlinkPreemption__ext_Format_Type :=
  unit__Format.

Definition DownlinkPreemption__list_type : Set := (seq_type DownlinkPreemption__root_list) * (seq_ext_type DownlinkPreemption__ext_list).
Definition DownlinkPreemption__list_cond (z : DownlinkPreemption__list_type) : Prop :=
        (seq_cond DownlinkPreemption__root_list (fst z)) /\ (seq_ext_cond DownlinkPreemption__ext_list (snd z)).
Definition DownlinkPreemption__list_format : T_Format DownlinkPreemption__list_type DownlinkPreemption__list_cond :=
 (* Eval compute in *) seq_ext_format DownlinkPreemption__root_list DownlinkPreemption__root_Format_list DownlinkPreemption__ext_list DownlinkPreemption__ext_Format_list.

Opaque DownlinkPreemption__list_format.
Definition DownlinkPreemption__F1 (z : DownlinkPreemption__Type) : DownlinkPreemption__list_type :=
  (((DownlinkPreemption__int_RNTI z, (DownlinkPreemption__timeFrequencySet z, (DownlinkPreemption__dci_PayloadSize z, (DownlinkPreemption__int_ConfigurationPerServingCell z, tt))))), (
tt)).
Definition DownlinkPreemption__F2 (y : DownlinkPreemption__list_type) : DownlinkPreemption__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__DownlinkPreemption__Type j0 j1 j2 j3
  end.
Definition DownlinkPreemption__helper1 : (forall a : DownlinkPreemption__Type, DownlinkPreemption__cond a -> DownlinkPreemption__list_cond (DownlinkPreemption__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DownlinkPreemption__helper2 : (forall a : DownlinkPreemption__Type, DownlinkPreemption__F2 (DownlinkPreemption__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DownlinkPreemption__helper3 : (forall b : DownlinkPreemption__list_type, DownlinkPreemption__list_cond b -> DownlinkPreemption__cond (DownlinkPreemption__F2 b) /\ DownlinkPreemption__F1 (DownlinkPreemption__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DownlinkPreemption__cond, DownlinkPreemption__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DownlinkPreemption__Format : T_Format DownlinkPreemption__Type DownlinkPreemption__cond :=
 proj2_format DownlinkPreemption__cond DownlinkPreemption__list_format  DownlinkPreemption__F1 DownlinkPreemption__F2 DownlinkPreemption__helper1 DownlinkPreemption__helper2 DownlinkPreemption__helper3.

Opaque DownlinkPreemption__cond DownlinkPreemption__Format.

