Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Definition SSB_MTC4_r17__pci_List_r17__Type := list PhysCellId__Type.

Lemma SSB_MTC4_r17__pci_List_r17__helper1 : (0 <= 1 <= maxNrofPCIsPerSMTC)%Z. unfold maxNrofPCIsPerSMTC.
 lia. Qed.
Lemma SSB_MTC4_r17__pci_List_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPCIsPerSMTC - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPCIsPerSMTC - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC4_r17__pci_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC4_r17__pci_List_r17__cond (z : SSB_MTC4_r17__pci_List_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPCIsPerSMTC)%Z /\ (list_and PhysCellId__cond z) .

Lemma SSB_MTC4_r17__offset_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma SSB_MTC4_r17__offset_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC4_r17__offset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC4_r17__offset_r17__Type := Z.
Definition SSB_MTC4_r17__offset_r17__cond := (fun z => (0 <= z <= 159)%Z).
Record SSB_MTC4_r17__Type : Set :=
  make__SSB_MTC4_r17__Type {
    SSB_MTC4_r17__pci_List_r17 : option SSB_MTC4_r17__pci_List_r17__Type ;
    SSB_MTC4_r17__offset_r17 : Z ;
}.
Definition SSB_MTC4_r17__list := (
 Opt SSB_MTC4_r17__pci_List_r17__Type SSB_MTC4_r17__pci_List_r17__cond ::
 Nor Z SSB_MTC4_r17__offset_r17__cond ::
 nil).
Definition SSB_MTC4_r17__cond z := 
  opt_cond SSB_MTC4_r17__pci_List_r17__cond (SSB_MTC4_r17__pci_List_r17 z) /\
  SSB_MTC4_r17__offset_r17__cond (SSB_MTC4_r17__offset_r17 z) /\
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
Definition SSB_MTC4_r17__pci_List_r17__Format : T_Format SSB_MTC4_r17__pci_List_r17__Type SSB_MTC4_r17__pci_List_r17__cond := seq_of_format PhysCellId__Format 1 maxNrofPCIsPerSMTC SSB_MTC4_r17__pci_List_r17__helper1 SSB_MTC4_r17__pci_List_r17__helper2.

Opaque SSB_MTC4_r17__pci_List_r17__cond SSB_MTC4_r17__pci_List_r17__Format.

Definition SSB_MTC4_r17__offset_r17__Format : T_Format Z SSB_MTC4_r17__offset_r17__cond :=
 ranged_int_format (0) (159) SSB_MTC4_r17__offset_r17__helper1 SSB_MTC4_r17__offset_r17__helper2.

Opaque SSB_MTC4_r17__offset_r17__cond SSB_MTC4_r17__offset_r17__Format.


Definition SSB_MTC4_r17__Format_Type := Eval cbn in seq_format_prod SSB_MTC4_r17__list.
Definition SSB_MTC4_r17__Format_list : SSB_MTC4_r17__Format_Type :=
  (SSB_MTC4_r17__pci_List_r17__Format, (SSB_MTC4_r17__offset_r17__Format, unit_format)).
Definition SSB_MTC4_r17__list__Format := (*Eval compute in *) seq_format SSB_MTC4_r17__list SSB_MTC4_r17__Format_list.
Definition SSB_MTC4_r17__F1 z :=
  (SSB_MTC4_r17__pci_List_r17 z, (SSB_MTC4_r17__offset_r17 z, tt)).
Definition SSB_MTC4_r17__F2 (y : seq_type SSB_MTC4_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SSB_MTC4_r17__Type i0 i1
  end.
Lemma SSB_MTC4_r17__F1F2_cond (z : SSB_MTC4_r17__Type)
  : SSB_MTC4_r17__cond z ->
  (seq_cond SSB_MTC4_r17__list (SSB_MTC4_r17__F1 z)).
intro H. unfold SSB_MTC4_r17__cond in H. simpl. auto. Qed.
Lemma SSB_MTC4_r17__F1F2_cond2 (z : SSB_MTC4_r17__Type)
 : SSB_MTC4_r17__F2 (SSB_MTC4_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_MTC4_r17__F2F1_cond (y : seq_type SSB_MTC4_r17__list)
  : seq_cond SSB_MTC4_r17__list y ->
 (SSB_MTC4_r17__cond (SSB_MTC4_r17__F2 y)) /\  SSB_MTC4_r17__F1 (SSB_MTC4_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_MTC4_r17__cond. simpl in *. auto.
 - simpl. unfold SSB_MTC4_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_MTC4_r17__Format : T_Format SSB_MTC4_r17__Type SSB_MTC4_r17__cond :=
        proj2_format  SSB_MTC4_r17__cond SSB_MTC4_r17__list__Format
    SSB_MTC4_r17__F1 SSB_MTC4_r17__F2 SSB_MTC4_r17__F1F2_cond  SSB_MTC4_r17__F1F2_cond2 SSB_MTC4_r17__F2F1_cond.
Opaque SSB_MTC4_r17__cond SSB_MTC4_r17__Format.

