Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Definition SSB_MTC2__pci_List__Type := list PhysCellId__Type.

Lemma SSB_MTC2__pci_List__helper1 : (0 <= 1 <= maxNrofPCIsPerSMTC)%Z. unfold maxNrofPCIsPerSMTC.
 lia. Qed.
Lemma SSB_MTC2__pci_List__helper2 : to_bit_sz (Z.to_nat (maxNrofPCIsPerSMTC - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPCIsPerSMTC - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC2__pci_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC2__pci_List__cond (z : SSB_MTC2__pci_List__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPCIsPerSMTC)%Z /\ (list_and PhysCellId__cond z) .

Inductive SSB_MTC2__periodicity__Type : Set :=
 | SSB_MTC2__periodicity__sf5
 | SSB_MTC2__periodicity__sf10
 | SSB_MTC2__periodicity__sf20
 | SSB_MTC2__periodicity__sf40
 | SSB_MTC2__periodicity__sf80
 | SSB_MTC2__periodicity__spare3
 | SSB_MTC2__periodicity__spare2
 | SSB_MTC2__periodicity__spare1
.
Definition SSB_MTC2__periodicity__cond := (fun (_ : SSB_MTC2__periodicity__Type) => True).
Lemma SSB_MTC2__periodicity__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SSB_MTC2__periodicity__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SSB_MTC2__periodicity__nat__helper.

Definition SSB_MTC2__periodicity__F1 t :=
  match t with
  | SSB_MTC2__periodicity__sf5 => 0
  | SSB_MTC2__periodicity__sf10 => 1
  | SSB_MTC2__periodicity__sf20 => 2
  | SSB_MTC2__periodicity__sf40 => 3
  | SSB_MTC2__periodicity__sf80 => 4
  | SSB_MTC2__periodicity__spare3 => 5
  | SSB_MTC2__periodicity__spare2 => 6
  | SSB_MTC2__periodicity__spare1 => 7
  end.
Definition SSB_MTC2__periodicity__F2 n :=
  match n with
  | 0 => SSB_MTC2__periodicity__sf5
  | 1 => SSB_MTC2__periodicity__sf10
  | 2 => SSB_MTC2__periodicity__sf20
  | 3 => SSB_MTC2__periodicity__sf40
  | 4 => SSB_MTC2__periodicity__sf80
  | 5 => SSB_MTC2__periodicity__spare3
  | 6 => SSB_MTC2__periodicity__spare2
  | 7 => SSB_MTC2__periodicity__spare1
  | _ => SSB_MTC2__periodicity__sf5
  end.
Lemma SSB_MTC2__periodicity__F1F2 : forall x : SSB_MTC2__periodicity__Type, (SSB_MTC2__periodicity__F1 x <= 7) /\ SSB_MTC2__periodicity__F2 (SSB_MTC2__periodicity__F1 x) = x. imp_solve. Qed.
Lemma SSB_MTC2__periodicity__F2F1 : forall (y : nat) (H : y <= 7), SSB_MTC2__periodicity__F1 (SSB_MTC2__periodicity__F2 y) = y. enum_solve H y. Qed.

Record SSB_MTC2__Type : Set :=
  make__SSB_MTC2__Type {
    SSB_MTC2__pci_List : option SSB_MTC2__pci_List__Type ;
    SSB_MTC2__periodicity : SSB_MTC2__periodicity__Type ;
}.
Definition SSB_MTC2__list := (
 Opt SSB_MTC2__pci_List__Type SSB_MTC2__pci_List__cond ::
 Nor SSB_MTC2__periodicity__Type SSB_MTC2__periodicity__cond ::
 nil).
Definition SSB_MTC2__cond z := 
  opt_cond SSB_MTC2__pci_List__cond (SSB_MTC2__pci_List z) /\
  SSB_MTC2__periodicity__cond (SSB_MTC2__periodicity z) /\
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
Definition SSB_MTC2__pci_List__Format : T_Format SSB_MTC2__pci_List__Type SSB_MTC2__pci_List__cond := seq_of_format PhysCellId__Format 1 maxNrofPCIsPerSMTC SSB_MTC2__pci_List__helper1 SSB_MTC2__pci_List__helper2.

Opaque SSB_MTC2__pci_List__cond SSB_MTC2__pci_List__Format.

Definition SSB_MTC2__periodicity__Format : T_Format SSB_MTC2__periodicity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SSB_MTC2__periodicity__nat__Format SSB_MTC2__periodicity__F1 SSB_MTC2__periodicity__F2 SSB_MTC2__periodicity__F1F2 SSB_MTC2__periodicity__F2F1.

Opaque SSB_MTC2__periodicity__cond SSB_MTC2__periodicity__Format.


Definition SSB_MTC2__Format_Type := Eval cbn in seq_format_prod SSB_MTC2__list.
Definition SSB_MTC2__Format_list : SSB_MTC2__Format_Type :=
  (SSB_MTC2__pci_List__Format, (SSB_MTC2__periodicity__Format, unit_format)).
Definition SSB_MTC2__list__Format := (*Eval compute in *) seq_format SSB_MTC2__list SSB_MTC2__Format_list.
Definition SSB_MTC2__F1 z :=
  (SSB_MTC2__pci_List z, (SSB_MTC2__periodicity z, tt)).
Definition SSB_MTC2__F2 (y : seq_type SSB_MTC2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SSB_MTC2__Type i0 i1
  end.
Lemma SSB_MTC2__F1F2_cond (z : SSB_MTC2__Type)
  : SSB_MTC2__cond z ->
  (seq_cond SSB_MTC2__list (SSB_MTC2__F1 z)).
intro H. unfold SSB_MTC2__cond in H. simpl. auto. Qed.
Lemma SSB_MTC2__F1F2_cond2 (z : SSB_MTC2__Type)
 : SSB_MTC2__F2 (SSB_MTC2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_MTC2__F2F1_cond (y : seq_type SSB_MTC2__list)
  : seq_cond SSB_MTC2__list y ->
 (SSB_MTC2__cond (SSB_MTC2__F2 y)) /\  SSB_MTC2__F1 (SSB_MTC2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_MTC2__cond. simpl in *. auto.
 - simpl. unfold SSB_MTC2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_MTC2__Format : T_Format SSB_MTC2__Type SSB_MTC2__cond :=
        proj2_format  SSB_MTC2__cond SSB_MTC2__list__Format
    SSB_MTC2__F1 SSB_MTC2__F2 SSB_MTC2__F1F2_cond  SSB_MTC2__F1F2_cond2 SSB_MTC2__F2F1_cond.
Opaque SSB_MTC2__cond SSB_MTC2__Format.

