Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PDSCH_TimeDomainResourceAllocation_r16.

Opaque PDSCH_TimeDomainResourceAllocation_r16__cond PDSCH_TimeDomainResourceAllocation_r16__Format.

Definition MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Type := list PDSCH_TimeDomainResourceAllocation_r16__Type.

Lemma MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__helper1 : (0 <= 1 <= maxNrofMultiplePDSCHs_r17)%Z. unfold maxNrofMultiplePDSCHs_r17.
 lia. Qed.
Lemma MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofMultiplePDSCHs_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofMultiplePDSCHs_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__cond (z : MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofMultiplePDSCHs_r17)%Z /\ (list_and PDSCH_TimeDomainResourceAllocation_r16__cond z) .

Record MultiPDSCH_TDRA_r17__Type : Set :=
  make__MultiPDSCH_TDRA_r17__Type {
    MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17 : MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Type ;
}.
Definition MultiPDSCH_TDRA_r17__root_list : list seq_elem := (
 Nor MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Type MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__cond ::
 nil).
Definition MultiPDSCH_TDRA_r17__ext_list : list typ := (
  nil).
Definition MultiPDSCH_TDRA_r17__cond (z : MultiPDSCH_TDRA_r17__Type) := 
(  MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__cond (MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17 z) /\
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
Definition MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Format : T_Format MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Type MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__cond := seq_of_format PDSCH_TimeDomainResourceAllocation_r16__Format 1 maxNrofMultiplePDSCHs_r17 MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__helper1 MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__helper2.

Opaque MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__cond MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Format.


Definition MultiPDSCH_TDRA_r17__root_Format_Type := Eval cbn in seq_format_prod MultiPDSCH_TDRA_r17__root_list.
Definition MultiPDSCH_TDRA_r17__root_Format_list : MultiPDSCH_TDRA_r17__root_Format_Type :=
  (MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17__Format, unit_format).

Definition MultiPDSCH_TDRA_r17__ext_Format_Type := Eval cbn in get_formats MultiPDSCH_TDRA_r17__ext_list.
Definition MultiPDSCH_TDRA_r17__ext_Format_list : MultiPDSCH_TDRA_r17__ext_Format_Type :=
  unit__Format.

Definition MultiPDSCH_TDRA_r17__list_type : Set := (seq_type MultiPDSCH_TDRA_r17__root_list) * (seq_ext_type MultiPDSCH_TDRA_r17__ext_list).
Definition MultiPDSCH_TDRA_r17__list_cond (z : MultiPDSCH_TDRA_r17__list_type) : Prop :=
        (seq_cond MultiPDSCH_TDRA_r17__root_list (fst z)) /\ (seq_ext_cond MultiPDSCH_TDRA_r17__ext_list (snd z)).
Definition MultiPDSCH_TDRA_r17__list_format : T_Format MultiPDSCH_TDRA_r17__list_type MultiPDSCH_TDRA_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MultiPDSCH_TDRA_r17__root_list MultiPDSCH_TDRA_r17__root_Format_list MultiPDSCH_TDRA_r17__ext_list MultiPDSCH_TDRA_r17__ext_Format_list.

Opaque MultiPDSCH_TDRA_r17__list_format.
Definition MultiPDSCH_TDRA_r17__F1 (z : MultiPDSCH_TDRA_r17__Type) : MultiPDSCH_TDRA_r17__list_type :=
  (((MultiPDSCH_TDRA_r17__pdsch_TDRA_List_r17 z, tt)), (
tt)).
Definition MultiPDSCH_TDRA_r17__F2 (y : MultiPDSCH_TDRA_r17__list_type) : MultiPDSCH_TDRA_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__MultiPDSCH_TDRA_r17__Type j0
  end.
Definition MultiPDSCH_TDRA_r17__helper1 : (forall a : MultiPDSCH_TDRA_r17__Type, MultiPDSCH_TDRA_r17__cond a -> MultiPDSCH_TDRA_r17__list_cond (MultiPDSCH_TDRA_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MultiPDSCH_TDRA_r17__helper2 : (forall a : MultiPDSCH_TDRA_r17__Type, MultiPDSCH_TDRA_r17__F2 (MultiPDSCH_TDRA_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MultiPDSCH_TDRA_r17__helper3 : (forall b : MultiPDSCH_TDRA_r17__list_type, MultiPDSCH_TDRA_r17__list_cond b -> MultiPDSCH_TDRA_r17__cond (MultiPDSCH_TDRA_r17__F2 b) /\ MultiPDSCH_TDRA_r17__F1 (MultiPDSCH_TDRA_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MultiPDSCH_TDRA_r17__cond, MultiPDSCH_TDRA_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MultiPDSCH_TDRA_r17__Format : T_Format MultiPDSCH_TDRA_r17__Type MultiPDSCH_TDRA_r17__cond :=
 proj2_format MultiPDSCH_TDRA_r17__cond MultiPDSCH_TDRA_r17__list_format  MultiPDSCH_TDRA_r17__F1 MultiPDSCH_TDRA_r17__F2 MultiPDSCH_TDRA_r17__helper1 MultiPDSCH_TDRA_r17__helper2 MultiPDSCH_TDRA_r17__helper3.

Opaque MultiPDSCH_TDRA_r17__cond MultiPDSCH_TDRA_r17__Format.

