Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_RS_Index.

Opaque CSI_RS_Index__cond CSI_RS_Index__Format.

Lemma CSI_RS_Resource_Mobility__slotConfig__ms4__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__slotConfig__ms4__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__slotConfig__ms4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__slotConfig__ms4__Type := Z.
Definition CSI_RS_Resource_Mobility__slotConfig__ms4__cond := (fun z => (0 <= z <= 31)%Z).
Lemma CSI_RS_Resource_Mobility__slotConfig__ms5__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__slotConfig__ms5__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__slotConfig__ms5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__slotConfig__ms5__Type := Z.
Definition CSI_RS_Resource_Mobility__slotConfig__ms5__cond := (fun z => (0 <= z <= 39)%Z).
Lemma CSI_RS_Resource_Mobility__slotConfig__ms10__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__slotConfig__ms10__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__slotConfig__ms10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__slotConfig__ms10__Type := Z.
Definition CSI_RS_Resource_Mobility__slotConfig__ms10__cond := (fun z => (0 <= z <= 79)%Z).
Lemma CSI_RS_Resource_Mobility__slotConfig__ms20__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__slotConfig__ms20__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__slotConfig__ms20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__slotConfig__ms20__Type := Z.
Definition CSI_RS_Resource_Mobility__slotConfig__ms20__cond := (fun z => (0 <= z <= 159)%Z).
Lemma CSI_RS_Resource_Mobility__slotConfig__ms40__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__slotConfig__ms40__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__slotConfig__ms40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__slotConfig__ms40__Type := Z.
Definition CSI_RS_Resource_Mobility__slotConfig__ms40__cond := (fun z => (0 <= z <= 319)%Z).

Inductive CSI_RS_Resource_Mobility__slotConfig__Type : Set :=
  | CSI_RS_Resource_Mobility__slotConfig__ms4 : Z -> CSI_RS_Resource_Mobility__slotConfig__Type
  | CSI_RS_Resource_Mobility__slotConfig__ms5 : Z -> CSI_RS_Resource_Mobility__slotConfig__Type
  | CSI_RS_Resource_Mobility__slotConfig__ms10 : Z -> CSI_RS_Resource_Mobility__slotConfig__Type
  | CSI_RS_Resource_Mobility__slotConfig__ms20 : Z -> CSI_RS_Resource_Mobility__slotConfig__Type
  | CSI_RS_Resource_Mobility__slotConfig__ms40 : Z -> CSI_RS_Resource_Mobility__slotConfig__Type
.
Definition CSI_RS_Resource_Mobility__slotConfig__list : list typ := (
typ_cons Z CSI_RS_Resource_Mobility__slotConfig__ms4__cond ::
typ_cons Z CSI_RS_Resource_Mobility__slotConfig__ms5__cond ::
typ_cons Z CSI_RS_Resource_Mobility__slotConfig__ms10__cond ::
typ_cons Z CSI_RS_Resource_Mobility__slotConfig__ms20__cond ::
typ_cons Z CSI_RS_Resource_Mobility__slotConfig__ms40__cond ::
 nil).
Definition CSI_RS_Resource_Mobility__slotConfig__cond (c : CSI_RS_Resource_Mobility__slotConfig__Type) := 
  match c with
  | CSI_RS_Resource_Mobility__slotConfig__ms4 t => CSI_RS_Resource_Mobility__slotConfig__ms4__cond t 
  | CSI_RS_Resource_Mobility__slotConfig__ms5 t => CSI_RS_Resource_Mobility__slotConfig__ms5__cond t 
  | CSI_RS_Resource_Mobility__slotConfig__ms10 t => CSI_RS_Resource_Mobility__slotConfig__ms10__cond t 
  | CSI_RS_Resource_Mobility__slotConfig__ms20 t => CSI_RS_Resource_Mobility__slotConfig__ms20__cond t 
  | CSI_RS_Resource_Mobility__slotConfig__ms40 t => CSI_RS_Resource_Mobility__slotConfig__ms40__cond t 
  end.

Lemma CSI_RS_Resource_Mobility__slotConfig__len_helper1 : to_bit_sz (length CSI_RS_Resource_Mobility__slotConfig__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_RS_Resource_Mobility__slotConfig__len_helper2 : 2 <= length2 CSI_RS_Resource_Mobility__slotConfig__list.
 simpl. lia. Qed.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Record CSI_RS_Resource_Mobility__associatedSSB__Type : Set :=
  make__CSI_RS_Resource_Mobility__associatedSSB__Type {
    CSI_RS_Resource_Mobility__associatedSSB__ssb_Index : SSB_Index__Type ;
    CSI_RS_Resource_Mobility__associatedSSB__isQuasiColocated : bool ;
}.
Definition CSI_RS_Resource_Mobility__associatedSSB__list := (
 Nor SSB_Index__Type SSB_Index__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition CSI_RS_Resource_Mobility__associatedSSB__cond z := 
  SSB_Index__cond (CSI_RS_Resource_Mobility__associatedSSB__ssb_Index z) /\
  (fun _ => True) (CSI_RS_Resource_Mobility__associatedSSB__isQuasiColocated z) /\
  True.

Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Type := bit_string_fixed.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Type := bit_string_fixed.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 12 /\ bit_string_len_prop (fst z) (snd z)).

Inductive CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type : Set :=
  | CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1 : CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Type -> CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type
  | CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2 : CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Type -> CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type
.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__list : list typ := (
typ_cons CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Type CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__cond ::
typ_cons CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Type CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__cond ::
 nil).
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond (c : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type) := 
  match c with
  | CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1 t => CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__cond t 
  | CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2 t => CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__cond t 
  end.

Lemma CSI_RS_Resource_Mobility__frequencyDomainAllocation__len_helper1 : to_bit_sz (length CSI_RS_Resource_Mobility__frequencyDomainAllocation__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_RS_Resource_Mobility__frequencyDomainAllocation__len_helper2 : 2 <= length2 CSI_RS_Resource_Mobility__frequencyDomainAllocation__list.
 simpl. lia. Qed.
Lemma CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__Type := Z.
Definition CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__cond := (fun z => (0 <= z <= 13)%Z).
Lemma CSI_RS_Resource_Mobility__sequenceGenerationConfig__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__sequenceGenerationConfig__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__sequenceGenerationConfig__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__sequenceGenerationConfig__Type := Z.
Definition CSI_RS_Resource_Mobility__sequenceGenerationConfig__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__Type := Z.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__cond := (fun z => (0 <= z <= 255)%Z).
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__Type := Z.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__cond := (fun z => (0 <= z <= 319)%Z).
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__Type := Z.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__cond := (fun z => (0 <= z <= 639)%Z).
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__Type := Z.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__Type := Z.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__cond := (fun z => (0 <= z <= 2559)%Z).

Inductive CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type : Set :=
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4 : Z -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5 : Z -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10 : Z -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20 : Z -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40 : Z -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type
.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list : list typ := (
typ_cons Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__cond ::
typ_cons Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__cond ::
typ_cons Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__cond ::
typ_cons Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__cond ::
typ_cons Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__cond ::
 nil).
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond (c : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type) := 
  match c with
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4 t => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__cond t 
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5 t => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__cond t 
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10 t => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__cond t 
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20 t => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__cond t 
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40 t => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__cond t 
  end.

Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__len_helper1 : to_bit_sz (length CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__len_helper2 : 2 <= length2 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list.
 simpl. lia. Qed.
Record CSI_RS_Resource_Mobility__ext0O__Type : Set :=
  make__CSI_RS_Resource_Mobility__ext0O__Type {
    CSI_RS_Resource_Mobility__ext0O__slotConfig_r17 : option CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type ;
}.
Definition CSI_RS_Resource_Mobility__ext0O__list := (
 Opt CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond ::
 nil).
Definition CSI_RS_Resource_Mobility__ext0O__cond z := 
  opt_cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17 z) /\
  True.

Definition CSI_RS_Resource_Mobility__ext0__Type := CSI_RS_Resource_Mobility__ext0O__Type.
Definition CSI_RS_Resource_Mobility__ext0__cond := CSI_RS_Resource_Mobility__ext0O__cond.

Record CSI_RS_Resource_Mobility__Type : Set :=
  make__CSI_RS_Resource_Mobility__Type {
    CSI_RS_Resource_Mobility__csi_RS_Index : CSI_RS_Index__Type ;
    CSI_RS_Resource_Mobility__slotConfig : CSI_RS_Resource_Mobility__slotConfig__Type ;
    CSI_RS_Resource_Mobility__associatedSSB : option CSI_RS_Resource_Mobility__associatedSSB__Type ;
    CSI_RS_Resource_Mobility__frequencyDomainAllocation : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type ;
    CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain : Z ;
    CSI_RS_Resource_Mobility__sequenceGenerationConfig : Z ;
    CSI_RS_Resource_Mobility__ext0 : option CSI_RS_Resource_Mobility__ext0__Type ;
}.
Definition CSI_RS_Resource_Mobility__root_list : list seq_elem := (
 Nor CSI_RS_Index__Type CSI_RS_Index__cond ::
 Nor CSI_RS_Resource_Mobility__slotConfig__Type CSI_RS_Resource_Mobility__slotConfig__cond ::
 Opt CSI_RS_Resource_Mobility__associatedSSB__Type CSI_RS_Resource_Mobility__associatedSSB__cond ::
 Nor CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond ::
 Nor Z CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__cond ::
 Nor Z CSI_RS_Resource_Mobility__sequenceGenerationConfig__cond ::
 nil).
Definition CSI_RS_Resource_Mobility__ext_list : list typ := (
  typ_cons CSI_RS_Resource_Mobility__ext0__Type CSI_RS_Resource_Mobility__ext0__cond ::
  nil).
Definition CSI_RS_Resource_Mobility__cond (z : CSI_RS_Resource_Mobility__Type) := 
(  CSI_RS_Index__cond (CSI_RS_Resource_Mobility__csi_RS_Index z) /\
  CSI_RS_Resource_Mobility__slotConfig__cond (CSI_RS_Resource_Mobility__slotConfig z) /\
  opt_cond CSI_RS_Resource_Mobility__associatedSSB__cond (CSI_RS_Resource_Mobility__associatedSSB z) /\
  CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond (CSI_RS_Resource_Mobility__frequencyDomainAllocation z) /\
  CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__cond (CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain z) /\
  CSI_RS_Resource_Mobility__sequenceGenerationConfig__cond (CSI_RS_Resource_Mobility__sequenceGenerationConfig z) /\
  True) /\ 
(  opt_cond CSI_RS_Resource_Mobility__ext0__cond (CSI_RS_Resource_Mobility__ext0 z) /\
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
Definition CSI_RS_Resource_Mobility__slotConfig__ms4__Format : T_Format Z CSI_RS_Resource_Mobility__slotConfig__ms4__cond :=
 ranged_int_format (0) (31) CSI_RS_Resource_Mobility__slotConfig__ms4__helper1 CSI_RS_Resource_Mobility__slotConfig__ms4__helper2.

Opaque CSI_RS_Resource_Mobility__slotConfig__ms4__cond CSI_RS_Resource_Mobility__slotConfig__ms4__Format.

Definition CSI_RS_Resource_Mobility__slotConfig__ms5__Format : T_Format Z CSI_RS_Resource_Mobility__slotConfig__ms5__cond :=
 ranged_int_format (0) (39) CSI_RS_Resource_Mobility__slotConfig__ms5__helper1 CSI_RS_Resource_Mobility__slotConfig__ms5__helper2.

Opaque CSI_RS_Resource_Mobility__slotConfig__ms5__cond CSI_RS_Resource_Mobility__slotConfig__ms5__Format.

Definition CSI_RS_Resource_Mobility__slotConfig__ms10__Format : T_Format Z CSI_RS_Resource_Mobility__slotConfig__ms10__cond :=
 ranged_int_format (0) (79) CSI_RS_Resource_Mobility__slotConfig__ms10__helper1 CSI_RS_Resource_Mobility__slotConfig__ms10__helper2.

Opaque CSI_RS_Resource_Mobility__slotConfig__ms10__cond CSI_RS_Resource_Mobility__slotConfig__ms10__Format.

Definition CSI_RS_Resource_Mobility__slotConfig__ms20__Format : T_Format Z CSI_RS_Resource_Mobility__slotConfig__ms20__cond :=
 ranged_int_format (0) (159) CSI_RS_Resource_Mobility__slotConfig__ms20__helper1 CSI_RS_Resource_Mobility__slotConfig__ms20__helper2.

Opaque CSI_RS_Resource_Mobility__slotConfig__ms20__cond CSI_RS_Resource_Mobility__slotConfig__ms20__Format.

Definition CSI_RS_Resource_Mobility__slotConfig__ms40__Format : T_Format Z CSI_RS_Resource_Mobility__slotConfig__ms40__cond :=
 ranged_int_format (0) (319) CSI_RS_Resource_Mobility__slotConfig__ms40__helper1 CSI_RS_Resource_Mobility__slotConfig__ms40__helper2.

Opaque CSI_RS_Resource_Mobility__slotConfig__ms40__cond CSI_RS_Resource_Mobility__slotConfig__ms40__Format.


Definition CSI_RS_Resource_Mobility__slotConfig__Format_Type := Eval cbn in get_formats CSI_RS_Resource_Mobility__slotConfig__list.
Definition CSI_RS_Resource_Mobility__slotConfig__Format_list : CSI_RS_Resource_Mobility__slotConfig__Format_Type :=
  (CSI_RS_Resource_Mobility__slotConfig__ms4__Format, (CSI_RS_Resource_Mobility__slotConfig__ms5__Format, (CSI_RS_Resource_Mobility__slotConfig__ms10__Format, (CSI_RS_Resource_Mobility__slotConfig__ms20__Format, (CSI_RS_Resource_Mobility__slotConfig__ms40__Format, unit__Format))))).
Definition CSI_RS_Resource_Mobility__slotConfig__list__Format := Eval compute in choice_format CSI_RS_Resource_Mobility__slotConfig__list CSI_RS_Resource_Mobility__slotConfig__len_helper1 CSI_RS_Resource_Mobility__slotConfig__len_helper2  CSI_RS_Resource_Mobility__slotConfig__Format_list.
Definition CSI_RS_Resource_Mobility__slotConfig__F1 (z : CSI_RS_Resource_Mobility__slotConfig__Type) : (choice CSI_RS_Resource_Mobility__slotConfig__list) :=
  match z with
   | CSI_RS_Resource_Mobility__slotConfig__ms4 t => existT _ 0 t
  | CSI_RS_Resource_Mobility__slotConfig__ms5 t => existT _ 1 t
  | CSI_RS_Resource_Mobility__slotConfig__ms10 t => existT _ 2 t
  | CSI_RS_Resource_Mobility__slotConfig__ms20 t => existT _ 3 t
  | CSI_RS_Resource_Mobility__slotConfig__ms40 t => existT _ 4 t
  end.
Definition CSI_RS_Resource_Mobility__slotConfig__g := (fun n => typ_set (get_nth_typ CSI_RS_Resource_Mobility__slotConfig__list n)).
Definition CSI_RS_Resource_Mobility__slotConfig__F2 (y : choice CSI_RS_Resource_Mobility__slotConfig__list) : CSI_RS_Resource_Mobility__slotConfig__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_RS_Resource_Mobility__slotConfig__g n -> CSI_RS_Resource_Mobility__slotConfig__Type) with
    | 0 => fun (t : Z) => CSI_RS_Resource_Mobility__slotConfig__ms4 t 
    | 1 => fun (t : Z) => CSI_RS_Resource_Mobility__slotConfig__ms5 t 
    | 2 => fun (t : Z) => CSI_RS_Resource_Mobility__slotConfig__ms10 t 
    | 3 => fun (t : Z) => CSI_RS_Resource_Mobility__slotConfig__ms20 t 
    | 4 => fun (t : Z) => CSI_RS_Resource_Mobility__slotConfig__ms40 t 
 | (S (S (S (S (S n0))))) => (fun (x' : nat) (t'' : CSI_RS_Resource_Mobility__slotConfig__g (S (S (S (S (S x')))))) =>let t' :=
           eq_rect (get_nth_typ CSI_RS_Resource_Mobility__slotConfig__list (S (S (S (S (S x'))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_RS_Resource_Mobility__slotConfig__list (S (S (S (S (S x')))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))) in match t' return CSI_RS_Resource_Mobility__slotConfig__Type with end) n0
           end t0).

Lemma CSI_RS_Resource_Mobility__slotConfig__helper2 :  forall (y : CSI_RS_Resource_Mobility__slotConfig__Type), CSI_RS_Resource_Mobility__slotConfig__cond y -> choice_cond CSI_RS_Resource_Mobility__slotConfig__list (CSI_RS_Resource_Mobility__slotConfig__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_RS_Resource_Mobility__slotConfig__helper3 :  forall (y : CSI_RS_Resource_Mobility__slotConfig__Type), CSI_RS_Resource_Mobility__slotConfig__F2 (CSI_RS_Resource_Mobility__slotConfig__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_RS_Resource_Mobility__slotConfig__helper4 : (forall b : choice CSI_RS_Resource_Mobility__slotConfig__list, choice_cond CSI_RS_Resource_Mobility__slotConfig__list b -> CSI_RS_Resource_Mobility__slotConfig__cond (CSI_RS_Resource_Mobility__slotConfig__F2 b) /\ CSI_RS_Resource_Mobility__slotConfig__F1 (CSI_RS_Resource_Mobility__slotConfig__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_RS_Resource_Mobility__slotConfig__F1 CSI_RS_Resource_Mobility__slotConfig__F2.
Definition CSI_RS_Resource_Mobility__slotConfig__Format : T_Format CSI_RS_Resource_Mobility__slotConfig__Type CSI_RS_Resource_Mobility__slotConfig__cond :=
  (* Eval compute in *) proj2_format CSI_RS_Resource_Mobility__slotConfig__cond CSI_RS_Resource_Mobility__slotConfig__list__Format CSI_RS_Resource_Mobility__slotConfig__F1 CSI_RS_Resource_Mobility__slotConfig__F2 CSI_RS_Resource_Mobility__slotConfig__helper2 CSI_RS_Resource_Mobility__slotConfig__helper3 CSI_RS_Resource_Mobility__slotConfig__helper4.
Opaque CSI_RS_Resource_Mobility__slotConfig__cond CSI_RS_Resource_Mobility__slotConfig__Format.


Definition CSI_RS_Resource_Mobility__associatedSSB__Format_Type := Eval cbn in seq_format_prod CSI_RS_Resource_Mobility__associatedSSB__list.
Definition CSI_RS_Resource_Mobility__associatedSSB__Format_list : CSI_RS_Resource_Mobility__associatedSSB__Format_Type :=
  (SSB_Index__Format, (bool__Format, unit_format)).
Definition CSI_RS_Resource_Mobility__associatedSSB__list__Format := (*Eval compute in *) seq_format CSI_RS_Resource_Mobility__associatedSSB__list CSI_RS_Resource_Mobility__associatedSSB__Format_list.
Definition CSI_RS_Resource_Mobility__associatedSSB__F1 z :=
  (CSI_RS_Resource_Mobility__associatedSSB__ssb_Index z, (CSI_RS_Resource_Mobility__associatedSSB__isQuasiColocated z, tt)).
Definition CSI_RS_Resource_Mobility__associatedSSB__F2 (y : seq_type CSI_RS_Resource_Mobility__associatedSSB__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_RS_Resource_Mobility__associatedSSB__Type i0 i1
  end.
Lemma CSI_RS_Resource_Mobility__associatedSSB__F1F2_cond (z : CSI_RS_Resource_Mobility__associatedSSB__Type)
  : CSI_RS_Resource_Mobility__associatedSSB__cond z ->
  (seq_cond CSI_RS_Resource_Mobility__associatedSSB__list (CSI_RS_Resource_Mobility__associatedSSB__F1 z)).
intro H. unfold CSI_RS_Resource_Mobility__associatedSSB__cond in H. simpl. auto. Qed.
Lemma CSI_RS_Resource_Mobility__associatedSSB__F1F2_cond2 (z : CSI_RS_Resource_Mobility__associatedSSB__Type)
 : CSI_RS_Resource_Mobility__associatedSSB__F2 (CSI_RS_Resource_Mobility__associatedSSB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_RS_Resource_Mobility__associatedSSB__F2F1_cond (y : seq_type CSI_RS_Resource_Mobility__associatedSSB__list)
  : seq_cond CSI_RS_Resource_Mobility__associatedSSB__list y ->
 (CSI_RS_Resource_Mobility__associatedSSB__cond (CSI_RS_Resource_Mobility__associatedSSB__F2 y)) /\  CSI_RS_Resource_Mobility__associatedSSB__F1 (CSI_RS_Resource_Mobility__associatedSSB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_RS_Resource_Mobility__associatedSSB__cond. simpl in *. auto.
 - simpl. unfold CSI_RS_Resource_Mobility__associatedSSB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_RS_Resource_Mobility__associatedSSB__Format : T_Format CSI_RS_Resource_Mobility__associatedSSB__Type CSI_RS_Resource_Mobility__associatedSSB__cond :=
        proj2_format  CSI_RS_Resource_Mobility__associatedSSB__cond CSI_RS_Resource_Mobility__associatedSSB__list__Format
    CSI_RS_Resource_Mobility__associatedSSB__F1 CSI_RS_Resource_Mobility__associatedSSB__F2 CSI_RS_Resource_Mobility__associatedSSB__F1F2_cond  CSI_RS_Resource_Mobility__associatedSSB__F1F2_cond2 CSI_RS_Resource_Mobility__associatedSSB__F2F1_cond.
Opaque CSI_RS_Resource_Mobility__associatedSSB__cond CSI_RS_Resource_Mobility__associatedSSB__Format.

Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Format : T_Format CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Type CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__cond CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Format.

Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Format : T_Format CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Type CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__cond := (* Eval compute in *) bit_string_fixed_format 12.
Opaque CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__cond CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Format.


Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format_Type := Eval cbn in get_formats CSI_RS_Resource_Mobility__frequencyDomainAllocation__list.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format_list : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format_Type :=
  (CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Format, (CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Format, unit__Format)).
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__list__Format := Eval compute in choice_format CSI_RS_Resource_Mobility__frequencyDomainAllocation__list CSI_RS_Resource_Mobility__frequencyDomainAllocation__len_helper1 CSI_RS_Resource_Mobility__frequencyDomainAllocation__len_helper2  CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format_list.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__F1 (z : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type) : (choice CSI_RS_Resource_Mobility__frequencyDomainAllocation__list) :=
  match z with
   | CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1 t => existT _ 0 t
  | CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2 t => existT _ 1 t
  end.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__g := (fun n => typ_set (get_nth_typ CSI_RS_Resource_Mobility__frequencyDomainAllocation__list n)).
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__F2 (y : choice CSI_RS_Resource_Mobility__frequencyDomainAllocation__list) : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_RS_Resource_Mobility__frequencyDomainAllocation__g n -> CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type) with
    | 0 => fun (t : CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1__Type) => CSI_RS_Resource_Mobility__frequencyDomainAllocation__row1 t 
    | 1 => fun (t : CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2__Type) => CSI_RS_Resource_Mobility__frequencyDomainAllocation__row2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CSI_RS_Resource_Mobility__frequencyDomainAllocation__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CSI_RS_Resource_Mobility__frequencyDomainAllocation__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_RS_Resource_Mobility__frequencyDomainAllocation__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type with end) n0
           end t0).

Lemma CSI_RS_Resource_Mobility__frequencyDomainAllocation__helper2 :  forall (y : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type), CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond y -> choice_cond CSI_RS_Resource_Mobility__frequencyDomainAllocation__list (CSI_RS_Resource_Mobility__frequencyDomainAllocation__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_RS_Resource_Mobility__frequencyDomainAllocation__helper3 :  forall (y : CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type), CSI_RS_Resource_Mobility__frequencyDomainAllocation__F2 (CSI_RS_Resource_Mobility__frequencyDomainAllocation__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_RS_Resource_Mobility__frequencyDomainAllocation__helper4 : (forall b : choice CSI_RS_Resource_Mobility__frequencyDomainAllocation__list, choice_cond CSI_RS_Resource_Mobility__frequencyDomainAllocation__list b -> CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond (CSI_RS_Resource_Mobility__frequencyDomainAllocation__F2 b) /\ CSI_RS_Resource_Mobility__frequencyDomainAllocation__F1 (CSI_RS_Resource_Mobility__frequencyDomainAllocation__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_RS_Resource_Mobility__frequencyDomainAllocation__F1 CSI_RS_Resource_Mobility__frequencyDomainAllocation__F2.
Definition CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format : T_Format CSI_RS_Resource_Mobility__frequencyDomainAllocation__Type CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond :=
  (* Eval compute in *) proj2_format CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond CSI_RS_Resource_Mobility__frequencyDomainAllocation__list__Format CSI_RS_Resource_Mobility__frequencyDomainAllocation__F1 CSI_RS_Resource_Mobility__frequencyDomainAllocation__F2 CSI_RS_Resource_Mobility__frequencyDomainAllocation__helper2 CSI_RS_Resource_Mobility__frequencyDomainAllocation__helper3 CSI_RS_Resource_Mobility__frequencyDomainAllocation__helper4.
Opaque CSI_RS_Resource_Mobility__frequencyDomainAllocation__cond CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format.

Definition CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__Format : T_Format Z CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__cond :=
 ranged_int_format (0) (13) CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__helper1 CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__helper2.

Opaque CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__cond CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__Format.

Definition CSI_RS_Resource_Mobility__sequenceGenerationConfig__Format : T_Format Z CSI_RS_Resource_Mobility__sequenceGenerationConfig__cond :=
 ranged_int_format (0) (1023) CSI_RS_Resource_Mobility__sequenceGenerationConfig__helper1 CSI_RS_Resource_Mobility__sequenceGenerationConfig__helper2.

Opaque CSI_RS_Resource_Mobility__sequenceGenerationConfig__cond CSI_RS_Resource_Mobility__sequenceGenerationConfig__Format.

Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__Format : T_Format Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__cond :=
 ranged_int_format (0) (255) CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__helper1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__helper2.

Opaque CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__Format.

Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__Format : T_Format Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__cond :=
 ranged_int_format (0) (319) CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__helper1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__helper2.

Opaque CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__Format.

Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__Format : T_Format Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__cond :=
 ranged_int_format (0) (639) CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__helper1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__helper2.

Opaque CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__Format.

Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__Format : T_Format Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__cond :=
 ranged_int_format (0) (1279) CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__helper1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__helper2.

Opaque CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__Format.

Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__Format : T_Format Z CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__cond :=
 ranged_int_format (0) (2559) CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__helper1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__helper2.

Opaque CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__Format.


Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format_Type := Eval cbn in get_formats CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format_list : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format_Type :=
  (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4__Format, (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5__Format, (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10__Format, (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20__Format, (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40__Format, unit__Format))))).
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list__Format := Eval compute in choice_format CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__len_helper1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__len_helper2  CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format_list.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F1 (z : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type) : (choice CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list) :=
  match z with
   | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4 t => existT _ 0 t
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5 t => existT _ 1 t
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10 t => existT _ 2 t
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20 t => existT _ 3 t
  | CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40 t => existT _ 4 t
  end.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__g := (fun n => typ_set (get_nth_typ CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list n)).
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F2 (y : choice CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list) : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__g n -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type) with
    | 0 => fun (t : Z) => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms4 t 
    | 1 => fun (t : Z) => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms5 t 
    | 2 => fun (t : Z) => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms10 t 
    | 3 => fun (t : Z) => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms20 t 
    | 4 => fun (t : Z) => CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__ms40 t 
 | (S (S (S (S (S n0))))) => (fun (x' : nat) (t'' : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__g (S (S (S (S (S x')))))) =>let t' :=
           eq_rect (get_nth_typ CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list (S (S (S (S (S x'))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list (S (S (S (S (S x')))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))) in match t' return CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type with end) n0
           end t0).

Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__helper2 :  forall (y : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type), CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond y -> choice_cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__helper3 :  forall (y : CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type), CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F2 (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__helper4 : (forall b : choice CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list, choice_cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list b -> CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F2 b) /\ CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F1 (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F2.
Definition CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format : T_Format CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Type CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond :=
  (* Eval compute in *) proj2_format CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__list__Format CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F1 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__F2 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__helper2 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__helper3 CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__helper4.
Opaque CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__cond CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format.


Definition CSI_RS_Resource_Mobility__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_RS_Resource_Mobility__ext0O__list.
Definition CSI_RS_Resource_Mobility__ext0O__Format_list : CSI_RS_Resource_Mobility__ext0O__Format_Type :=
  (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17__Format, unit_format).
Definition CSI_RS_Resource_Mobility__ext0O__list__Format := (*Eval compute in *) seq_format CSI_RS_Resource_Mobility__ext0O__list CSI_RS_Resource_Mobility__ext0O__Format_list.
Definition CSI_RS_Resource_Mobility__ext0O__F1 z :=
  (CSI_RS_Resource_Mobility__ext0O__slotConfig_r17 z, tt).
Definition CSI_RS_Resource_Mobility__ext0O__F2 (y : seq_type CSI_RS_Resource_Mobility__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_RS_Resource_Mobility__ext0O__Type i0
  end.
Lemma CSI_RS_Resource_Mobility__ext0O__F1F2_cond (z : CSI_RS_Resource_Mobility__ext0O__Type)
  : CSI_RS_Resource_Mobility__ext0O__cond z ->
  (seq_cond CSI_RS_Resource_Mobility__ext0O__list (CSI_RS_Resource_Mobility__ext0O__F1 z)).
intro H. unfold CSI_RS_Resource_Mobility__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__F1F2_cond2 (z : CSI_RS_Resource_Mobility__ext0O__Type)
 : CSI_RS_Resource_Mobility__ext0O__F2 (CSI_RS_Resource_Mobility__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_RS_Resource_Mobility__ext0O__F2F1_cond (y : seq_type CSI_RS_Resource_Mobility__ext0O__list)
  : seq_cond CSI_RS_Resource_Mobility__ext0O__list y ->
 (CSI_RS_Resource_Mobility__ext0O__cond (CSI_RS_Resource_Mobility__ext0O__F2 y)) /\  CSI_RS_Resource_Mobility__ext0O__F1 (CSI_RS_Resource_Mobility__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_RS_Resource_Mobility__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_RS_Resource_Mobility__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_RS_Resource_Mobility__ext0O__Format : T_Format CSI_RS_Resource_Mobility__ext0O__Type CSI_RS_Resource_Mobility__ext0O__cond :=
        proj2_format  CSI_RS_Resource_Mobility__ext0O__cond CSI_RS_Resource_Mobility__ext0O__list__Format
    CSI_RS_Resource_Mobility__ext0O__F1 CSI_RS_Resource_Mobility__ext0O__F2 CSI_RS_Resource_Mobility__ext0O__F1F2_cond  CSI_RS_Resource_Mobility__ext0O__F1F2_cond2 CSI_RS_Resource_Mobility__ext0O__F2F1_cond.
Opaque CSI_RS_Resource_Mobility__ext0O__cond CSI_RS_Resource_Mobility__ext0O__Format.

Definition CSI_RS_Resource_Mobility__ext0__check_all_none (b : CSI_RS_Resource_Mobility__ext0O__Type) : bool :=
match b with 
  | make__CSI_RS_Resource_Mobility__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_RS_Resource_Mobility__ext0__Format : T_Format CSI_RS_Resource_Mobility__ext0__Type CSI_RS_Resource_Mobility__ext0__cond :=
  restrict_add_format CSI_RS_Resource_Mobility__ext0__check_all_none CSI_RS_Resource_Mobility__ext0O__Format.

Opaque CSI_RS_Resource_Mobility__ext0__cond CSI_RS_Resource_Mobility__ext0__Format.


Definition CSI_RS_Resource_Mobility__root_Format_Type := Eval cbn in seq_format_prod CSI_RS_Resource_Mobility__root_list.
Definition CSI_RS_Resource_Mobility__root_Format_list : CSI_RS_Resource_Mobility__root_Format_Type :=
  (CSI_RS_Index__Format, (CSI_RS_Resource_Mobility__slotConfig__Format, (CSI_RS_Resource_Mobility__associatedSSB__Format, (CSI_RS_Resource_Mobility__frequencyDomainAllocation__Format, (CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain__Format, (CSI_RS_Resource_Mobility__sequenceGenerationConfig__Format, unit_format)))))).

Definition CSI_RS_Resource_Mobility__ext_Format_Type := Eval cbn in get_formats CSI_RS_Resource_Mobility__ext_list.
Definition CSI_RS_Resource_Mobility__ext_Format_list : CSI_RS_Resource_Mobility__ext_Format_Type :=
  (CSI_RS_Resource_Mobility__ext0__Format, unit__Format).

Definition CSI_RS_Resource_Mobility__list_type : Set := (seq_type CSI_RS_Resource_Mobility__root_list) * (seq_ext_type CSI_RS_Resource_Mobility__ext_list).
Definition CSI_RS_Resource_Mobility__list_cond (z : CSI_RS_Resource_Mobility__list_type) : Prop :=
        (seq_cond CSI_RS_Resource_Mobility__root_list (fst z)) /\ (seq_ext_cond CSI_RS_Resource_Mobility__ext_list (snd z)).
Definition CSI_RS_Resource_Mobility__list_format : T_Format CSI_RS_Resource_Mobility__list_type CSI_RS_Resource_Mobility__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_RS_Resource_Mobility__root_list CSI_RS_Resource_Mobility__root_Format_list CSI_RS_Resource_Mobility__ext_list CSI_RS_Resource_Mobility__ext_Format_list.

Opaque CSI_RS_Resource_Mobility__list_format.
Definition CSI_RS_Resource_Mobility__F1 (z : CSI_RS_Resource_Mobility__Type) : CSI_RS_Resource_Mobility__list_type :=
  (((CSI_RS_Resource_Mobility__csi_RS_Index z, (CSI_RS_Resource_Mobility__slotConfig z, (CSI_RS_Resource_Mobility__associatedSSB z, (CSI_RS_Resource_Mobility__frequencyDomainAllocation z, (CSI_RS_Resource_Mobility__firstOFDMSymbolInTimeDomain z, (CSI_RS_Resource_Mobility__sequenceGenerationConfig z, tt))))))), (
(CSI_RS_Resource_Mobility__ext0 z, tt))).
Definition CSI_RS_Resource_Mobility__F2 (y : CSI_RS_Resource_Mobility__list_type) : CSI_RS_Resource_Mobility__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__CSI_RS_Resource_Mobility__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition CSI_RS_Resource_Mobility__helper1 : (forall a : CSI_RS_Resource_Mobility__Type, CSI_RS_Resource_Mobility__cond a -> CSI_RS_Resource_Mobility__list_cond (CSI_RS_Resource_Mobility__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_RS_Resource_Mobility__helper2 : (forall a : CSI_RS_Resource_Mobility__Type, CSI_RS_Resource_Mobility__F2 (CSI_RS_Resource_Mobility__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_RS_Resource_Mobility__helper3 : (forall b : CSI_RS_Resource_Mobility__list_type, CSI_RS_Resource_Mobility__list_cond b -> CSI_RS_Resource_Mobility__cond (CSI_RS_Resource_Mobility__F2 b) /\ CSI_RS_Resource_Mobility__F1 (CSI_RS_Resource_Mobility__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_RS_Resource_Mobility__cond, CSI_RS_Resource_Mobility__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_RS_Resource_Mobility__Format : T_Format CSI_RS_Resource_Mobility__Type CSI_RS_Resource_Mobility__cond :=
 proj2_format CSI_RS_Resource_Mobility__cond CSI_RS_Resource_Mobility__list_format  CSI_RS_Resource_Mobility__F1 CSI_RS_Resource_Mobility__F2 CSI_RS_Resource_Mobility__helper1 CSI_RS_Resource_Mobility__helper2 CSI_RS_Resource_Mobility__helper3.

Opaque CSI_RS_Resource_Mobility__cond CSI_RS_Resource_Mobility__Format.

