Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Definition TCI_ActivatedConfig_r17__pdcch_TCI_r17__Type := list TCI_StateId__Type.

Lemma TCI_ActivatedConfig_r17__pdcch_TCI_r17__helper1 : (0 <= 1 <= 5)%Z.  lia. Qed.
Lemma TCI_ActivatedConfig_r17__pdcch_TCI_r17__helper2 : to_bit_sz (Z.to_nat (5 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TCI_ActivatedConfig_r17__pdcch_TCI_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TCI_ActivatedConfig_r17__pdcch_TCI_r17__cond (z : TCI_ActivatedConfig_r17__pdcch_TCI_r17__Type) :=  (1 <= Z.of_nat (length z) <= 5)%Z /\ (list_and TCI_StateId__cond z) .

Lemma TCI_ActivatedConfig_r17__pdsch_TCI_r17__helper1 : (0 <= 1 <= maxNrofTCI_States)%Z. unfold maxNrofTCI_States.
 lia. Qed.
Lemma TCI_ActivatedConfig_r17__pdsch_TCI_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_States - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_States - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TCI_ActivatedConfig_r17__pdsch_TCI_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TCI_ActivatedConfig_r17__pdsch_TCI_r17__Type := bit_string.
Definition TCI_ActivatedConfig_r17__pdsch_TCI_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= maxNrofTCI_States)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record TCI_ActivatedConfig_r17__Type : Set :=
  make__TCI_ActivatedConfig_r17__Type {
    TCI_ActivatedConfig_r17__pdcch_TCI_r17 : TCI_ActivatedConfig_r17__pdcch_TCI_r17__Type ;
    TCI_ActivatedConfig_r17__pdsch_TCI_r17 : TCI_ActivatedConfig_r17__pdsch_TCI_r17__Type ;
}.
Definition TCI_ActivatedConfig_r17__list := (
 Nor TCI_ActivatedConfig_r17__pdcch_TCI_r17__Type TCI_ActivatedConfig_r17__pdcch_TCI_r17__cond ::
 Nor TCI_ActivatedConfig_r17__pdsch_TCI_r17__Type TCI_ActivatedConfig_r17__pdsch_TCI_r17__cond ::
 nil).
Definition TCI_ActivatedConfig_r17__cond z := 
  TCI_ActivatedConfig_r17__pdcch_TCI_r17__cond (TCI_ActivatedConfig_r17__pdcch_TCI_r17 z) /\
  TCI_ActivatedConfig_r17__pdsch_TCI_r17__cond (TCI_ActivatedConfig_r17__pdsch_TCI_r17 z) /\
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
Definition TCI_ActivatedConfig_r17__pdcch_TCI_r17__Format : T_Format TCI_ActivatedConfig_r17__pdcch_TCI_r17__Type TCI_ActivatedConfig_r17__pdcch_TCI_r17__cond := seq_of_format TCI_StateId__Format 1 5 TCI_ActivatedConfig_r17__pdcch_TCI_r17__helper1 TCI_ActivatedConfig_r17__pdcch_TCI_r17__helper2.

Opaque TCI_ActivatedConfig_r17__pdcch_TCI_r17__cond TCI_ActivatedConfig_r17__pdcch_TCI_r17__Format.

Definition TCI_ActivatedConfig_r17__pdsch_TCI_r17__Format : T_Format TCI_ActivatedConfig_r17__pdsch_TCI_r17__Type TCI_ActivatedConfig_r17__pdsch_TCI_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 maxNrofTCI_States TCI_ActivatedConfig_r17__pdsch_TCI_r17__helper1 TCI_ActivatedConfig_r17__pdsch_TCI_r17__helper2.
Opaque TCI_ActivatedConfig_r17__pdsch_TCI_r17__cond TCI_ActivatedConfig_r17__pdsch_TCI_r17__Format.


Definition TCI_ActivatedConfig_r17__Format_Type := Eval cbn in seq_format_prod TCI_ActivatedConfig_r17__list.
Definition TCI_ActivatedConfig_r17__Format_list : TCI_ActivatedConfig_r17__Format_Type :=
  (TCI_ActivatedConfig_r17__pdcch_TCI_r17__Format, (TCI_ActivatedConfig_r17__pdsch_TCI_r17__Format, unit_format)).
Definition TCI_ActivatedConfig_r17__list__Format := (*Eval compute in *) seq_format TCI_ActivatedConfig_r17__list TCI_ActivatedConfig_r17__Format_list.
Definition TCI_ActivatedConfig_r17__F1 z :=
  (TCI_ActivatedConfig_r17__pdcch_TCI_r17 z, (TCI_ActivatedConfig_r17__pdsch_TCI_r17 z, tt)).
Definition TCI_ActivatedConfig_r17__F2 (y : seq_type TCI_ActivatedConfig_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TCI_ActivatedConfig_r17__Type i0 i1
  end.
Lemma TCI_ActivatedConfig_r17__F1F2_cond (z : TCI_ActivatedConfig_r17__Type)
  : TCI_ActivatedConfig_r17__cond z ->
  (seq_cond TCI_ActivatedConfig_r17__list (TCI_ActivatedConfig_r17__F1 z)).
intro H. unfold TCI_ActivatedConfig_r17__cond in H. simpl. auto. Qed.
Lemma TCI_ActivatedConfig_r17__F1F2_cond2 (z : TCI_ActivatedConfig_r17__Type)
 : TCI_ActivatedConfig_r17__F2 (TCI_ActivatedConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TCI_ActivatedConfig_r17__F2F1_cond (y : seq_type TCI_ActivatedConfig_r17__list)
  : seq_cond TCI_ActivatedConfig_r17__list y ->
 (TCI_ActivatedConfig_r17__cond (TCI_ActivatedConfig_r17__F2 y)) /\  TCI_ActivatedConfig_r17__F1 (TCI_ActivatedConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TCI_ActivatedConfig_r17__cond. simpl in *. auto.
 - simpl. unfold TCI_ActivatedConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TCI_ActivatedConfig_r17__Format : T_Format TCI_ActivatedConfig_r17__Type TCI_ActivatedConfig_r17__cond :=
        proj2_format  TCI_ActivatedConfig_r17__cond TCI_ActivatedConfig_r17__list__Format
    TCI_ActivatedConfig_r17__F1 TCI_ActivatedConfig_r17__F2 TCI_ActivatedConfig_r17__F1F2_cond  TCI_ActivatedConfig_r17__F1F2_cond2 TCI_ActivatedConfig_r17__F2F1_cond.
Opaque TCI_ActivatedConfig_r17__cond TCI_ActivatedConfig_r17__Format.

