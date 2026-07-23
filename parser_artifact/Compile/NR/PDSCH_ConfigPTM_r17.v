Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__Type := Z.
Definition PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__Type := Z.
Definition PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__cond := (fun z => (0 <= z <= 65535)%Z).
Inductive PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Type : Set :=
 | PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n2
 | PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n4
 | PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n8
.
Definition PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__cond := (fun (_ : PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Type) => True).
Lemma PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__nat__helper.

Definition PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1 t :=
  match t with
  | PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n2 => 0
  | PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n4 => 1
  | PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n8 => 2
  end.
Definition PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F2 n :=
  match n with
  | 0 => PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n2
  | 1 => PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n4
  | 2 => PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n8
  | _ => PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__n2
  end.
Lemma PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1F2 : forall x : PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Type, (PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1 x <= 2) /\ PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F2 (PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F2F1 : forall (y : nat) (H : y <= 2), PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1 (PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_ConfigPTM_r17__Type : Set :=
  make__PDSCH_ConfigPTM_r17__Type {
    PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17 : option Z ;
    PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17 : option Z ;
    PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17 : option PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Type ;
}.
Definition PDSCH_ConfigPTM_r17__list := (
 Opt Z PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__cond ::
 Opt Z PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__cond ::
 Opt PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Type PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__cond ::
 nil).
Definition PDSCH_ConfigPTM_r17__cond z := 
  opt_cond PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__cond (PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17 z) /\
  opt_cond PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__cond (PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17 z) /\
  opt_cond PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__cond (PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17 z) /\
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
Definition PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__Format : T_Format Z PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__cond :=
 ranged_int_format (0) (1023) PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__helper1 PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__helper2.

Opaque PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__cond PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__Format.

Definition PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__Format : T_Format Z PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__cond :=
 ranged_int_format (0) (65535) PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__helper1 PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__helper2.

Opaque PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__cond PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__Format.

Definition PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Format : T_Format PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__nat__Format PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1 PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F2 PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F1F2 PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__F2F1.

Opaque PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__cond PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Format.


Definition PDSCH_ConfigPTM_r17__Format_Type := Eval cbn in seq_format_prod PDSCH_ConfigPTM_r17__list.
Definition PDSCH_ConfigPTM_r17__Format_list : PDSCH_ConfigPTM_r17__Format_Type :=
  (PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17__Format, (PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17__Format, (PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17__Format, unit_format))).
Definition PDSCH_ConfigPTM_r17__list__Format := (*Eval compute in *) seq_format PDSCH_ConfigPTM_r17__list PDSCH_ConfigPTM_r17__Format_list.
Definition PDSCH_ConfigPTM_r17__F1 z :=
  (PDSCH_ConfigPTM_r17__dataScramblingIdentityPDSCH_r17 z, (PDSCH_ConfigPTM_r17__dmrs_ScramblingID0_r17 z, (PDSCH_ConfigPTM_r17__pdsch_AggregationFactor_r17 z, tt))).
Definition PDSCH_ConfigPTM_r17__F2 (y : seq_type PDSCH_ConfigPTM_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDSCH_ConfigPTM_r17__Type i0 i1 i2
  end.
Lemma PDSCH_ConfigPTM_r17__F1F2_cond (z : PDSCH_ConfigPTM_r17__Type)
  : PDSCH_ConfigPTM_r17__cond z ->
  (seq_cond PDSCH_ConfigPTM_r17__list (PDSCH_ConfigPTM_r17__F1 z)).
intro H. unfold PDSCH_ConfigPTM_r17__cond in H. simpl. auto. Qed.
Lemma PDSCH_ConfigPTM_r17__F1F2_cond2 (z : PDSCH_ConfigPTM_r17__Type)
 : PDSCH_ConfigPTM_r17__F2 (PDSCH_ConfigPTM_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_ConfigPTM_r17__F2F1_cond (y : seq_type PDSCH_ConfigPTM_r17__list)
  : seq_cond PDSCH_ConfigPTM_r17__list y ->
 (PDSCH_ConfigPTM_r17__cond (PDSCH_ConfigPTM_r17__F2 y)) /\  PDSCH_ConfigPTM_r17__F1 (PDSCH_ConfigPTM_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_ConfigPTM_r17__cond. simpl in *. auto.
 - simpl. unfold PDSCH_ConfigPTM_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_ConfigPTM_r17__Format : T_Format PDSCH_ConfigPTM_r17__Type PDSCH_ConfigPTM_r17__cond :=
        proj2_format  PDSCH_ConfigPTM_r17__cond PDSCH_ConfigPTM_r17__list__Format
    PDSCH_ConfigPTM_r17__F1 PDSCH_ConfigPTM_r17__F2 PDSCH_ConfigPTM_r17__F1F2_cond  PDSCH_ConfigPTM_r17__F1F2_cond2 PDSCH_ConfigPTM_r17__F2F1_cond.
Opaque PDSCH_ConfigPTM_r17__cond PDSCH_ConfigPTM_r17__Format.

