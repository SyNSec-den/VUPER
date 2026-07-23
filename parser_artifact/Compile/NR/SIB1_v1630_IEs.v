Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UAC_AC1_SelectAssistInfo_r16.

Opaque UAC_AC1_SelectAssistInfo_r16__cond UAC_AC1_SelectAssistInfo_r16__Format.

Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Type := list UAC_AC1_SelectAssistInfo_r16__Type.

Lemma SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__helper1 : (0 <= 2 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__cond (z : SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Type) :=  (2 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and UAC_AC1_SelectAssistInfo_r16__cond z) .

Record SIB1_v1630_IEs__uac_BarringInfo_v1630__Type : Set :=
  make__SIB1_v1630_IEs__uac_BarringInfo_v1630__Type {
    SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16 : SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Type ;
}.
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__list := (
 Nor SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Type SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__cond ::
 nil).
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__cond z := 
  SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__cond (SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16 z) /\
  True.

Require Import NR.SIB1_v1700_IEs.

Opaque SIB1_v1700_IEs__cond SIB1_v1700_IEs__Format.

Record SIB1_v1630_IEs__Type : Set :=
  make__SIB1_v1630_IEs__Type {
    SIB1_v1630_IEs__uac_BarringInfo_v1630 : option SIB1_v1630_IEs__uac_BarringInfo_v1630__Type ;
    SIB1_v1630_IEs__nonCriticalExtension : option SIB1_v1700_IEs__Type ;
}.
Definition SIB1_v1630_IEs__list := (
 Opt SIB1_v1630_IEs__uac_BarringInfo_v1630__Type SIB1_v1630_IEs__uac_BarringInfo_v1630__cond ::
 Opt SIB1_v1700_IEs__Type SIB1_v1700_IEs__cond ::
 nil).
Definition SIB1_v1630_IEs__cond z := 
  opt_cond SIB1_v1630_IEs__uac_BarringInfo_v1630__cond (SIB1_v1630_IEs__uac_BarringInfo_v1630 z) /\
  opt_cond SIB1_v1700_IEs__cond (SIB1_v1630_IEs__nonCriticalExtension z) /\
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
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Format : T_Format SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Type SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__cond := seq_of_format UAC_AC1_SelectAssistInfo_r16__Format 2 maxPLMN SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__helper1 SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__helper2.

Opaque SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__cond SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Format.


Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__Format_Type := Eval cbn in seq_format_prod SIB1_v1630_IEs__uac_BarringInfo_v1630__list.
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__Format_list : SIB1_v1630_IEs__uac_BarringInfo_v1630__Format_Type :=
  (SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16__Format, unit_format).
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__list__Format := (*Eval compute in *) seq_format SIB1_v1630_IEs__uac_BarringInfo_v1630__list SIB1_v1630_IEs__uac_BarringInfo_v1630__Format_list.
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__F1 z :=
  (SIB1_v1630_IEs__uac_BarringInfo_v1630__uac_AC1_SelectAssistInfo_r16 z, tt).
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__F2 (y : seq_type SIB1_v1630_IEs__uac_BarringInfo_v1630__list) :=
  match y with
  | (i0, _)=>
    make__SIB1_v1630_IEs__uac_BarringInfo_v1630__Type i0
  end.
Lemma SIB1_v1630_IEs__uac_BarringInfo_v1630__F1F2_cond (z : SIB1_v1630_IEs__uac_BarringInfo_v1630__Type)
  : SIB1_v1630_IEs__uac_BarringInfo_v1630__cond z ->
  (seq_cond SIB1_v1630_IEs__uac_BarringInfo_v1630__list (SIB1_v1630_IEs__uac_BarringInfo_v1630__F1 z)).
intro H. unfold SIB1_v1630_IEs__uac_BarringInfo_v1630__cond in H. simpl. auto. Qed.
Lemma SIB1_v1630_IEs__uac_BarringInfo_v1630__F1F2_cond2 (z : SIB1_v1630_IEs__uac_BarringInfo_v1630__Type)
 : SIB1_v1630_IEs__uac_BarringInfo_v1630__F2 (SIB1_v1630_IEs__uac_BarringInfo_v1630__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1_v1630_IEs__uac_BarringInfo_v1630__F2F1_cond (y : seq_type SIB1_v1630_IEs__uac_BarringInfo_v1630__list)
  : seq_cond SIB1_v1630_IEs__uac_BarringInfo_v1630__list y ->
 (SIB1_v1630_IEs__uac_BarringInfo_v1630__cond (SIB1_v1630_IEs__uac_BarringInfo_v1630__F2 y)) /\  SIB1_v1630_IEs__uac_BarringInfo_v1630__F1 (SIB1_v1630_IEs__uac_BarringInfo_v1630__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1_v1630_IEs__uac_BarringInfo_v1630__cond. simpl in *. auto.
 - simpl. unfold SIB1_v1630_IEs__uac_BarringInfo_v1630__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1_v1630_IEs__uac_BarringInfo_v1630__Format : T_Format SIB1_v1630_IEs__uac_BarringInfo_v1630__Type SIB1_v1630_IEs__uac_BarringInfo_v1630__cond :=
        proj2_format  SIB1_v1630_IEs__uac_BarringInfo_v1630__cond SIB1_v1630_IEs__uac_BarringInfo_v1630__list__Format
    SIB1_v1630_IEs__uac_BarringInfo_v1630__F1 SIB1_v1630_IEs__uac_BarringInfo_v1630__F2 SIB1_v1630_IEs__uac_BarringInfo_v1630__F1F2_cond  SIB1_v1630_IEs__uac_BarringInfo_v1630__F1F2_cond2 SIB1_v1630_IEs__uac_BarringInfo_v1630__F2F1_cond.
Opaque SIB1_v1630_IEs__uac_BarringInfo_v1630__cond SIB1_v1630_IEs__uac_BarringInfo_v1630__Format.


Definition SIB1_v1630_IEs__Format_Type := Eval cbn in seq_format_prod SIB1_v1630_IEs__list.
Definition SIB1_v1630_IEs__Format_list : SIB1_v1630_IEs__Format_Type :=
  (SIB1_v1630_IEs__uac_BarringInfo_v1630__Format, (SIB1_v1700_IEs__Format, unit_format)).
Definition SIB1_v1630_IEs__list__Format := (*Eval compute in *) seq_format SIB1_v1630_IEs__list SIB1_v1630_IEs__Format_list.
Definition SIB1_v1630_IEs__F1 z :=
  (SIB1_v1630_IEs__uac_BarringInfo_v1630 z, (SIB1_v1630_IEs__nonCriticalExtension z, tt)).
Definition SIB1_v1630_IEs__F2 (y : seq_type SIB1_v1630_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB1_v1630_IEs__Type i0 i1
  end.
Lemma SIB1_v1630_IEs__F1F2_cond (z : SIB1_v1630_IEs__Type)
  : SIB1_v1630_IEs__cond z ->
  (seq_cond SIB1_v1630_IEs__list (SIB1_v1630_IEs__F1 z)).
intro H. unfold SIB1_v1630_IEs__cond in H. simpl. auto. Qed.
Lemma SIB1_v1630_IEs__F1F2_cond2 (z : SIB1_v1630_IEs__Type)
 : SIB1_v1630_IEs__F2 (SIB1_v1630_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1_v1630_IEs__F2F1_cond (y : seq_type SIB1_v1630_IEs__list)
  : seq_cond SIB1_v1630_IEs__list y ->
 (SIB1_v1630_IEs__cond (SIB1_v1630_IEs__F2 y)) /\  SIB1_v1630_IEs__F1 (SIB1_v1630_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1_v1630_IEs__cond. simpl in *. auto.
 - simpl. unfold SIB1_v1630_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1_v1630_IEs__Format : T_Format SIB1_v1630_IEs__Type SIB1_v1630_IEs__cond :=
        proj2_format  SIB1_v1630_IEs__cond SIB1_v1630_IEs__list__Format
    SIB1_v1630_IEs__F1 SIB1_v1630_IEs__F2 SIB1_v1630_IEs__F1F2_cond  SIB1_v1630_IEs__F1F2_cond2 SIB1_v1630_IEs__F2F1_cond.
Opaque SIB1_v1630_IEs__cond SIB1_v1630_IEs__Format.

