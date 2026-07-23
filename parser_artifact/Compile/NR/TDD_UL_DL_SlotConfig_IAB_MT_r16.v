Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TDD_UL_DL_SlotIndex.

Opaque TDD_UL_DL_SlotIndex__cond TDD_UL_DL_SlotIndex__Format.

Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__helper1 : (1 <= maxNrofSymbols_1)%Z. unfold maxNrofSymbols_1.
 lia. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSymbols_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSymbols_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__Type := Z.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__cond := (fun z => (1 <= z <= maxNrofSymbols_1)%Z).
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__helper1 : (1 <= maxNrofSymbols_1)%Z. unfold maxNrofSymbols_1.
 lia. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSymbols_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSymbols_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__Type := Z.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__cond := (fun z => (1 <= z <= maxNrofSymbols_1)%Z).
Record TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type : Set :=
  make__TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type {
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16 : option Z ;
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16 : option Z ;
}.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list := (
 Opt Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__cond ::
 Opt Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__cond ::
 nil).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond z := 
  opt_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16 z) /\
  opt_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16 z) /\
  True.

Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__helper1 : (1 <= maxNrofSymbols_1)%Z. unfold maxNrofSymbols_1.
 lia. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSymbols_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSymbols_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__Type := Z.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__cond := (fun z => (1 <= z <= maxNrofSymbols_1)%Z).
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__helper1 : (1 <= maxNrofSymbols_1)%Z. unfold maxNrofSymbols_1.
 lia. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSymbols_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSymbols_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__Type := Z.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__cond := (fun z => (1 <= z <= maxNrofSymbols_1)%Z).
Record TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type : Set :=
  make__TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type {
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16 : option Z ;
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16 : option Z ;
}.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list := (
 Opt Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__cond ::
 Opt Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__cond ::
 nil).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond z := 
  opt_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16 z) /\
  opt_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16 z) /\
  True.


Inductive TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type : Set :=
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allDownlink_r16 : unit -> TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allUplink_r16 : unit -> TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16 : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type -> TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16 : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type -> TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type
.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond ::
typ_cons TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond ::
 nil).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond (c : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type) := 
  match c with
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allDownlink_r16 t => (fun _ => True) t 
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allUplink_r16 t => (fun _ => True) t 
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16 t => TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond t 
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16 t => TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond t 
  end.

Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__len_helper1 : to_bit_sz (length TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__len_helper2 : 2 <= length2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list.
 simpl. lia. Qed.
Record TDD_UL_DL_SlotConfig_IAB_MT_r16__Type : Set :=
  make__TDD_UL_DL_SlotConfig_IAB_MT_r16__Type {
    TDD_UL_DL_SlotConfig_IAB_MT_r16__slotIndex_r16 : TDD_UL_DL_SlotIndex__Type ;
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16 : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type ;
}.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__list := (
 Nor TDD_UL_DL_SlotIndex__Type TDD_UL_DL_SlotIndex__cond ::
 Nor TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond ::
 nil).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__cond z := 
  TDD_UL_DL_SlotIndex__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__slotIndex_r16 z) /\
  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16 z) /\
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
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__Format : T_Format Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__cond :=
 ranged_int_format (1) (maxNrofSymbols_1) TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__helper1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__helper2.

Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__Format.

Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__Format : T_Format Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__cond :=
 ranged_int_format (1) (maxNrofSymbols_1) TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__helper1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__helper2.

Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__Format.


Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format_Type := Eval cbn in seq_format_prod TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format_list : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format_Type :=
  (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16__Format, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16__Format, unit_format)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list__Format := (*Eval compute in *) seq_format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format_list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1 z :=
  (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofDownlinkSymbols_r16 z, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__nrofUplinkSymbols_r16 z, tt)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2 (y : seq_type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type i0 i1
  end.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1F2_cond (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type)
  : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond z ->
  (seq_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1 z)).
intro H. unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond in H. simpl. auto. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1F2_cond2 (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type)
 : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2F1_cond (y : seq_type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list)
  : seq_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list y ->
 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2 y)) /\  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond. simpl in *. auto.
 - simpl. unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format : T_Format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond :=
        proj2_format  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__list__Format
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1F2_cond  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F1F2_cond2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__F2F1_cond.
Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format.

Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__Format : T_Format Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__cond :=
 ranged_int_format (1) (maxNrofSymbols_1) TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__helper1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__helper2.

Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__Format.

Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__Format : T_Format Z TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__cond :=
 ranged_int_format (1) (maxNrofSymbols_1) TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__helper1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__helper2.

Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__Format.


Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format_Type := Eval cbn in seq_format_prod TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format_list : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format_Type :=
  (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16__Format, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16__Format, unit_format)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list__Format := (*Eval compute in *) seq_format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format_list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1 z :=
  (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofDownlinkSymbols_r16 z, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__nrofUplinkSymbols_r16 z, tt)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2 (y : seq_type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type i0 i1
  end.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1F2_cond (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type)
  : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond z ->
  (seq_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1 z)).
intro H. unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond in H. simpl. auto. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1F2_cond2 (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type)
 : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2F1_cond (y : seq_type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list)
  : seq_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list y ->
 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2 y)) /\  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond. simpl in *. auto.
 - simpl. unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format : T_Format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond :=
        proj2_format  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__list__Format
    TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1F2_cond  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F1F2_cond2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__F2F1_cond.
Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format.


Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format_Type := Eval cbn in get_formats TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format_list : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format_Type :=
  (unit__Format, (unit__Format, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Format, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Format, unit__Format)))).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list__Format := Eval compute in choice_format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__len_helper1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__len_helper2  TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format_list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F1 (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type) : (choice TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list) :=
  match z with
   | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allDownlink_r16 t => existT _ 0 t
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allUplink_r16 t => existT _ 1 t
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16 t => existT _ 2 t
  | TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16 t => existT _ 3 t
  end.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__g := (fun n => typ_set (get_nth_typ TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list n)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F2 (y : choice TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list) : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__g n -> TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type) with
    | 0 => fun (t : unit) => TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allDownlink_r16 t 
    | 1 => fun (t : unit) => TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__allUplink_r16 t 
    | 2 => fun (t : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16__Type) => TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_r16 t 
    | 3 => fun (t : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16__Type) => TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__explicit_IAB_MT_r16 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type with end) n0
           end t0).

Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__helper2 :  forall (y : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type), TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond y -> choice_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__helper3 :  forall (y : TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type), TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F2 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__helper4 : (forall b : choice TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list, choice_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list b -> TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F2 b) /\ TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F1 (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F2.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format : T_Format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond :=
  (* Eval compute in *) proj2_format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__list__Format TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F1 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__F2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__helper2 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__helper3 TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__helper4.
Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format.


Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__Format_Type := Eval cbn in seq_format_prod TDD_UL_DL_SlotConfig_IAB_MT_r16__list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__Format_list : TDD_UL_DL_SlotConfig_IAB_MT_r16__Format_Type :=
  (TDD_UL_DL_SlotIndex__Format, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16__Format, unit_format)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__list__Format := (*Eval compute in *) seq_format TDD_UL_DL_SlotConfig_IAB_MT_r16__list TDD_UL_DL_SlotConfig_IAB_MT_r16__Format_list.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__F1 z :=
  (TDD_UL_DL_SlotConfig_IAB_MT_r16__slotIndex_r16 z, (TDD_UL_DL_SlotConfig_IAB_MT_r16__symbols_IAB_MT_r16 z, tt)).
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__F2 (y : seq_type TDD_UL_DL_SlotConfig_IAB_MT_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TDD_UL_DL_SlotConfig_IAB_MT_r16__Type i0 i1
  end.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__F1F2_cond (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__Type)
  : TDD_UL_DL_SlotConfig_IAB_MT_r16__cond z ->
  (seq_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__list (TDD_UL_DL_SlotConfig_IAB_MT_r16__F1 z)).
intro H. unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__cond in H. simpl. auto. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__F1F2_cond2 (z : TDD_UL_DL_SlotConfig_IAB_MT_r16__Type)
 : TDD_UL_DL_SlotConfig_IAB_MT_r16__F2 (TDD_UL_DL_SlotConfig_IAB_MT_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TDD_UL_DL_SlotConfig_IAB_MT_r16__F2F1_cond (y : seq_type TDD_UL_DL_SlotConfig_IAB_MT_r16__list)
  : seq_cond TDD_UL_DL_SlotConfig_IAB_MT_r16__list y ->
 (TDD_UL_DL_SlotConfig_IAB_MT_r16__cond (TDD_UL_DL_SlotConfig_IAB_MT_r16__F2 y)) /\  TDD_UL_DL_SlotConfig_IAB_MT_r16__F1 (TDD_UL_DL_SlotConfig_IAB_MT_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__cond. simpl in *. auto.
 - simpl. unfold TDD_UL_DL_SlotConfig_IAB_MT_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TDD_UL_DL_SlotConfig_IAB_MT_r16__Format : T_Format TDD_UL_DL_SlotConfig_IAB_MT_r16__Type TDD_UL_DL_SlotConfig_IAB_MT_r16__cond :=
        proj2_format  TDD_UL_DL_SlotConfig_IAB_MT_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__list__Format
    TDD_UL_DL_SlotConfig_IAB_MT_r16__F1 TDD_UL_DL_SlotConfig_IAB_MT_r16__F2 TDD_UL_DL_SlotConfig_IAB_MT_r16__F1F2_cond  TDD_UL_DL_SlotConfig_IAB_MT_r16__F1F2_cond2 TDD_UL_DL_SlotConfig_IAB_MT_r16__F2F1_cond.
Opaque TDD_UL_DL_SlotConfig_IAB_MT_r16__cond TDD_UL_DL_SlotConfig_IAB_MT_r16__Format.

