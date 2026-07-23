Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SCS_SpecificCarrier__offsetToCarrier__helper1 : (0 <= 2199)%Z.  lia. Qed.
Lemma SCS_SpecificCarrier__offsetToCarrier__helper2 : to_bit_sz (Z.to_nat (2199 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2199 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SCS_SpecificCarrier__offsetToCarrier__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SCS_SpecificCarrier__offsetToCarrier__Type := Z.
Definition SCS_SpecificCarrier__offsetToCarrier__cond := (fun z => (0 <= z <= 2199)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Lemma SCS_SpecificCarrier__carrierBandwidth__helper1 : (1 <= maxNrofPhysicalResourceBlocks)%Z. unfold maxNrofPhysicalResourceBlocks.
 lia. Qed.
Lemma SCS_SpecificCarrier__carrierBandwidth__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SCS_SpecificCarrier__carrierBandwidth__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SCS_SpecificCarrier__carrierBandwidth__Type := Z.
Definition SCS_SpecificCarrier__carrierBandwidth__cond := (fun z => (1 <= z <= maxNrofPhysicalResourceBlocks)%Z).
Lemma SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__helper1 : (0 <= 4095)%Z.  lia. Qed.
Lemma SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__helper2 : to_bit_sz (Z.to_nat (4095 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4095 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__Type := Z.
Definition SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__cond := (fun z => (0 <= z <= 4095)%Z).
Record SCS_SpecificCarrier__ext0O__Type : Set :=
  make__SCS_SpecificCarrier__ext0O__Type {
    SCS_SpecificCarrier__ext0O__txDirectCurrentLocation : option Z ;
}.
Definition SCS_SpecificCarrier__ext0O__list := (
 Opt Z SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__cond ::
 nil).
Definition SCS_SpecificCarrier__ext0O__cond z := 
  opt_cond SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__cond (SCS_SpecificCarrier__ext0O__txDirectCurrentLocation z) /\
  True.

Definition SCS_SpecificCarrier__ext0__Type := SCS_SpecificCarrier__ext0O__Type.
Definition SCS_SpecificCarrier__ext0__cond := SCS_SpecificCarrier__ext0O__cond.

Record SCS_SpecificCarrier__Type : Set :=
  make__SCS_SpecificCarrier__Type {
    SCS_SpecificCarrier__offsetToCarrier : Z ;
    SCS_SpecificCarrier__subcarrierSpacing : SubcarrierSpacing__Type ;
    SCS_SpecificCarrier__carrierBandwidth : Z ;
    SCS_SpecificCarrier__ext0 : option SCS_SpecificCarrier__ext0__Type ;
}.
Definition SCS_SpecificCarrier__root_list : list seq_elem := (
 Nor Z SCS_SpecificCarrier__offsetToCarrier__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor Z SCS_SpecificCarrier__carrierBandwidth__cond ::
 nil).
Definition SCS_SpecificCarrier__ext_list : list typ := (
  typ_cons SCS_SpecificCarrier__ext0__Type SCS_SpecificCarrier__ext0__cond ::
  nil).
Definition SCS_SpecificCarrier__cond (z : SCS_SpecificCarrier__Type) := 
(  SCS_SpecificCarrier__offsetToCarrier__cond (SCS_SpecificCarrier__offsetToCarrier z) /\
  SubcarrierSpacing__cond (SCS_SpecificCarrier__subcarrierSpacing z) /\
  SCS_SpecificCarrier__carrierBandwidth__cond (SCS_SpecificCarrier__carrierBandwidth z) /\
  True) /\ 
(  opt_cond SCS_SpecificCarrier__ext0__cond (SCS_SpecificCarrier__ext0 z) /\
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
Definition SCS_SpecificCarrier__offsetToCarrier__Format : T_Format Z SCS_SpecificCarrier__offsetToCarrier__cond :=
 ranged_int_format (0) (2199) SCS_SpecificCarrier__offsetToCarrier__helper1 SCS_SpecificCarrier__offsetToCarrier__helper2.

Opaque SCS_SpecificCarrier__offsetToCarrier__cond SCS_SpecificCarrier__offsetToCarrier__Format.

Definition SCS_SpecificCarrier__carrierBandwidth__Format : T_Format Z SCS_SpecificCarrier__carrierBandwidth__cond :=
 ranged_int_format (1) (maxNrofPhysicalResourceBlocks) SCS_SpecificCarrier__carrierBandwidth__helper1 SCS_SpecificCarrier__carrierBandwidth__helper2.

Opaque SCS_SpecificCarrier__carrierBandwidth__cond SCS_SpecificCarrier__carrierBandwidth__Format.

Definition SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__Format : T_Format Z SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__cond :=
 ranged_int_format (0) (4095) SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__helper1 SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__helper2.

Opaque SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__cond SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__Format.


Definition SCS_SpecificCarrier__ext0O__Format_Type := Eval cbn in seq_format_prod SCS_SpecificCarrier__ext0O__list.
Definition SCS_SpecificCarrier__ext0O__Format_list : SCS_SpecificCarrier__ext0O__Format_Type :=
  (SCS_SpecificCarrier__ext0O__txDirectCurrentLocation__Format, unit_format).
Definition SCS_SpecificCarrier__ext0O__list__Format := (*Eval compute in *) seq_format SCS_SpecificCarrier__ext0O__list SCS_SpecificCarrier__ext0O__Format_list.
Definition SCS_SpecificCarrier__ext0O__F1 z :=
  (SCS_SpecificCarrier__ext0O__txDirectCurrentLocation z, tt).
Definition SCS_SpecificCarrier__ext0O__F2 (y : seq_type SCS_SpecificCarrier__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SCS_SpecificCarrier__ext0O__Type i0
  end.
Lemma SCS_SpecificCarrier__ext0O__F1F2_cond (z : SCS_SpecificCarrier__ext0O__Type)
  : SCS_SpecificCarrier__ext0O__cond z ->
  (seq_cond SCS_SpecificCarrier__ext0O__list (SCS_SpecificCarrier__ext0O__F1 z)).
intro H. unfold SCS_SpecificCarrier__ext0O__cond in H. simpl. auto. Qed.
Lemma SCS_SpecificCarrier__ext0O__F1F2_cond2 (z : SCS_SpecificCarrier__ext0O__Type)
 : SCS_SpecificCarrier__ext0O__F2 (SCS_SpecificCarrier__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCS_SpecificCarrier__ext0O__F2F1_cond (y : seq_type SCS_SpecificCarrier__ext0O__list)
  : seq_cond SCS_SpecificCarrier__ext0O__list y ->
 (SCS_SpecificCarrier__ext0O__cond (SCS_SpecificCarrier__ext0O__F2 y)) /\  SCS_SpecificCarrier__ext0O__F1 (SCS_SpecificCarrier__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCS_SpecificCarrier__ext0O__cond. simpl in *. auto.
 - simpl. unfold SCS_SpecificCarrier__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCS_SpecificCarrier__ext0O__Format : T_Format SCS_SpecificCarrier__ext0O__Type SCS_SpecificCarrier__ext0O__cond :=
        proj2_format  SCS_SpecificCarrier__ext0O__cond SCS_SpecificCarrier__ext0O__list__Format
    SCS_SpecificCarrier__ext0O__F1 SCS_SpecificCarrier__ext0O__F2 SCS_SpecificCarrier__ext0O__F1F2_cond  SCS_SpecificCarrier__ext0O__F1F2_cond2 SCS_SpecificCarrier__ext0O__F2F1_cond.
Opaque SCS_SpecificCarrier__ext0O__cond SCS_SpecificCarrier__ext0O__Format.

Definition SCS_SpecificCarrier__ext0__check_all_none (b : SCS_SpecificCarrier__ext0O__Type) : bool :=
match b with 
  | make__SCS_SpecificCarrier__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SCS_SpecificCarrier__ext0__Format : T_Format SCS_SpecificCarrier__ext0__Type SCS_SpecificCarrier__ext0__cond :=
  restrict_add_format SCS_SpecificCarrier__ext0__check_all_none SCS_SpecificCarrier__ext0O__Format.

Opaque SCS_SpecificCarrier__ext0__cond SCS_SpecificCarrier__ext0__Format.


Definition SCS_SpecificCarrier__root_Format_Type := Eval cbn in seq_format_prod SCS_SpecificCarrier__root_list.
Definition SCS_SpecificCarrier__root_Format_list : SCS_SpecificCarrier__root_Format_Type :=
  (SCS_SpecificCarrier__offsetToCarrier__Format, (SubcarrierSpacing__Format, (SCS_SpecificCarrier__carrierBandwidth__Format, unit_format))).

Definition SCS_SpecificCarrier__ext_Format_Type := Eval cbn in get_formats SCS_SpecificCarrier__ext_list.
Definition SCS_SpecificCarrier__ext_Format_list : SCS_SpecificCarrier__ext_Format_Type :=
  (SCS_SpecificCarrier__ext0__Format, unit__Format).

Definition SCS_SpecificCarrier__list_type : Set := (seq_type SCS_SpecificCarrier__root_list) * (seq_ext_type SCS_SpecificCarrier__ext_list).
Definition SCS_SpecificCarrier__list_cond (z : SCS_SpecificCarrier__list_type) : Prop :=
        (seq_cond SCS_SpecificCarrier__root_list (fst z)) /\ (seq_ext_cond SCS_SpecificCarrier__ext_list (snd z)).
Definition SCS_SpecificCarrier__list_format : T_Format SCS_SpecificCarrier__list_type SCS_SpecificCarrier__list_cond :=
 (* Eval compute in *) seq_ext_format SCS_SpecificCarrier__root_list SCS_SpecificCarrier__root_Format_list SCS_SpecificCarrier__ext_list SCS_SpecificCarrier__ext_Format_list.

Opaque SCS_SpecificCarrier__list_format.
Definition SCS_SpecificCarrier__F1 (z : SCS_SpecificCarrier__Type) : SCS_SpecificCarrier__list_type :=
  (((SCS_SpecificCarrier__offsetToCarrier z, (SCS_SpecificCarrier__subcarrierSpacing z, (SCS_SpecificCarrier__carrierBandwidth z, tt)))), (
(SCS_SpecificCarrier__ext0 z, tt))).
Definition SCS_SpecificCarrier__F2 (y : SCS_SpecificCarrier__list_type) : SCS_SpecificCarrier__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__SCS_SpecificCarrier__Type j0 j1 j2 i0
  end.
Definition SCS_SpecificCarrier__helper1 : (forall a : SCS_SpecificCarrier__Type, SCS_SpecificCarrier__cond a -> SCS_SpecificCarrier__list_cond (SCS_SpecificCarrier__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SCS_SpecificCarrier__helper2 : (forall a : SCS_SpecificCarrier__Type, SCS_SpecificCarrier__F2 (SCS_SpecificCarrier__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SCS_SpecificCarrier__helper3 : (forall b : SCS_SpecificCarrier__list_type, SCS_SpecificCarrier__list_cond b -> SCS_SpecificCarrier__cond (SCS_SpecificCarrier__F2 b) /\ SCS_SpecificCarrier__F1 (SCS_SpecificCarrier__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SCS_SpecificCarrier__cond, SCS_SpecificCarrier__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SCS_SpecificCarrier__Format : T_Format SCS_SpecificCarrier__Type SCS_SpecificCarrier__cond :=
 proj2_format SCS_SpecificCarrier__cond SCS_SpecificCarrier__list_format  SCS_SpecificCarrier__F1 SCS_SpecificCarrier__F2 SCS_SpecificCarrier__helper1 SCS_SpecificCarrier__helper2 SCS_SpecificCarrier__helper3.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

