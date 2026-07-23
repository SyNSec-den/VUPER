Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SL_PQI_r16__sl_StandardizedPQI_r16__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma SL_PQI_r16__sl_StandardizedPQI_r16__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PQI_r16__sl_StandardizedPQI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PQI_r16__sl_StandardizedPQI_r16__Type := Z.
Definition SL_PQI_r16__sl_StandardizedPQI_r16__cond := (fun z => (0 <= z <= 255)%Z).
Inductive SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type : Set :=
 | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__gbr
 | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__non_GBR
 | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__delayCriticalGBR
 | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__spare1
.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__cond := (fun (_ : SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type) => True).
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__nat__helper.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1 t :=
  match t with
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__gbr => 0
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__non_GBR => 1
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__delayCriticalGBR => 2
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__spare1 => 3
  end.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2 n :=
  match n with
  | 0 => SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__gbr
  | 1 => SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__non_GBR
  | 2 => SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__delayCriticalGBR
  | 3 => SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__spare1
  | _ => SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__gbr
  end.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1F2 : forall x : SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1 x <= 3) /\ SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2 (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2F1 : forall (y : nat) (H : y <= 3), SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1 (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__Type := Z.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__cond := (fun z => (1 <= z <= 8)%Z).
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__Type := Z.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__Type := Z.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__cond := (fun z => (0 <= z <= 9)%Z).
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__helper1 : (0 <= 4095)%Z.  lia. Qed.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__helper2 : to_bit_sz (Z.to_nat (4095 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4095 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__Type := Z.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__cond := (fun z => (0 <= z <= 4095)%Z).
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__helper1 : (0 <= 4095)%Z.  lia. Qed.
Lemma SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__helper2 : to_bit_sz (Z.to_nat (4095 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4095 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__Type := Z.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__cond := (fun z => (0 <= z <= 4095)%Z).
Record SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type : Set :=
  make__SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type {
    SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16 : option SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type ;
    SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16 : option Z ;
    SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16 : option Z ;
    SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16 : option Z ;
    SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16 : option Z ;
    SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16 : option Z ;
}.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_list : list seq_elem := (
 Opt SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__cond ::
 Opt Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__cond ::
 Opt Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__cond ::
 Opt Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__cond ::
 Opt Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__cond ::
 Opt Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__cond ::
 nil).
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_list : list typ := (
  nil).
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond (z : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type) := 
(  opt_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16 z) /\
  opt_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16 z) /\
  opt_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16 z) /\
  opt_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16 z) /\
  opt_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16 z) /\
  opt_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16 z) /\
  True) /\ 
(  True).


Inductive SL_PQI_r16__Type : Set :=
  | SL_PQI_r16__sl_StandardizedPQI_r16 : Z -> SL_PQI_r16__Type
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16 : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type -> SL_PQI_r16__Type
.
Definition SL_PQI_r16__list : list typ := (
typ_cons Z SL_PQI_r16__sl_StandardizedPQI_r16__cond ::
typ_cons SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond ::
 nil).
Definition SL_PQI_r16__cond (c : SL_PQI_r16__Type) := 
  match c with
  | SL_PQI_r16__sl_StandardizedPQI_r16 t => SL_PQI_r16__sl_StandardizedPQI_r16__cond t 
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16 t => SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond t 
  end.

Lemma SL_PQI_r16__len_helper1 : to_bit_sz (length SL_PQI_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_PQI_r16__len_helper2 : 2 <= length2 SL_PQI_r16__list.
 simpl. lia. Qed.

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
Definition SL_PQI_r16__sl_StandardizedPQI_r16__Format : T_Format Z SL_PQI_r16__sl_StandardizedPQI_r16__cond :=
 ranged_int_format (0) (255) SL_PQI_r16__sl_StandardizedPQI_r16__helper1 SL_PQI_r16__sl_StandardizedPQI_r16__helper2.

Opaque SL_PQI_r16__sl_StandardizedPQI_r16__cond SL_PQI_r16__sl_StandardizedPQI_r16__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Format : T_Format SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__nat__Format SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1F2 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2F1.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__Format : T_Format Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__cond :=
 ranged_int_format (1) (8) SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__helper1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__helper2.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__Format : T_Format Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__cond :=
 ranged_int_format (0) (1023) SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__helper1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__helper2.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__Format : T_Format Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__cond :=
 ranged_int_format (0) (9) SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__helper1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__helper2.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__Format : T_Format Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__cond :=
 ranged_int_format (0) (4095) SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__helper1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__helper2.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__Format : T_Format Z SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__cond :=
 ranged_int_format (0) (4095) SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__helper1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__helper2.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__Format.


Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_Type := Eval cbn in seq_format_prod SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_list.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_list : SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_Type :=
  (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Format, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__Format, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__Format, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__Format, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__Format, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__Format, unit_format)))))).

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_Type := Eval cbn in get_formats SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_list.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_list : SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_Type :=
  unit__Format.

Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type : Set := (seq_type SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_list) * (seq_ext_type SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_list).
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_cond (z : SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type) : Prop :=
        (seq_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_list (fst z)) /\ (seq_ext_cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_list (snd z)).
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_format : T_Format SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_list SL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_list SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_list SL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_list.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_format.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__F1 (z : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type) : SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type :=
  (((SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16 z, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16 z, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16 z, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16 z, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16 z, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16 z, tt))))))), (
tt)).
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__F2 (y : SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type) : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type j0 j1 j2 j3 j4 j5
  end.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__helper1 : (forall a : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type, SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond a -> SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__helper2 : (forall a : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type, SL_PQI_r16__sl_Non_StandardizedPQI_r16__F2 (SL_PQI_r16__sl_Non_StandardizedPQI_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__helper3 : (forall b : SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type, SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_cond b -> SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond (SL_PQI_r16__sl_Non_StandardizedPQI_r16__F2 b) /\ SL_PQI_r16__sl_Non_StandardizedPQI_r16__F1 (SL_PQI_r16__sl_Non_StandardizedPQI_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond, SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_PQI_r16__sl_Non_StandardizedPQI_r16__Format : T_Format SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond :=
 proj2_format SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__list_format  SL_PQI_r16__sl_Non_StandardizedPQI_r16__F1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__F2 SL_PQI_r16__sl_Non_StandardizedPQI_r16__helper1 SL_PQI_r16__sl_Non_StandardizedPQI_r16__helper2 SL_PQI_r16__sl_Non_StandardizedPQI_r16__helper3.

Opaque SL_PQI_r16__sl_Non_StandardizedPQI_r16__cond SL_PQI_r16__sl_Non_StandardizedPQI_r16__Format.


Definition SL_PQI_r16__Format_Type := Eval cbn in get_formats SL_PQI_r16__list.
Definition SL_PQI_r16__Format_list : SL_PQI_r16__Format_Type :=
  (SL_PQI_r16__sl_StandardizedPQI_r16__Format, (SL_PQI_r16__sl_Non_StandardizedPQI_r16__Format, unit__Format)).
Definition SL_PQI_r16__list__Format := Eval compute in choice_format SL_PQI_r16__list SL_PQI_r16__len_helper1 SL_PQI_r16__len_helper2  SL_PQI_r16__Format_list.
Definition SL_PQI_r16__F1 (z : SL_PQI_r16__Type) : (choice SL_PQI_r16__list) :=
  match z with
   | SL_PQI_r16__sl_StandardizedPQI_r16 t => existT _ 0 t
  | SL_PQI_r16__sl_Non_StandardizedPQI_r16 t => existT _ 1 t
  end.
Definition SL_PQI_r16__g := (fun n => typ_set (get_nth_typ SL_PQI_r16__list n)).
Definition SL_PQI_r16__F2 (y : choice SL_PQI_r16__list) : SL_PQI_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_PQI_r16__g n -> SL_PQI_r16__Type) with
    | 0 => fun (t : Z) => SL_PQI_r16__sl_StandardizedPQI_r16 t 
    | 1 => fun (t : SL_PQI_r16__sl_Non_StandardizedPQI_r16__Type) => SL_PQI_r16__sl_Non_StandardizedPQI_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_PQI_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_PQI_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_PQI_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_PQI_r16__Type with end) n0
           end t0).

Lemma SL_PQI_r16__helper2 :  forall (y : SL_PQI_r16__Type), SL_PQI_r16__cond y -> choice_cond SL_PQI_r16__list (SL_PQI_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_PQI_r16__helper3 :  forall (y : SL_PQI_r16__Type), SL_PQI_r16__F2 (SL_PQI_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_PQI_r16__helper4 : (forall b : choice SL_PQI_r16__list, choice_cond SL_PQI_r16__list b -> SL_PQI_r16__cond (SL_PQI_r16__F2 b) /\ SL_PQI_r16__F1 (SL_PQI_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_PQI_r16__F1 SL_PQI_r16__F2.
Definition SL_PQI_r16__Format : T_Format SL_PQI_r16__Type SL_PQI_r16__cond :=
  (* Eval compute in *) proj2_format SL_PQI_r16__cond SL_PQI_r16__list__Format SL_PQI_r16__F1 SL_PQI_r16__F2 SL_PQI_r16__helper2 SL_PQI_r16__helper3 SL_PQI_r16__helper4.
Opaque SL_PQI_r16__cond SL_PQI_r16__Format.

