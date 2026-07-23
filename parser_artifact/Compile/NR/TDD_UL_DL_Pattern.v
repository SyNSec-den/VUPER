Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Type : Set :=
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p5
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p625
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms1
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms1p25
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms2
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms2p5
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms5
 | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms10
.
Definition TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__cond := (fun (_ : TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Type) => True).
Lemma TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__nat__helper.

Definition TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1 t :=
  match t with
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p5 => 0
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p625 => 1
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms1 => 2
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms1p25 => 3
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms2 => 4
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms2p5 => 5
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms5 => 6
  | TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms10 => 7
  end.
Definition TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F2 n :=
  match n with
  | 0 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p5
  | 1 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p625
  | 2 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms1
  | 3 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms1p25
  | 4 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms2
  | 5 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms2p5
  | 6 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms5
  | 7 => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms10
  | _ => TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__ms0p5
  end.
Lemma TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1F2 : forall x : TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Type, (TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1 x <= 7) /\ TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F2 (TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1 x) = x. imp_solve. Qed.
Lemma TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F2F1 : forall (y : nat) (H : y <= 7), TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1 (TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F2 y) = y. enum_solve H y. Qed.

Lemma TDD_UL_DL_Pattern__nrofDownlinkSlots__helper1 : (0 <= maxNrofSlots)%Z. unfold maxNrofSlots.
 lia. Qed.
Lemma TDD_UL_DL_Pattern__nrofDownlinkSlots__helper2 : to_bit_sz (Z.to_nat (maxNrofSlots - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlots - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_Pattern__nrofDownlinkSlots__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_Pattern__nrofDownlinkSlots__Type := Z.
Definition TDD_UL_DL_Pattern__nrofDownlinkSlots__cond := (fun z => (0 <= z <= maxNrofSlots)%Z).
Lemma TDD_UL_DL_Pattern__nrofDownlinkSymbols__helper1 : (0 <= maxNrofSymbols_1)%Z. unfold maxNrofSymbols_1.
 lia. Qed.
Lemma TDD_UL_DL_Pattern__nrofDownlinkSymbols__helper2 : to_bit_sz (Z.to_nat (maxNrofSymbols_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSymbols_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_Pattern__nrofDownlinkSymbols__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_Pattern__nrofDownlinkSymbols__Type := Z.
Definition TDD_UL_DL_Pattern__nrofDownlinkSymbols__cond := (fun z => (0 <= z <= maxNrofSymbols_1)%Z).
Lemma TDD_UL_DL_Pattern__nrofUplinkSlots__helper1 : (0 <= maxNrofSlots)%Z. unfold maxNrofSlots.
 lia. Qed.
Lemma TDD_UL_DL_Pattern__nrofUplinkSlots__helper2 : to_bit_sz (Z.to_nat (maxNrofSlots - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlots - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_Pattern__nrofUplinkSlots__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_Pattern__nrofUplinkSlots__Type := Z.
Definition TDD_UL_DL_Pattern__nrofUplinkSlots__cond := (fun z => (0 <= z <= maxNrofSlots)%Z).
Lemma TDD_UL_DL_Pattern__nrofUplinkSymbols__helper1 : (0 <= maxNrofSymbols_1)%Z. unfold maxNrofSymbols_1.
 lia. Qed.
Lemma TDD_UL_DL_Pattern__nrofUplinkSymbols__helper2 : to_bit_sz (Z.to_nat (maxNrofSymbols_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSymbols_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_Pattern__nrofUplinkSymbols__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_Pattern__nrofUplinkSymbols__Type := Z.
Definition TDD_UL_DL_Pattern__nrofUplinkSymbols__cond := (fun z => (0 <= z <= maxNrofSymbols_1)%Z).
Inductive TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Type : Set :=
 | TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms3
 | TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms4
.
Definition TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__cond := (fun (_ : TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Type) => True).
Lemma TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__nat__helper.

Definition TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1 t :=
  match t with
  | TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms3 => 0
  | TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms4 => 1
  end.
Definition TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F2 n :=
  match n with
  | 0 => TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms3
  | 1 => TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms4
  | _ => TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__ms3
  end.
Lemma TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1F2 : forall x : TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Type, (TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1 x <= 1) /\ TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F2 (TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1 x) = x. imp_solve. Qed.
Lemma TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F2F1 : forall (y : nat) (H : y <= 1), TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1 (TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F2 y) = y. enum_solve H y. Qed.

Record TDD_UL_DL_Pattern__ext0O__Type : Set :=
  make__TDD_UL_DL_Pattern__ext0O__Type {
    TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530 : option TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Type ;
}.
Definition TDD_UL_DL_Pattern__ext0O__list := (
 Opt TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Type TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__cond ::
 nil).
Definition TDD_UL_DL_Pattern__ext0O__cond z := 
  opt_cond TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__cond (TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530 z) /\
  True.

Definition TDD_UL_DL_Pattern__ext0__Type := TDD_UL_DL_Pattern__ext0O__Type.
Definition TDD_UL_DL_Pattern__ext0__cond := TDD_UL_DL_Pattern__ext0O__cond.

Record TDD_UL_DL_Pattern__Type : Set :=
  make__TDD_UL_DL_Pattern__Type {
    TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity : TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Type ;
    TDD_UL_DL_Pattern__nrofDownlinkSlots : Z ;
    TDD_UL_DL_Pattern__nrofDownlinkSymbols : Z ;
    TDD_UL_DL_Pattern__nrofUplinkSlots : Z ;
    TDD_UL_DL_Pattern__nrofUplinkSymbols : Z ;
    TDD_UL_DL_Pattern__ext0 : option TDD_UL_DL_Pattern__ext0__Type ;
}.
Definition TDD_UL_DL_Pattern__root_list : list seq_elem := (
 Nor TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Type TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__cond ::
 Nor Z TDD_UL_DL_Pattern__nrofDownlinkSlots__cond ::
 Nor Z TDD_UL_DL_Pattern__nrofDownlinkSymbols__cond ::
 Nor Z TDD_UL_DL_Pattern__nrofUplinkSlots__cond ::
 Nor Z TDD_UL_DL_Pattern__nrofUplinkSymbols__cond ::
 nil).
Definition TDD_UL_DL_Pattern__ext_list : list typ := (
  typ_cons TDD_UL_DL_Pattern__ext0__Type TDD_UL_DL_Pattern__ext0__cond ::
  nil).
Definition TDD_UL_DL_Pattern__cond (z : TDD_UL_DL_Pattern__Type) := 
(  TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__cond (TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity z) /\
  TDD_UL_DL_Pattern__nrofDownlinkSlots__cond (TDD_UL_DL_Pattern__nrofDownlinkSlots z) /\
  TDD_UL_DL_Pattern__nrofDownlinkSymbols__cond (TDD_UL_DL_Pattern__nrofDownlinkSymbols z) /\
  TDD_UL_DL_Pattern__nrofUplinkSlots__cond (TDD_UL_DL_Pattern__nrofUplinkSlots z) /\
  TDD_UL_DL_Pattern__nrofUplinkSymbols__cond (TDD_UL_DL_Pattern__nrofUplinkSymbols z) /\
  True) /\ 
(  opt_cond TDD_UL_DL_Pattern__ext0__cond (TDD_UL_DL_Pattern__ext0 z) /\
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
Definition TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Format : T_Format TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__nat__Format TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1 TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F2 TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F1F2 TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__F2F1.

Opaque TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__cond TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Format.

Definition TDD_UL_DL_Pattern__nrofDownlinkSlots__Format : T_Format Z TDD_UL_DL_Pattern__nrofDownlinkSlots__cond :=
 ranged_int_format (0) (maxNrofSlots) TDD_UL_DL_Pattern__nrofDownlinkSlots__helper1 TDD_UL_DL_Pattern__nrofDownlinkSlots__helper2.

Opaque TDD_UL_DL_Pattern__nrofDownlinkSlots__cond TDD_UL_DL_Pattern__nrofDownlinkSlots__Format.

Definition TDD_UL_DL_Pattern__nrofDownlinkSymbols__Format : T_Format Z TDD_UL_DL_Pattern__nrofDownlinkSymbols__cond :=
 ranged_int_format (0) (maxNrofSymbols_1) TDD_UL_DL_Pattern__nrofDownlinkSymbols__helper1 TDD_UL_DL_Pattern__nrofDownlinkSymbols__helper2.

Opaque TDD_UL_DL_Pattern__nrofDownlinkSymbols__cond TDD_UL_DL_Pattern__nrofDownlinkSymbols__Format.

Definition TDD_UL_DL_Pattern__nrofUplinkSlots__Format : T_Format Z TDD_UL_DL_Pattern__nrofUplinkSlots__cond :=
 ranged_int_format (0) (maxNrofSlots) TDD_UL_DL_Pattern__nrofUplinkSlots__helper1 TDD_UL_DL_Pattern__nrofUplinkSlots__helper2.

Opaque TDD_UL_DL_Pattern__nrofUplinkSlots__cond TDD_UL_DL_Pattern__nrofUplinkSlots__Format.

Definition TDD_UL_DL_Pattern__nrofUplinkSymbols__Format : T_Format Z TDD_UL_DL_Pattern__nrofUplinkSymbols__cond :=
 ranged_int_format (0) (maxNrofSymbols_1) TDD_UL_DL_Pattern__nrofUplinkSymbols__helper1 TDD_UL_DL_Pattern__nrofUplinkSymbols__helper2.

Opaque TDD_UL_DL_Pattern__nrofUplinkSymbols__cond TDD_UL_DL_Pattern__nrofUplinkSymbols__Format.

Definition TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Format : T_Format TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__nat__Format TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1 TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F2 TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F1F2 TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__F2F1.

Opaque TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__cond TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Format.


Definition TDD_UL_DL_Pattern__ext0O__Format_Type := Eval cbn in seq_format_prod TDD_UL_DL_Pattern__ext0O__list.
Definition TDD_UL_DL_Pattern__ext0O__Format_list : TDD_UL_DL_Pattern__ext0O__Format_Type :=
  (TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530__Format, unit_format).
Definition TDD_UL_DL_Pattern__ext0O__list__Format := (*Eval compute in *) seq_format TDD_UL_DL_Pattern__ext0O__list TDD_UL_DL_Pattern__ext0O__Format_list.
Definition TDD_UL_DL_Pattern__ext0O__F1 z :=
  (TDD_UL_DL_Pattern__ext0O__dl_UL_TransmissionPeriodicity_v1530 z, tt).
Definition TDD_UL_DL_Pattern__ext0O__F2 (y : seq_type TDD_UL_DL_Pattern__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__TDD_UL_DL_Pattern__ext0O__Type i0
  end.
Lemma TDD_UL_DL_Pattern__ext0O__F1F2_cond (z : TDD_UL_DL_Pattern__ext0O__Type)
  : TDD_UL_DL_Pattern__ext0O__cond z ->
  (seq_cond TDD_UL_DL_Pattern__ext0O__list (TDD_UL_DL_Pattern__ext0O__F1 z)).
intro H. unfold TDD_UL_DL_Pattern__ext0O__cond in H. simpl. auto. Qed.
Lemma TDD_UL_DL_Pattern__ext0O__F1F2_cond2 (z : TDD_UL_DL_Pattern__ext0O__Type)
 : TDD_UL_DL_Pattern__ext0O__F2 (TDD_UL_DL_Pattern__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TDD_UL_DL_Pattern__ext0O__F2F1_cond (y : seq_type TDD_UL_DL_Pattern__ext0O__list)
  : seq_cond TDD_UL_DL_Pattern__ext0O__list y ->
 (TDD_UL_DL_Pattern__ext0O__cond (TDD_UL_DL_Pattern__ext0O__F2 y)) /\  TDD_UL_DL_Pattern__ext0O__F1 (TDD_UL_DL_Pattern__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TDD_UL_DL_Pattern__ext0O__cond. simpl in *. auto.
 - simpl. unfold TDD_UL_DL_Pattern__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TDD_UL_DL_Pattern__ext0O__Format : T_Format TDD_UL_DL_Pattern__ext0O__Type TDD_UL_DL_Pattern__ext0O__cond :=
        proj2_format  TDD_UL_DL_Pattern__ext0O__cond TDD_UL_DL_Pattern__ext0O__list__Format
    TDD_UL_DL_Pattern__ext0O__F1 TDD_UL_DL_Pattern__ext0O__F2 TDD_UL_DL_Pattern__ext0O__F1F2_cond  TDD_UL_DL_Pattern__ext0O__F1F2_cond2 TDD_UL_DL_Pattern__ext0O__F2F1_cond.
Opaque TDD_UL_DL_Pattern__ext0O__cond TDD_UL_DL_Pattern__ext0O__Format.

Definition TDD_UL_DL_Pattern__ext0__check_all_none (b : TDD_UL_DL_Pattern__ext0O__Type) : bool :=
match b with 
  | make__TDD_UL_DL_Pattern__ext0O__Type None  => false 
  | _ => true 
 end.
Definition TDD_UL_DL_Pattern__ext0__Format : T_Format TDD_UL_DL_Pattern__ext0__Type TDD_UL_DL_Pattern__ext0__cond :=
  restrict_add_format TDD_UL_DL_Pattern__ext0__check_all_none TDD_UL_DL_Pattern__ext0O__Format.

Opaque TDD_UL_DL_Pattern__ext0__cond TDD_UL_DL_Pattern__ext0__Format.


Definition TDD_UL_DL_Pattern__root_Format_Type := Eval cbn in seq_format_prod TDD_UL_DL_Pattern__root_list.
Definition TDD_UL_DL_Pattern__root_Format_list : TDD_UL_DL_Pattern__root_Format_Type :=
  (TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity__Format, (TDD_UL_DL_Pattern__nrofDownlinkSlots__Format, (TDD_UL_DL_Pattern__nrofDownlinkSymbols__Format, (TDD_UL_DL_Pattern__nrofUplinkSlots__Format, (TDD_UL_DL_Pattern__nrofUplinkSymbols__Format, unit_format))))).

Definition TDD_UL_DL_Pattern__ext_Format_Type := Eval cbn in get_formats TDD_UL_DL_Pattern__ext_list.
Definition TDD_UL_DL_Pattern__ext_Format_list : TDD_UL_DL_Pattern__ext_Format_Type :=
  (TDD_UL_DL_Pattern__ext0__Format, unit__Format).

Definition TDD_UL_DL_Pattern__list_type : Set := (seq_type TDD_UL_DL_Pattern__root_list) * (seq_ext_type TDD_UL_DL_Pattern__ext_list).
Definition TDD_UL_DL_Pattern__list_cond (z : TDD_UL_DL_Pattern__list_type) : Prop :=
        (seq_cond TDD_UL_DL_Pattern__root_list (fst z)) /\ (seq_ext_cond TDD_UL_DL_Pattern__ext_list (snd z)).
Definition TDD_UL_DL_Pattern__list_format : T_Format TDD_UL_DL_Pattern__list_type TDD_UL_DL_Pattern__list_cond :=
 (* Eval compute in *) seq_ext_format TDD_UL_DL_Pattern__root_list TDD_UL_DL_Pattern__root_Format_list TDD_UL_DL_Pattern__ext_list TDD_UL_DL_Pattern__ext_Format_list.

Opaque TDD_UL_DL_Pattern__list_format.
Definition TDD_UL_DL_Pattern__F1 (z : TDD_UL_DL_Pattern__Type) : TDD_UL_DL_Pattern__list_type :=
  (((TDD_UL_DL_Pattern__dl_UL_TransmissionPeriodicity z, (TDD_UL_DL_Pattern__nrofDownlinkSlots z, (TDD_UL_DL_Pattern__nrofDownlinkSymbols z, (TDD_UL_DL_Pattern__nrofUplinkSlots z, (TDD_UL_DL_Pattern__nrofUplinkSymbols z, tt)))))), (
(TDD_UL_DL_Pattern__ext0 z, tt))).
Definition TDD_UL_DL_Pattern__F2 (y : TDD_UL_DL_Pattern__list_type) : TDD_UL_DL_Pattern__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__TDD_UL_DL_Pattern__Type j0 j1 j2 j3 j4 i0
  end.
Definition TDD_UL_DL_Pattern__helper1 : (forall a : TDD_UL_DL_Pattern__Type, TDD_UL_DL_Pattern__cond a -> TDD_UL_DL_Pattern__list_cond (TDD_UL_DL_Pattern__F1 a)).
                     intros. destruct a. auto. Qed.
Definition TDD_UL_DL_Pattern__helper2 : (forall a : TDD_UL_DL_Pattern__Type, TDD_UL_DL_Pattern__F2 (TDD_UL_DL_Pattern__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition TDD_UL_DL_Pattern__helper3 : (forall b : TDD_UL_DL_Pattern__list_type, TDD_UL_DL_Pattern__list_cond b -> TDD_UL_DL_Pattern__cond (TDD_UL_DL_Pattern__F2 b) /\ TDD_UL_DL_Pattern__F1 (TDD_UL_DL_Pattern__F2 b) = b).
                     intros. destruct b as [y y1]. unfold TDD_UL_DL_Pattern__cond, TDD_UL_DL_Pattern__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition TDD_UL_DL_Pattern__Format : T_Format TDD_UL_DL_Pattern__Type TDD_UL_DL_Pattern__cond :=
 proj2_format TDD_UL_DL_Pattern__cond TDD_UL_DL_Pattern__list_format  TDD_UL_DL_Pattern__F1 TDD_UL_DL_Pattern__F2 TDD_UL_DL_Pattern__helper1 TDD_UL_DL_Pattern__helper2 TDD_UL_DL_Pattern__helper3.

Opaque TDD_UL_DL_Pattern__cond TDD_UL_DL_Pattern__Format.

