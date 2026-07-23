Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Type : Set :=
 | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl0
 | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl1
 | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl2
 | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl4
.
Definition SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__cond := (fun (_ : SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Type) => True).
Lemma SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__nat__helper.

Definition SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1 t :=
  match t with
  | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl0 => 0
  | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl1 => 1
  | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl2 => 2
  | SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl4 => 3
  end.
Definition SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F2 n :=
  match n with
  | 0 => SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl0
  | 1 => SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl1
  | 2 => SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl2
  | 3 => SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl4
  | _ => SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__sl0
  end.
Lemma SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1F2 : forall x : SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Type, (SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1 x <= 3) /\ SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F2 (SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F2F1 : forall (y : nat) (H : y <= 3), SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1 (SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__helper1 : (0 <= 10 <= 275)%Z.  lia. Qed.
Lemma SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__helper2 : to_bit_sz (Z.to_nat (275 - 10)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (275 - 10))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Type := bit_string.
Definition SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__cond := (fun z : bit_string => (10 <= Z.of_nat (fst z) <= 275)%Z /\ bit_string_len_prop (fst z) (snd z)).
Inductive SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Type : Set :=
 | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n1
 | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n2
 | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n3
 | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n6
.
Definition SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__cond := (fun (_ : SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Type) => True).
Lemma SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__nat__helper.

Definition SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1 t :=
  match t with
  | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n1 => 0
  | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n2 => 1
  | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n3 => 2
  | SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n6 => 3
  end.
Definition SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F2 n :=
  match n with
  | 0 => SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n1
  | 1 => SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n2
  | 2 => SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n3
  | 3 => SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n6
  | _ => SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__n1
  end.
Lemma SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1F2 : forall x : SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Type, (SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1 x <= 3) /\ SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F2 (SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F2F1 : forall (y : nat) (H : y <= 3), SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1 (SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Type : Set :=
 | SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl2
 | SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl3
.
Definition SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__cond := (fun (_ : SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Type) => True).
Lemma SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__nat__helper.

Definition SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1 t :=
  match t with
  | SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl2 => 0
  | SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl3 => 1
  end.
Definition SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F2 n :=
  match n with
  | 0 => SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl2
  | 1 => SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl3
  | _ => SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__sl2
  end.
Lemma SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1F2 : forall x : SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Type, (SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1 x <= 1) /\ SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F2 (SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1 (SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__Type := Z.
Definition SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__cond := (fun z => (0 <= z <= 1023)%Z).
Inductive SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Type : Set :=
 | SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__startSubCH
 | SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__allocSubCH
.
Definition SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__cond := (fun (_ : SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Type) => True).
Lemma SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__nat__helper.

Definition SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1 t :=
  match t with
  | SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__startSubCH => 0
  | SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__allocSubCH => 1
  end.
Definition SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F2 n :=
  match n with
  | 0 => SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__startSubCH
  | 1 => SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__allocSubCH
  | _ => SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__startSubCH
  end.
Lemma SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1F2 : forall x : SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Type, (SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1 x <= 1) /\ SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F2 (SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1 (SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_PSFCH_Config_r16__Type : Set :=
  make__SL_PSFCH_Config_r16__Type {
    SL_PSFCH_Config_r16__sl_PSFCH_Period_r16 : option SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Type ;
    SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16 : option SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Type ;
    SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16 : option SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Type ;
    SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16 : option SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Type ;
    SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16 : option Z ;
    SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16 : option SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Type ;
}.
Definition SL_PSFCH_Config_r16__root_list : list seq_elem := (
 Opt SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Type SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__cond ::
 Opt SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Type SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__cond ::
 Opt SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Type SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__cond ::
 Opt SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Type SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__cond ::
 Opt Z SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__cond ::
 Opt SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Type SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__cond ::
 nil).
Definition SL_PSFCH_Config_r16__ext_list : list typ := (
  nil).
Definition SL_PSFCH_Config_r16__cond (z : SL_PSFCH_Config_r16__Type) := 
(  opt_cond SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__cond (SL_PSFCH_Config_r16__sl_PSFCH_Period_r16 z) /\
  opt_cond SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__cond (SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16 z) /\
  opt_cond SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__cond (SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16 z) /\
  opt_cond SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__cond (SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16 z) /\
  opt_cond SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__cond (SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16 z) /\
  opt_cond SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__cond (SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16 z) /\
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
Definition SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Format : T_Format SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__nat__Format SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1 SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F2 SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F1F2 SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__F2F1.

Opaque SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__cond SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Format.

Definition SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Format : T_Format SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Type SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__cond := (* Eval compute in *) bit_string_ranged_format 10 275 SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__helper1 SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__helper2.
Opaque SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__cond SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Format.

Definition SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Format : T_Format SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__nat__Format SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1 SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F2 SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F1F2 SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__F2F1.

Opaque SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__cond SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Format.

Definition SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Format : T_Format SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__nat__Format SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1 SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F2 SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F1F2 SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__F2F1.

Opaque SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__cond SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Format.

Definition SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__Format : T_Format Z SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__cond :=
 ranged_int_format (0) (1023) SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__helper1 SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__helper2.

Opaque SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__cond SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__Format.

Definition SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Format : T_Format SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__nat__Format SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1 SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F2 SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F1F2 SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__F2F1.

Opaque SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__cond SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Format.


Definition SL_PSFCH_Config_r16__root_Format_Type := Eval cbn in seq_format_prod SL_PSFCH_Config_r16__root_list.
Definition SL_PSFCH_Config_r16__root_Format_list : SL_PSFCH_Config_r16__root_Format_Type :=
  (SL_PSFCH_Config_r16__sl_PSFCH_Period_r16__Format, (SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16__Format, (SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16__Format, (SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16__Format, (SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16__Format, (SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16__Format, unit_format)))))).

Definition SL_PSFCH_Config_r16__ext_Format_Type := Eval cbn in get_formats SL_PSFCH_Config_r16__ext_list.
Definition SL_PSFCH_Config_r16__ext_Format_list : SL_PSFCH_Config_r16__ext_Format_Type :=
  unit__Format.

Definition SL_PSFCH_Config_r16__list_type : Set := (seq_type SL_PSFCH_Config_r16__root_list) * (seq_ext_type SL_PSFCH_Config_r16__ext_list).
Definition SL_PSFCH_Config_r16__list_cond (z : SL_PSFCH_Config_r16__list_type) : Prop :=
        (seq_cond SL_PSFCH_Config_r16__root_list (fst z)) /\ (seq_ext_cond SL_PSFCH_Config_r16__ext_list (snd z)).
Definition SL_PSFCH_Config_r16__list_format : T_Format SL_PSFCH_Config_r16__list_type SL_PSFCH_Config_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_PSFCH_Config_r16__root_list SL_PSFCH_Config_r16__root_Format_list SL_PSFCH_Config_r16__ext_list SL_PSFCH_Config_r16__ext_Format_list.

Opaque SL_PSFCH_Config_r16__list_format.
Definition SL_PSFCH_Config_r16__F1 (z : SL_PSFCH_Config_r16__Type) : SL_PSFCH_Config_r16__list_type :=
  (((SL_PSFCH_Config_r16__sl_PSFCH_Period_r16 z, (SL_PSFCH_Config_r16__sl_PSFCH_RB_Set_r16 z, (SL_PSFCH_Config_r16__sl_NumMuxCS_Pair_r16 z, (SL_PSFCH_Config_r16__sl_MinTimeGapPSFCH_r16 z, (SL_PSFCH_Config_r16__sl_PSFCH_HopID_r16 z, (SL_PSFCH_Config_r16__sl_PSFCH_CandidateResourceType_r16 z, tt))))))), (
tt)).
Definition SL_PSFCH_Config_r16__F2 (y : SL_PSFCH_Config_r16__list_type) : SL_PSFCH_Config_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SL_PSFCH_Config_r16__Type j0 j1 j2 j3 j4 j5
  end.
Definition SL_PSFCH_Config_r16__helper1 : (forall a : SL_PSFCH_Config_r16__Type, SL_PSFCH_Config_r16__cond a -> SL_PSFCH_Config_r16__list_cond (SL_PSFCH_Config_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_PSFCH_Config_r16__helper2 : (forall a : SL_PSFCH_Config_r16__Type, SL_PSFCH_Config_r16__F2 (SL_PSFCH_Config_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_PSFCH_Config_r16__helper3 : (forall b : SL_PSFCH_Config_r16__list_type, SL_PSFCH_Config_r16__list_cond b -> SL_PSFCH_Config_r16__cond (SL_PSFCH_Config_r16__F2 b) /\ SL_PSFCH_Config_r16__F1 (SL_PSFCH_Config_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_PSFCH_Config_r16__cond, SL_PSFCH_Config_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_PSFCH_Config_r16__Format : T_Format SL_PSFCH_Config_r16__Type SL_PSFCH_Config_r16__cond :=
 proj2_format SL_PSFCH_Config_r16__cond SL_PSFCH_Config_r16__list_format  SL_PSFCH_Config_r16__F1 SL_PSFCH_Config_r16__F2 SL_PSFCH_Config_r16__helper1 SL_PSFCH_Config_r16__helper2 SL_PSFCH_Config_r16__helper3.

Opaque SL_PSFCH_Config_r16__cond SL_PSFCH_Config_r16__Format.

