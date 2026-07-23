Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.AdditionalPCIIndex_r17.

Opaque AdditionalPCIIndex_r17__cond AdditionalPCIIndex_r17__Format.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Inductive SSB_MTC_AdditionalPCI_r17__periodicity_r17__Type : Set :=
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms5
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms10
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms20
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms40
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms80
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms160
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__spare2
 | SSB_MTC_AdditionalPCI_r17__periodicity_r17__spare1
.
Definition SSB_MTC_AdditionalPCI_r17__periodicity_r17__cond := (fun (_ : SSB_MTC_AdditionalPCI_r17__periodicity_r17__Type) => True).
Lemma SSB_MTC_AdditionalPCI_r17__periodicity_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SSB_MTC_AdditionalPCI_r17__periodicity_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SSB_MTC_AdditionalPCI_r17__periodicity_r17__nat__helper.

Definition SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1 t :=
  match t with
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms5 => 0
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms10 => 1
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms20 => 2
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms40 => 3
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms80 => 4
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms160 => 5
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__spare2 => 6
  | SSB_MTC_AdditionalPCI_r17__periodicity_r17__spare1 => 7
  end.
Definition SSB_MTC_AdditionalPCI_r17__periodicity_r17__F2 n :=
  match n with
  | 0 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms5
  | 1 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms10
  | 2 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms20
  | 3 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms40
  | 4 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms80
  | 5 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms160
  | 6 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__spare2
  | 7 => SSB_MTC_AdditionalPCI_r17__periodicity_r17__spare1
  | _ => SSB_MTC_AdditionalPCI_r17__periodicity_r17__ms5
  end.
Lemma SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1F2 : forall x : SSB_MTC_AdditionalPCI_r17__periodicity_r17__Type, (SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1 x <= 7) /\ SSB_MTC_AdditionalPCI_r17__periodicity_r17__F2 (SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1 x) = x. imp_solve. Qed.
Lemma SSB_MTC_AdditionalPCI_r17__periodicity_r17__F2F1 : forall (y : nat) (H : y <= 7), SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1 (SSB_MTC_AdditionalPCI_r17__periodicity_r17__F2 y) = y. enum_solve H y. Qed.

Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Type := bit_string_fixed.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Type := bit_string_fixed.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Type := bit_string_fixed.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 64 /\ bit_string_len_prop (fst z) (snd z)).

Inductive SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type : Set :=
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Type -> SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Type -> SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Type -> SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type
.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list : list typ := (
typ_cons SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__cond ::
typ_cons SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__cond ::
typ_cons SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__cond ::
 nil).
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond (c : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type) := 
  match c with
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap t => SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__cond t 
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap t => SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__cond t 
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap t => SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__cond t 
  end.

Lemma SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__len_helper1 : to_bit_sz (length SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__len_helper2 : 2 <= length2 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list.
 simpl. lia. Qed.
Lemma SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__helper1 : (-60 <= 50)%Z.  lia. Qed.
Lemma SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__helper2 : to_bit_sz (Z.to_nat (50 - -60)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (50 - -60))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__Type := Z.
Definition SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__cond := (fun z => (-60 <= z <= 50)%Z).
Record SSB_MTC_AdditionalPCI_r17__Type : Set :=
  make__SSB_MTC_AdditionalPCI_r17__Type {
    SSB_MTC_AdditionalPCI_r17__additionalPCIIndex_r17 : AdditionalPCIIndex_r17__Type ;
    SSB_MTC_AdditionalPCI_r17__additionalPCI_r17 : PhysCellId__Type ;
    SSB_MTC_AdditionalPCI_r17__periodicity_r17 : SSB_MTC_AdditionalPCI_r17__periodicity_r17__Type ;
    SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17 : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type ;
    SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17 : Z ;
}.
Definition SSB_MTC_AdditionalPCI_r17__list := (
 Nor AdditionalPCIIndex_r17__Type AdditionalPCIIndex_r17__cond ::
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor SSB_MTC_AdditionalPCI_r17__periodicity_r17__Type SSB_MTC_AdditionalPCI_r17__periodicity_r17__cond ::
 Nor SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond ::
 Nor Z SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__cond ::
 nil).
Definition SSB_MTC_AdditionalPCI_r17__cond z := 
  AdditionalPCIIndex_r17__cond (SSB_MTC_AdditionalPCI_r17__additionalPCIIndex_r17 z) /\
  PhysCellId__cond (SSB_MTC_AdditionalPCI_r17__additionalPCI_r17 z) /\
  SSB_MTC_AdditionalPCI_r17__periodicity_r17__cond (SSB_MTC_AdditionalPCI_r17__periodicity_r17 z) /\
  SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17 z) /\
  SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__cond (SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17 z) /\
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
Definition SSB_MTC_AdditionalPCI_r17__periodicity_r17__Format : T_Format SSB_MTC_AdditionalPCI_r17__periodicity_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SSB_MTC_AdditionalPCI_r17__periodicity_r17__nat__Format SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1 SSB_MTC_AdditionalPCI_r17__periodicity_r17__F2 SSB_MTC_AdditionalPCI_r17__periodicity_r17__F1F2 SSB_MTC_AdditionalPCI_r17__periodicity_r17__F2F1.

Opaque SSB_MTC_AdditionalPCI_r17__periodicity_r17__cond SSB_MTC_AdditionalPCI_r17__periodicity_r17__Format.

Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Format : T_Format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Format.

Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Format : T_Format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Format.

Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Format : T_Format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__cond := (* Eval compute in *) bit_string_fixed_format 64.
Opaque SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Format.


Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format_Type := Eval cbn in get_formats SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format_list : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format_Type :=
  (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Format, (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Format, (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Format, unit__Format))).
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list__Format := Eval compute in choice_format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__len_helper1 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__len_helper2  SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format_list.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F1 (z : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type) : (choice SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list) :=
  match z with
   | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap t => existT _ 0 t
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap t => existT _ 1 t
  | SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap t => existT _ 2 t
  end.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__g := (fun n => typ_set (get_nth_typ SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list n)).
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F2 (y : choice SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list) : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__g n -> SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type) with
    | 0 => fun (t : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap__Type) => SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__shortBitmap t 
    | 1 => fun (t : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap__Type) => SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__mediumBitmap t 
    | 2 => fun (t : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap__Type) => SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__longBitmap t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type with end) n0
           end t0).

Lemma SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__helper2 :  forall (y : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type), SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond y -> choice_cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__helper3 :  forall (y : SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type), SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F2 (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__helper4 : (forall b : choice SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list, choice_cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list b -> SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F2 b) /\ SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F1 (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F1 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F2.
Definition SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format : T_Format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Type SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond :=
  (* Eval compute in *) proj2_format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__list__Format SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F1 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__F2 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__helper2 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__helper3 SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__helper4.
Opaque SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__cond SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format.

Definition SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__Format : T_Format Z SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__cond :=
 ranged_int_format (-60) (50) SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__helper1 SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__helper2.

Opaque SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__cond SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__Format.


Definition SSB_MTC_AdditionalPCI_r17__Format_Type := Eval cbn in seq_format_prod SSB_MTC_AdditionalPCI_r17__list.
Definition SSB_MTC_AdditionalPCI_r17__Format_list : SSB_MTC_AdditionalPCI_r17__Format_Type :=
  (AdditionalPCIIndex_r17__Format, (PhysCellId__Format, (SSB_MTC_AdditionalPCI_r17__periodicity_r17__Format, (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17__Format, (SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17__Format, unit_format))))).
Definition SSB_MTC_AdditionalPCI_r17__list__Format := (*Eval compute in *) seq_format SSB_MTC_AdditionalPCI_r17__list SSB_MTC_AdditionalPCI_r17__Format_list.
Definition SSB_MTC_AdditionalPCI_r17__F1 z :=
  (SSB_MTC_AdditionalPCI_r17__additionalPCIIndex_r17 z, (SSB_MTC_AdditionalPCI_r17__additionalPCI_r17 z, (SSB_MTC_AdditionalPCI_r17__periodicity_r17 z, (SSB_MTC_AdditionalPCI_r17__ssb_PositionsInBurst_r17 z, (SSB_MTC_AdditionalPCI_r17__ss_PBCH_BlockPower_r17 z, tt))))).
Definition SSB_MTC_AdditionalPCI_r17__F2 (y : seq_type SSB_MTC_AdditionalPCI_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SSB_MTC_AdditionalPCI_r17__Type i0 i1 i2 i3 i4
  end.
Lemma SSB_MTC_AdditionalPCI_r17__F1F2_cond (z : SSB_MTC_AdditionalPCI_r17__Type)
  : SSB_MTC_AdditionalPCI_r17__cond z ->
  (seq_cond SSB_MTC_AdditionalPCI_r17__list (SSB_MTC_AdditionalPCI_r17__F1 z)).
intro H. unfold SSB_MTC_AdditionalPCI_r17__cond in H. simpl. auto. Qed.
Lemma SSB_MTC_AdditionalPCI_r17__F1F2_cond2 (z : SSB_MTC_AdditionalPCI_r17__Type)
 : SSB_MTC_AdditionalPCI_r17__F2 (SSB_MTC_AdditionalPCI_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_MTC_AdditionalPCI_r17__F2F1_cond (y : seq_type SSB_MTC_AdditionalPCI_r17__list)
  : seq_cond SSB_MTC_AdditionalPCI_r17__list y ->
 (SSB_MTC_AdditionalPCI_r17__cond (SSB_MTC_AdditionalPCI_r17__F2 y)) /\  SSB_MTC_AdditionalPCI_r17__F1 (SSB_MTC_AdditionalPCI_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_MTC_AdditionalPCI_r17__cond. simpl in *. auto.
 - simpl. unfold SSB_MTC_AdditionalPCI_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_MTC_AdditionalPCI_r17__Format : T_Format SSB_MTC_AdditionalPCI_r17__Type SSB_MTC_AdditionalPCI_r17__cond :=
        proj2_format  SSB_MTC_AdditionalPCI_r17__cond SSB_MTC_AdditionalPCI_r17__list__Format
    SSB_MTC_AdditionalPCI_r17__F1 SSB_MTC_AdditionalPCI_r17__F2 SSB_MTC_AdditionalPCI_r17__F1F2_cond  SSB_MTC_AdditionalPCI_r17__F1F2_cond2 SSB_MTC_AdditionalPCI_r17__F2F1_cond.
Opaque SSB_MTC_AdditionalPCI_r17__cond SSB_MTC_AdditionalPCI_r17__Format.

