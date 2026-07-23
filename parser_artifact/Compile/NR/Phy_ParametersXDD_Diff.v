Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Phy_ParametersXDD_Diff__dynamicSFI__Type : Set :=
 | Phy_ParametersXDD_Diff__dynamicSFI__supported
.
Definition Phy_ParametersXDD_Diff__dynamicSFI__cond := (fun (_ : Phy_ParametersXDD_Diff__dynamicSFI__Type) => True).
Lemma Phy_ParametersXDD_Diff__dynamicSFI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__dynamicSFI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__dynamicSFI__nat__helper.

Definition Phy_ParametersXDD_Diff__dynamicSFI__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__dynamicSFI__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__dynamicSFI__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__dynamicSFI__supported
  | _ => Phy_ParametersXDD_Diff__dynamicSFI__supported
  end.
Lemma Phy_ParametersXDD_Diff__dynamicSFI__F1F2 : forall x : Phy_ParametersXDD_Diff__dynamicSFI__Type, (Phy_ParametersXDD_Diff__dynamicSFI__F1 x <= 0) /\ Phy_ParametersXDD_Diff__dynamicSFI__F2 (Phy_ParametersXDD_Diff__dynamicSFI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__dynamicSFI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__dynamicSFI__F1 (Phy_ParametersXDD_Diff__dynamicSFI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Type : Set :=
 | Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__supported
.
Definition Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__cond := (fun (_ : Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Type) => True).
Lemma Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__helper.

Definition Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__supported
  | _ => Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__supported
  end.
Lemma Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1F2 : forall x : Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Type, (Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 x <= 0) /\ Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 (Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 (Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Type : Set :=
 | Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__supported
.
Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__cond := (fun (_ : Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Type) => True).
Lemma Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__nat__helper.

Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__supported
  | _ => Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__supported
  end.
Lemma Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1F2 : forall x : Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Type, (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1 x <= 0) /\ Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F2 (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1 (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Type : Set :=
 | Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__supported
.
Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__cond := (fun (_ : Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Type) => True).
Lemma Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__nat__helper.

Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__supported
  | _ => Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__supported
  end.
Lemma Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1F2 : forall x : Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Type, (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1 x <= 0) /\ Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F2 (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1 (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type : Set :=
 | Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported
.
Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond := (fun (_ : Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type) => True).
Lemma Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__helper.

Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported
  | _ => Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported
  end.
Lemma Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1F2 : forall x : Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type, (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 x <= 0) /\ Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type : Set :=
 | Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported
.
Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond := (fun (_ : Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type) => True).
Lemma Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__helper.

Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported
  | _ => Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported
  end.
Lemma Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1F2 : forall x : Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type, (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 x <= 0) /\ Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Type : Set :=
 | Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__supported
.
Definition Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__cond := (fun (_ : Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Type) => True).
Lemma Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__nat__helper.

Definition Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1 t :=
  match t with
  | Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__supported => 0
  end.
Definition Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F2 n :=
  match n with
  | 0 => Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__supported
  | _ => Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__supported
  end.
Lemma Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1F2 : forall x : Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Type, (Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1 x <= 0) /\ Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F2 (Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1 (Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersXDD_Diff__ext0O__Type : Set :=
  make__Phy_ParametersXDD_Diff__ext0O__Type {
    Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA : option Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type ;
    Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB : option Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type ;
    Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset : option Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Type ;
}.
Definition Phy_ParametersXDD_Diff__ext0O__list := (
 Opt Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond ::
 Opt Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond ::
 Opt Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Type Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__cond ::
 nil).
Definition Phy_ParametersXDD_Diff__ext0O__cond z := 
  opt_cond Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA z) /\
  opt_cond Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB z) /\
  opt_cond Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__cond (Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset z) /\
  True.

Definition Phy_ParametersXDD_Diff__ext0__Type := Phy_ParametersXDD_Diff__ext0O__Type.
Definition Phy_ParametersXDD_Diff__ext0__cond := Phy_ParametersXDD_Diff__ext0O__cond.

Record Phy_ParametersXDD_Diff__Type : Set :=
  make__Phy_ParametersXDD_Diff__Type {
    Phy_ParametersXDD_Diff__dynamicSFI : option Phy_ParametersXDD_Diff__dynamicSFI__Type ;
    Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols : option Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Type ;
    Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH : option Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Type ;
    Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH : option Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Type ;
    Phy_ParametersXDD_Diff__ext0 : option Phy_ParametersXDD_Diff__ext0__Type ;
}.
Definition Phy_ParametersXDD_Diff__root_list : list seq_elem := (
 Opt Phy_ParametersXDD_Diff__dynamicSFI__Type Phy_ParametersXDD_Diff__dynamicSFI__cond ::
 Opt Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Type Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__cond ::
 Opt Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Type Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__cond ::
 Opt Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Type Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__cond ::
 nil).
Definition Phy_ParametersXDD_Diff__ext_list : list typ := (
  typ_cons Phy_ParametersXDD_Diff__ext0__Type Phy_ParametersXDD_Diff__ext0__cond ::
  nil).
Definition Phy_ParametersXDD_Diff__cond (z : Phy_ParametersXDD_Diff__Type) := 
(  opt_cond Phy_ParametersXDD_Diff__dynamicSFI__cond (Phy_ParametersXDD_Diff__dynamicSFI z) /\
  opt_cond Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__cond (Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols z) /\
  opt_cond Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__cond (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH z) /\
  opt_cond Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__cond (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH z) /\
  True) /\ 
(  opt_cond Phy_ParametersXDD_Diff__ext0__cond (Phy_ParametersXDD_Diff__ext0 z) /\
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
Definition Phy_ParametersXDD_Diff__dynamicSFI__Format : T_Format Phy_ParametersXDD_Diff__dynamicSFI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__dynamicSFI__nat__Format Phy_ParametersXDD_Diff__dynamicSFI__F1 Phy_ParametersXDD_Diff__dynamicSFI__F2 Phy_ParametersXDD_Diff__dynamicSFI__F1F2 Phy_ParametersXDD_Diff__dynamicSFI__F2F1.

Opaque Phy_ParametersXDD_Diff__dynamicSFI__cond Phy_ParametersXDD_Diff__dynamicSFI__Format.

Definition Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Format : T_Format Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__Format Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F1F2 Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__F2F1.

Opaque Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__cond Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Format.

Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Format : T_Format Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__nat__Format Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F2 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F1F2 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__F2F1.

Opaque Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__cond Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Format.

Definition Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Format : T_Format Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__nat__Format Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F2 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F1F2 Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__F2F1.

Opaque Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__cond Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Format.

Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Format : T_Format Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__Format Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1F2 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2F1.

Opaque Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Format.

Definition Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Format : T_Format Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__Format Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1F2 Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2F1.

Opaque Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Format.

Definition Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Format : T_Format Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__nat__Format Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1 Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F2 Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F1F2 Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__F2F1.

Opaque Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__cond Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Format.


Definition Phy_ParametersXDD_Diff__ext0O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersXDD_Diff__ext0O__list.
Definition Phy_ParametersXDD_Diff__ext0O__Format_list : Phy_ParametersXDD_Diff__ext0O__Format_Type :=
  (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Format, (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Format, (Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset__Format, unit_format))).
Definition Phy_ParametersXDD_Diff__ext0O__list__Format := (*Eval compute in *) seq_format Phy_ParametersXDD_Diff__ext0O__list Phy_ParametersXDD_Diff__ext0O__Format_list.
Definition Phy_ParametersXDD_Diff__ext0O__F1 z :=
  (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA z, (Phy_ParametersXDD_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB z, (Phy_ParametersXDD_Diff__ext0O__ul_SchedulingOffset z, tt))).
Definition Phy_ParametersXDD_Diff__ext0O__F2 (y : seq_type Phy_ParametersXDD_Diff__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Phy_ParametersXDD_Diff__ext0O__Type i0 i1 i2
  end.
Lemma Phy_ParametersXDD_Diff__ext0O__F1F2_cond (z : Phy_ParametersXDD_Diff__ext0O__Type)
  : Phy_ParametersXDD_Diff__ext0O__cond z ->
  (seq_cond Phy_ParametersXDD_Diff__ext0O__list (Phy_ParametersXDD_Diff__ext0O__F1 z)).
intro H. unfold Phy_ParametersXDD_Diff__ext0O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersXDD_Diff__ext0O__F1F2_cond2 (z : Phy_ParametersXDD_Diff__ext0O__Type)
 : Phy_ParametersXDD_Diff__ext0O__F2 (Phy_ParametersXDD_Diff__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersXDD_Diff__ext0O__F2F1_cond (y : seq_type Phy_ParametersXDD_Diff__ext0O__list)
  : seq_cond Phy_ParametersXDD_Diff__ext0O__list y ->
 (Phy_ParametersXDD_Diff__ext0O__cond (Phy_ParametersXDD_Diff__ext0O__F2 y)) /\  Phy_ParametersXDD_Diff__ext0O__F1 (Phy_ParametersXDD_Diff__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersXDD_Diff__ext0O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersXDD_Diff__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersXDD_Diff__ext0O__Format : T_Format Phy_ParametersXDD_Diff__ext0O__Type Phy_ParametersXDD_Diff__ext0O__cond :=
        proj2_format  Phy_ParametersXDD_Diff__ext0O__cond Phy_ParametersXDD_Diff__ext0O__list__Format
    Phy_ParametersXDD_Diff__ext0O__F1 Phy_ParametersXDD_Diff__ext0O__F2 Phy_ParametersXDD_Diff__ext0O__F1F2_cond  Phy_ParametersXDD_Diff__ext0O__F1F2_cond2 Phy_ParametersXDD_Diff__ext0O__F2F1_cond.
Opaque Phy_ParametersXDD_Diff__ext0O__cond Phy_ParametersXDD_Diff__ext0O__Format.

Definition Phy_ParametersXDD_Diff__ext0__check_all_none (b : Phy_ParametersXDD_Diff__ext0O__Type) : bool :=
match b with 
  | make__Phy_ParametersXDD_Diff__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersXDD_Diff__ext0__Format : T_Format Phy_ParametersXDD_Diff__ext0__Type Phy_ParametersXDD_Diff__ext0__cond :=
  restrict_add_format Phy_ParametersXDD_Diff__ext0__check_all_none Phy_ParametersXDD_Diff__ext0O__Format.

Opaque Phy_ParametersXDD_Diff__ext0__cond Phy_ParametersXDD_Diff__ext0__Format.


Definition Phy_ParametersXDD_Diff__root_Format_Type := Eval cbn in seq_format_prod Phy_ParametersXDD_Diff__root_list.
Definition Phy_ParametersXDD_Diff__root_Format_list : Phy_ParametersXDD_Diff__root_Format_Type :=
  (Phy_ParametersXDD_Diff__dynamicSFI__Format, (Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols__Format, (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH__Format, (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH__Format, unit_format)))).

Definition Phy_ParametersXDD_Diff__ext_Format_Type := Eval cbn in get_formats Phy_ParametersXDD_Diff__ext_list.
Definition Phy_ParametersXDD_Diff__ext_Format_list : Phy_ParametersXDD_Diff__ext_Format_Type :=
  (Phy_ParametersXDD_Diff__ext0__Format, unit__Format).

Definition Phy_ParametersXDD_Diff__list_type : Set := (seq_type Phy_ParametersXDD_Diff__root_list) * (seq_ext_type Phy_ParametersXDD_Diff__ext_list).
Definition Phy_ParametersXDD_Diff__list_cond (z : Phy_ParametersXDD_Diff__list_type) : Prop :=
        (seq_cond Phy_ParametersXDD_Diff__root_list (fst z)) /\ (seq_ext_cond Phy_ParametersXDD_Diff__ext_list (snd z)).
Definition Phy_ParametersXDD_Diff__list_format : T_Format Phy_ParametersXDD_Diff__list_type Phy_ParametersXDD_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format Phy_ParametersXDD_Diff__root_list Phy_ParametersXDD_Diff__root_Format_list Phy_ParametersXDD_Diff__ext_list Phy_ParametersXDD_Diff__ext_Format_list.

Opaque Phy_ParametersXDD_Diff__list_format.
Definition Phy_ParametersXDD_Diff__F1 (z : Phy_ParametersXDD_Diff__Type) : Phy_ParametersXDD_Diff__list_type :=
  (((Phy_ParametersXDD_Diff__dynamicSFI z, (Phy_ParametersXDD_Diff__twoPUCCH_F0_2_ConsecSymbols z, (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUSCH z, (Phy_ParametersXDD_Diff__twoDifferentTPC_Loop_PUCCH z, tt))))), (
(Phy_ParametersXDD_Diff__ext0 z, tt))).
Definition Phy_ParametersXDD_Diff__F2 (y : Phy_ParametersXDD_Diff__list_type) : Phy_ParametersXDD_Diff__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__Phy_ParametersXDD_Diff__Type j0 j1 j2 j3 i0
  end.
Definition Phy_ParametersXDD_Diff__helper1 : (forall a : Phy_ParametersXDD_Diff__Type, Phy_ParametersXDD_Diff__cond a -> Phy_ParametersXDD_Diff__list_cond (Phy_ParametersXDD_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersXDD_Diff__helper2 : (forall a : Phy_ParametersXDD_Diff__Type, Phy_ParametersXDD_Diff__F2 (Phy_ParametersXDD_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersXDD_Diff__helper3 : (forall b : Phy_ParametersXDD_Diff__list_type, Phy_ParametersXDD_Diff__list_cond b -> Phy_ParametersXDD_Diff__cond (Phy_ParametersXDD_Diff__F2 b) /\ Phy_ParametersXDD_Diff__F1 (Phy_ParametersXDD_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Phy_ParametersXDD_Diff__cond, Phy_ParametersXDD_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Phy_ParametersXDD_Diff__Format : T_Format Phy_ParametersXDD_Diff__Type Phy_ParametersXDD_Diff__cond :=
 proj2_format Phy_ParametersXDD_Diff__cond Phy_ParametersXDD_Diff__list_format  Phy_ParametersXDD_Diff__F1 Phy_ParametersXDD_Diff__F2 Phy_ParametersXDD_Diff__helper1 Phy_ParametersXDD_Diff__helper2 Phy_ParametersXDD_Diff__helper3.

Opaque Phy_ParametersXDD_Diff__cond Phy_ParametersXDD_Diff__Format.

