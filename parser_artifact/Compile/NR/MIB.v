Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition MIB__systemFrameNumber__Type := bit_string_fixed.
Definition MIB__systemFrameNumber__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 6 /\ bit_string_len_prop (fst z) (snd z)).
Inductive MIB__subCarrierSpacingCommon__Type : Set :=
 | MIB__subCarrierSpacingCommon__scs15or60
 | MIB__subCarrierSpacingCommon__scs30or120
.
Definition MIB__subCarrierSpacingCommon__cond := (fun (_ : MIB__subCarrierSpacingCommon__Type) => True).
Lemma MIB__subCarrierSpacingCommon__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIB__subCarrierSpacingCommon__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIB__subCarrierSpacingCommon__nat__helper.

Definition MIB__subCarrierSpacingCommon__F1 t :=
  match t with
  | MIB__subCarrierSpacingCommon__scs15or60 => 0
  | MIB__subCarrierSpacingCommon__scs30or120 => 1
  end.
Definition MIB__subCarrierSpacingCommon__F2 n :=
  match n with
  | 0 => MIB__subCarrierSpacingCommon__scs15or60
  | 1 => MIB__subCarrierSpacingCommon__scs30or120
  | _ => MIB__subCarrierSpacingCommon__scs15or60
  end.
Lemma MIB__subCarrierSpacingCommon__F1F2 : forall x : MIB__subCarrierSpacingCommon__Type, (MIB__subCarrierSpacingCommon__F1 x <= 1) /\ MIB__subCarrierSpacingCommon__F2 (MIB__subCarrierSpacingCommon__F1 x) = x. imp_solve. Qed.
Lemma MIB__subCarrierSpacingCommon__F2F1 : forall (y : nat) (H : y <= 1), MIB__subCarrierSpacingCommon__F1 (MIB__subCarrierSpacingCommon__F2 y) = y. enum_solve H y. Qed.

Lemma MIB__ssb_SubcarrierOffset__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma MIB__ssb_SubcarrierOffset__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MIB__ssb_SubcarrierOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIB__ssb_SubcarrierOffset__Type := Z.
Definition MIB__ssb_SubcarrierOffset__cond := (fun z => (0 <= z <= 15)%Z).
Inductive MIB__dmrs_TypeA_Position__Type : Set :=
 | MIB__dmrs_TypeA_Position__pos2
 | MIB__dmrs_TypeA_Position__pos3
.
Definition MIB__dmrs_TypeA_Position__cond := (fun (_ : MIB__dmrs_TypeA_Position__Type) => True).
Lemma MIB__dmrs_TypeA_Position__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIB__dmrs_TypeA_Position__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIB__dmrs_TypeA_Position__nat__helper.

Definition MIB__dmrs_TypeA_Position__F1 t :=
  match t with
  | MIB__dmrs_TypeA_Position__pos2 => 0
  | MIB__dmrs_TypeA_Position__pos3 => 1
  end.
Definition MIB__dmrs_TypeA_Position__F2 n :=
  match n with
  | 0 => MIB__dmrs_TypeA_Position__pos2
  | 1 => MIB__dmrs_TypeA_Position__pos3
  | _ => MIB__dmrs_TypeA_Position__pos2
  end.
Lemma MIB__dmrs_TypeA_Position__F1F2 : forall x : MIB__dmrs_TypeA_Position__Type, (MIB__dmrs_TypeA_Position__F1 x <= 1) /\ MIB__dmrs_TypeA_Position__F2 (MIB__dmrs_TypeA_Position__F1 x) = x. imp_solve. Qed.
Lemma MIB__dmrs_TypeA_Position__F2F1 : forall (y : nat) (H : y <= 1), MIB__dmrs_TypeA_Position__F1 (MIB__dmrs_TypeA_Position__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PDCCH_ConfigSIB1.

Opaque PDCCH_ConfigSIB1__cond PDCCH_ConfigSIB1__Format.

Inductive MIB__cellBarred__Type : Set :=
 | MIB__cellBarred__barred
 | MIB__cellBarred__notBarred
.
Definition MIB__cellBarred__cond := (fun (_ : MIB__cellBarred__Type) => True).
Lemma MIB__cellBarred__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIB__cellBarred__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIB__cellBarred__nat__helper.

Definition MIB__cellBarred__F1 t :=
  match t with
  | MIB__cellBarred__barred => 0
  | MIB__cellBarred__notBarred => 1
  end.
Definition MIB__cellBarred__F2 n :=
  match n with
  | 0 => MIB__cellBarred__barred
  | 1 => MIB__cellBarred__notBarred
  | _ => MIB__cellBarred__barred
  end.
Lemma MIB__cellBarred__F1F2 : forall x : MIB__cellBarred__Type, (MIB__cellBarred__F1 x <= 1) /\ MIB__cellBarred__F2 (MIB__cellBarred__F1 x) = x. imp_solve. Qed.
Lemma MIB__cellBarred__F2F1 : forall (y : nat) (H : y <= 1), MIB__cellBarred__F1 (MIB__cellBarred__F2 y) = y. enum_solve H y. Qed.

Inductive MIB__intraFreqReselection__Type : Set :=
 | MIB__intraFreqReselection__allowed
 | MIB__intraFreqReselection__notAllowed
.
Definition MIB__intraFreqReselection__cond := (fun (_ : MIB__intraFreqReselection__Type) => True).
Lemma MIB__intraFreqReselection__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIB__intraFreqReselection__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIB__intraFreqReselection__nat__helper.

Definition MIB__intraFreqReselection__F1 t :=
  match t with
  | MIB__intraFreqReselection__allowed => 0
  | MIB__intraFreqReselection__notAllowed => 1
  end.
Definition MIB__intraFreqReselection__F2 n :=
  match n with
  | 0 => MIB__intraFreqReselection__allowed
  | 1 => MIB__intraFreqReselection__notAllowed
  | _ => MIB__intraFreqReselection__allowed
  end.
Lemma MIB__intraFreqReselection__F1F2 : forall x : MIB__intraFreqReselection__Type, (MIB__intraFreqReselection__F1 x <= 1) /\ MIB__intraFreqReselection__F2 (MIB__intraFreqReselection__F1 x) = x. imp_solve. Qed.
Lemma MIB__intraFreqReselection__F2F1 : forall (y : nat) (H : y <= 1), MIB__intraFreqReselection__F1 (MIB__intraFreqReselection__F2 y) = y. enum_solve H y. Qed.

Definition MIB__spare__Type := bit_string_fixed.
Definition MIB__spare__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 1 /\ bit_string_len_prop (fst z) (snd z)).
Record MIB__Type : Set :=
  make__MIB__Type {
    MIB__systemFrameNumber : MIB__systemFrameNumber__Type ;
    MIB__subCarrierSpacingCommon : MIB__subCarrierSpacingCommon__Type ;
    MIB__ssb_SubcarrierOffset : Z ;
    MIB__dmrs_TypeA_Position : MIB__dmrs_TypeA_Position__Type ;
    MIB__pdcch_ConfigSIB1 : PDCCH_ConfigSIB1__Type ;
    MIB__cellBarred : MIB__cellBarred__Type ;
    MIB__intraFreqReselection : MIB__intraFreqReselection__Type ;
    MIB__spare : MIB__spare__Type ;
}.
Definition MIB__list := (
 Nor MIB__systemFrameNumber__Type MIB__systemFrameNumber__cond ::
 Nor MIB__subCarrierSpacingCommon__Type MIB__subCarrierSpacingCommon__cond ::
 Nor Z MIB__ssb_SubcarrierOffset__cond ::
 Nor MIB__dmrs_TypeA_Position__Type MIB__dmrs_TypeA_Position__cond ::
 Nor PDCCH_ConfigSIB1__Type PDCCH_ConfigSIB1__cond ::
 Nor MIB__cellBarred__Type MIB__cellBarred__cond ::
 Nor MIB__intraFreqReselection__Type MIB__intraFreqReselection__cond ::
 Nor MIB__spare__Type MIB__spare__cond ::
 nil).
Definition MIB__cond z := 
  MIB__systemFrameNumber__cond (MIB__systemFrameNumber z) /\
  MIB__subCarrierSpacingCommon__cond (MIB__subCarrierSpacingCommon z) /\
  MIB__ssb_SubcarrierOffset__cond (MIB__ssb_SubcarrierOffset z) /\
  MIB__dmrs_TypeA_Position__cond (MIB__dmrs_TypeA_Position z) /\
  PDCCH_ConfigSIB1__cond (MIB__pdcch_ConfigSIB1 z) /\
  MIB__cellBarred__cond (MIB__cellBarred z) /\
  MIB__intraFreqReselection__cond (MIB__intraFreqReselection z) /\
  MIB__spare__cond (MIB__spare z) /\
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
Definition MIB__systemFrameNumber__Format : T_Format MIB__systemFrameNumber__Type MIB__systemFrameNumber__cond := (* Eval compute in *) bit_string_fixed_format 6.
Opaque MIB__systemFrameNumber__cond MIB__systemFrameNumber__Format.

Definition MIB__subCarrierSpacingCommon__Format : T_Format MIB__subCarrierSpacingCommon__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIB__subCarrierSpacingCommon__nat__Format MIB__subCarrierSpacingCommon__F1 MIB__subCarrierSpacingCommon__F2 MIB__subCarrierSpacingCommon__F1F2 MIB__subCarrierSpacingCommon__F2F1.

Opaque MIB__subCarrierSpacingCommon__cond MIB__subCarrierSpacingCommon__Format.

Definition MIB__ssb_SubcarrierOffset__Format : T_Format Z MIB__ssb_SubcarrierOffset__cond :=
 ranged_int_format (0) (15) MIB__ssb_SubcarrierOffset__helper1 MIB__ssb_SubcarrierOffset__helper2.

Opaque MIB__ssb_SubcarrierOffset__cond MIB__ssb_SubcarrierOffset__Format.

Definition MIB__dmrs_TypeA_Position__Format : T_Format MIB__dmrs_TypeA_Position__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIB__dmrs_TypeA_Position__nat__Format MIB__dmrs_TypeA_Position__F1 MIB__dmrs_TypeA_Position__F2 MIB__dmrs_TypeA_Position__F1F2 MIB__dmrs_TypeA_Position__F2F1.

Opaque MIB__dmrs_TypeA_Position__cond MIB__dmrs_TypeA_Position__Format.

Definition MIB__cellBarred__Format : T_Format MIB__cellBarred__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIB__cellBarred__nat__Format MIB__cellBarred__F1 MIB__cellBarred__F2 MIB__cellBarred__F1F2 MIB__cellBarred__F2F1.

Opaque MIB__cellBarred__cond MIB__cellBarred__Format.

Definition MIB__intraFreqReselection__Format : T_Format MIB__intraFreqReselection__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIB__intraFreqReselection__nat__Format MIB__intraFreqReselection__F1 MIB__intraFreqReselection__F2 MIB__intraFreqReselection__F1F2 MIB__intraFreqReselection__F2F1.

Opaque MIB__intraFreqReselection__cond MIB__intraFreqReselection__Format.

Definition MIB__spare__Format : T_Format MIB__spare__Type MIB__spare__cond := (* Eval compute in *) bit_string_fixed_format 1.
Opaque MIB__spare__cond MIB__spare__Format.


Definition MIB__Format_Type := Eval cbn in seq_format_prod MIB__list.
Definition MIB__Format_list : MIB__Format_Type :=
  (MIB__systemFrameNumber__Format, (MIB__subCarrierSpacingCommon__Format, (MIB__ssb_SubcarrierOffset__Format, (MIB__dmrs_TypeA_Position__Format, (PDCCH_ConfigSIB1__Format, (MIB__cellBarred__Format, (MIB__intraFreqReselection__Format, (MIB__spare__Format, unit_format)))))))).
Definition MIB__list__Format := (*Eval compute in *) seq_format MIB__list MIB__Format_list.
Definition MIB__F1 z :=
  (MIB__systemFrameNumber z, (MIB__subCarrierSpacingCommon z, (MIB__ssb_SubcarrierOffset z, (MIB__dmrs_TypeA_Position z, (MIB__pdcch_ConfigSIB1 z, (MIB__cellBarred z, (MIB__intraFreqReselection z, (MIB__spare z, tt)))))))).
Definition MIB__F2 (y : seq_type MIB__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__MIB__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma MIB__F1F2_cond (z : MIB__Type)
  : MIB__cond z ->
  (seq_cond MIB__list (MIB__F1 z)).
intro H. unfold MIB__cond in H. simpl. auto. Qed.
Lemma MIB__F1F2_cond2 (z : MIB__Type)
 : MIB__F2 (MIB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIB__F2F1_cond (y : seq_type MIB__list)
  : seq_cond MIB__list y ->
 (MIB__cond (MIB__F2 y)) /\  MIB__F1 (MIB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIB__cond. simpl in *. auto.
 - simpl. unfold MIB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIB__Format : T_Format MIB__Type MIB__cond :=
        proj2_format  MIB__cond MIB__list__Format
    MIB__F1 MIB__F2 MIB__F1F2_cond  MIB__F1F2_cond2 MIB__F2F1_cond.
Opaque MIB__cond MIB__Format.

