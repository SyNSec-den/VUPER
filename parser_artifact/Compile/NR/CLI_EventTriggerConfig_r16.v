Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasTriggerQuantityCLI_r16.

Opaque MeasTriggerQuantityCLI_r16__cond MeasTriggerQuantityCLI_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type : Set :=
  make__CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type {
    CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__i1_Threshold_r16 : MeasTriggerQuantityCLI_r16__Type ;
    CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__reportOnLeave_r16 : bool ;
    CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__hysteresis_r16 : Hysteresis__Type ;
    CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__timeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list := (
 Nor MeasTriggerQuantityCLI_r16__Type MeasTriggerQuantityCLI_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond z := 
  MeasTriggerQuantityCLI_r16__cond (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__i1_Threshold_r16 z) /\
  (fun _ => True) (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__reportOnLeave_r16 z) /\
  Hysteresis__cond (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__hysteresis_r16 z) /\
  TimeToTrigger__cond (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__timeToTrigger_r16 z) /\
  True.


Inductive CLI_EventTriggerConfig_r16__eventId_r16__root__Type : Set := | CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16 : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type -> CLI_EventTriggerConfig_r16__eventId_r16__root__Type.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__cond (c : CLI_EventTriggerConfig_r16__eventId_r16__root__Type) := 
  match c with
  | CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16 t => CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond t 
  end.


Definition CLI_EventTriggerConfig_r16__eventId_r16__ext__Type : Set := Empty_set.
Definition CLI_EventTriggerConfig_r16__eventId_r16__ext__cond (c : CLI_EventTriggerConfig_r16__eventId_r16__ext__Type) := True.
Definition CLI_EventTriggerConfig_r16__eventId_r16__Type : Set := CLI_EventTriggerConfig_r16__eventId_r16__root__Type + CLI_EventTriggerConfig_r16__eventId_r16__ext__Type.
Definition CLI_EventTriggerConfig_r16__eventId_r16__cond :=
  sum_cond CLI_EventTriggerConfig_r16__eventId_r16__root__cond CLI_EventTriggerConfig_r16__eventId_r16__ext__cond.
Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive CLI_EventTriggerConfig_r16__reportAmount_r16__Type : Set :=
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r1
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r2
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r4
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r8
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r16
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r32
 | CLI_EventTriggerConfig_r16__reportAmount_r16__r64
 | CLI_EventTriggerConfig_r16__reportAmount_r16__infinity
.
Definition CLI_EventTriggerConfig_r16__reportAmount_r16__cond := (fun (_ : CLI_EventTriggerConfig_r16__reportAmount_r16__Type) => True).
Lemma CLI_EventTriggerConfig_r16__reportAmount_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CLI_EventTriggerConfig_r16__reportAmount_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CLI_EventTriggerConfig_r16__reportAmount_r16__nat__helper.

Definition CLI_EventTriggerConfig_r16__reportAmount_r16__F1 t :=
  match t with
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r1 => 0
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r2 => 1
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r4 => 2
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r8 => 3
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r16 => 4
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r32 => 5
  | CLI_EventTriggerConfig_r16__reportAmount_r16__r64 => 6
  | CLI_EventTriggerConfig_r16__reportAmount_r16__infinity => 7
  end.
Definition CLI_EventTriggerConfig_r16__reportAmount_r16__F2 n :=
  match n with
  | 0 => CLI_EventTriggerConfig_r16__reportAmount_r16__r1
  | 1 => CLI_EventTriggerConfig_r16__reportAmount_r16__r2
  | 2 => CLI_EventTriggerConfig_r16__reportAmount_r16__r4
  | 3 => CLI_EventTriggerConfig_r16__reportAmount_r16__r8
  | 4 => CLI_EventTriggerConfig_r16__reportAmount_r16__r16
  | 5 => CLI_EventTriggerConfig_r16__reportAmount_r16__r32
  | 6 => CLI_EventTriggerConfig_r16__reportAmount_r16__r64
  | 7 => CLI_EventTriggerConfig_r16__reportAmount_r16__infinity
  | _ => CLI_EventTriggerConfig_r16__reportAmount_r16__r1
  end.
Lemma CLI_EventTriggerConfig_r16__reportAmount_r16__F1F2 : forall x : CLI_EventTriggerConfig_r16__reportAmount_r16__Type, (CLI_EventTriggerConfig_r16__reportAmount_r16__F1 x <= 7) /\ CLI_EventTriggerConfig_r16__reportAmount_r16__F2 (CLI_EventTriggerConfig_r16__reportAmount_r16__F1 x) = x. imp_solve. Qed.
Lemma CLI_EventTriggerConfig_r16__reportAmount_r16__F2F1 : forall (y : nat) (H : y <= 7), CLI_EventTriggerConfig_r16__reportAmount_r16__F1 (CLI_EventTriggerConfig_r16__reportAmount_r16__F2 y) = y. enum_solve H y. Qed.

Lemma CLI_EventTriggerConfig_r16__maxReportCLI_r16__helper1 : (1 <= maxCLI_Report_r16)%Z. unfold maxCLI_Report_r16.
 lia. Qed.
Lemma CLI_EventTriggerConfig_r16__maxReportCLI_r16__helper2 : to_bit_sz (Z.to_nat (maxCLI_Report_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCLI_Report_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CLI_EventTriggerConfig_r16__maxReportCLI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CLI_EventTriggerConfig_r16__maxReportCLI_r16__Type := Z.
Definition CLI_EventTriggerConfig_r16__maxReportCLI_r16__cond := (fun z => (1 <= z <= maxCLI_Report_r16)%Z).
Record CLI_EventTriggerConfig_r16__Type : Set :=
  make__CLI_EventTriggerConfig_r16__Type {
    CLI_EventTriggerConfig_r16__eventId_r16 : CLI_EventTriggerConfig_r16__eventId_r16__Type ;
    CLI_EventTriggerConfig_r16__reportInterval_r16 : ReportInterval__Type ;
    CLI_EventTriggerConfig_r16__reportAmount_r16 : CLI_EventTriggerConfig_r16__reportAmount_r16__Type ;
    CLI_EventTriggerConfig_r16__maxReportCLI_r16 : Z ;
}.
Definition CLI_EventTriggerConfig_r16__root_list : list seq_elem := (
 Nor CLI_EventTriggerConfig_r16__eventId_r16__Type CLI_EventTriggerConfig_r16__eventId_r16__cond ::
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor CLI_EventTriggerConfig_r16__reportAmount_r16__Type CLI_EventTriggerConfig_r16__reportAmount_r16__cond ::
 Nor Z CLI_EventTriggerConfig_r16__maxReportCLI_r16__cond ::
 nil).
Definition CLI_EventTriggerConfig_r16__ext_list : list typ := (
  nil).
Definition CLI_EventTriggerConfig_r16__cond (z : CLI_EventTriggerConfig_r16__Type) := 
(  CLI_EventTriggerConfig_r16__eventId_r16__cond (CLI_EventTriggerConfig_r16__eventId_r16 z) /\
  ReportInterval__cond (CLI_EventTriggerConfig_r16__reportInterval_r16 z) /\
  CLI_EventTriggerConfig_r16__reportAmount_r16__cond (CLI_EventTriggerConfig_r16__reportAmount_r16 z) /\
  CLI_EventTriggerConfig_r16__maxReportCLI_r16__cond (CLI_EventTriggerConfig_r16__maxReportCLI_r16 z) /\
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

Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format_Type := Eval cbn in seq_format_prod CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format_list : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format_Type :=
  (MeasTriggerQuantityCLI_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list__Format := (*Eval compute in *) seq_format CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format_list.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1 z :=
  (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__i1_Threshold_r16 z, (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__reportOnLeave_r16 z, (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__hysteresis_r16 z, (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__timeToTrigger_r16 z, tt)))).
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2 (y : seq_type CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type i0 i1 i2 i3
  end.
Lemma CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1F2_cond (z : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type)
  : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond z ->
  (seq_cond CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1 z)).
intro H. unfold CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond in H. simpl. auto. Qed.
Lemma CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1F2_cond2 (z : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type)
 : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2 (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2F1_cond (y : seq_type CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list)
  : seq_cond CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list y ->
 (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2 y)) /\  CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1 (CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond. simpl in *. auto.
 - simpl. unfold CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format : T_Format CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond :=
        proj2_format  CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__list__Format
    CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1 CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2 CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1F2_cond  CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F1F2_cond2 CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__F2F1_cond.
Opaque CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format.

Definition CLI_EventTriggerConfig_r16__eventId_r16__root__F1 (z : CLI_EventTriggerConfig_r16__eventId_r16__root__Type) : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type := 
  match z with
  | CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16 t => t
  end.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__F2 (y : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type) : CLI_EventTriggerConfig_r16__eventId_r16__root__Type := CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16 y.

Definition CLI_EventTriggerConfig_r16__eventId_r16__root__helper2 : (forall z : CLI_EventTriggerConfig_r16__eventId_r16__root__Type, CLI_EventTriggerConfig_r16__eventId_r16__root__cond z -> CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond (CLI_EventTriggerConfig_r16__eventId_r16__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__helper3 : (forall z : CLI_EventTriggerConfig_r16__eventId_r16__root__Type, CLI_EventTriggerConfig_r16__eventId_r16__root__F2 (CLI_EventTriggerConfig_r16__eventId_r16__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__helper4 : (forall y : CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Type, CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__cond y -> CLI_EventTriggerConfig_r16__eventId_r16__root__cond (CLI_EventTriggerConfig_r16__eventId_r16__root__F2 y) /\  CLI_EventTriggerConfig_r16__eventId_r16__root__F1 (CLI_EventTriggerConfig_r16__eventId_r16__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition CLI_EventTriggerConfig_r16__eventId_r16__root__Format : T_Format CLI_EventTriggerConfig_r16__eventId_r16__root__Type CLI_EventTriggerConfig_r16__eventId_r16__root__cond :=
  proj2_format CLI_EventTriggerConfig_r16__eventId_r16__root__cond CLI_EventTriggerConfig_r16__eventId_r16__root__eventI1_r16__Format CLI_EventTriggerConfig_r16__eventId_r16__root__F1 CLI_EventTriggerConfig_r16__eventId_r16__root__F2 CLI_EventTriggerConfig_r16__eventId_r16__root__helper2 CLI_EventTriggerConfig_r16__eventId_r16__root__helper3 CLI_EventTriggerConfig_r16__eventId_r16__root__helper4.
Opaque CLI_EventTriggerConfig_r16__eventId_r16__root__cond CLI_EventTriggerConfig_r16__eventId_r16__root__Format.

Definition CLI_EventTriggerConfig_r16__eventId_r16__ext__Format : T_Format CLI_EventTriggerConfig_r16__eventId_r16__ext__Type CLI_EventTriggerConfig_r16__eventId_r16__ext__cond := empty_format.
Opaque CLI_EventTriggerConfig_r16__eventId_r16__ext__cond CLI_EventTriggerConfig_r16__eventId_r16__ext__Format.

Definition CLI_EventTriggerConfig_r16__eventId_r16__Format : T_Format CLI_EventTriggerConfig_r16__eventId_r16__Type CLI_EventTriggerConfig_r16__eventId_r16__cond := sum_format CLI_EventTriggerConfig_r16__eventId_r16__root__Format CLI_EventTriggerConfig_r16__eventId_r16__ext__Format.
Opaque CLI_EventTriggerConfig_r16__eventId_r16__cond CLI_EventTriggerConfig_r16__eventId_r16__Format.

Definition CLI_EventTriggerConfig_r16__reportAmount_r16__Format : T_Format CLI_EventTriggerConfig_r16__reportAmount_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CLI_EventTriggerConfig_r16__reportAmount_r16__nat__Format CLI_EventTriggerConfig_r16__reportAmount_r16__F1 CLI_EventTriggerConfig_r16__reportAmount_r16__F2 CLI_EventTriggerConfig_r16__reportAmount_r16__F1F2 CLI_EventTriggerConfig_r16__reportAmount_r16__F2F1.

Opaque CLI_EventTriggerConfig_r16__reportAmount_r16__cond CLI_EventTriggerConfig_r16__reportAmount_r16__Format.

Definition CLI_EventTriggerConfig_r16__maxReportCLI_r16__Format : T_Format Z CLI_EventTriggerConfig_r16__maxReportCLI_r16__cond :=
 ranged_int_format (1) (maxCLI_Report_r16) CLI_EventTriggerConfig_r16__maxReportCLI_r16__helper1 CLI_EventTriggerConfig_r16__maxReportCLI_r16__helper2.

Opaque CLI_EventTriggerConfig_r16__maxReportCLI_r16__cond CLI_EventTriggerConfig_r16__maxReportCLI_r16__Format.


Definition CLI_EventTriggerConfig_r16__root_Format_Type := Eval cbn in seq_format_prod CLI_EventTriggerConfig_r16__root_list.
Definition CLI_EventTriggerConfig_r16__root_Format_list : CLI_EventTriggerConfig_r16__root_Format_Type :=
  (CLI_EventTriggerConfig_r16__eventId_r16__Format, (ReportInterval__Format, (CLI_EventTriggerConfig_r16__reportAmount_r16__Format, (CLI_EventTriggerConfig_r16__maxReportCLI_r16__Format, unit_format)))).

Definition CLI_EventTriggerConfig_r16__ext_Format_Type := Eval cbn in get_formats CLI_EventTriggerConfig_r16__ext_list.
Definition CLI_EventTriggerConfig_r16__ext_Format_list : CLI_EventTriggerConfig_r16__ext_Format_Type :=
  unit__Format.

Definition CLI_EventTriggerConfig_r16__list_type : Set := (seq_type CLI_EventTriggerConfig_r16__root_list) * (seq_ext_type CLI_EventTriggerConfig_r16__ext_list).
Definition CLI_EventTriggerConfig_r16__list_cond (z : CLI_EventTriggerConfig_r16__list_type) : Prop :=
        (seq_cond CLI_EventTriggerConfig_r16__root_list (fst z)) /\ (seq_ext_cond CLI_EventTriggerConfig_r16__ext_list (snd z)).
Definition CLI_EventTriggerConfig_r16__list_format : T_Format CLI_EventTriggerConfig_r16__list_type CLI_EventTriggerConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format CLI_EventTriggerConfig_r16__root_list CLI_EventTriggerConfig_r16__root_Format_list CLI_EventTriggerConfig_r16__ext_list CLI_EventTriggerConfig_r16__ext_Format_list.

Opaque CLI_EventTriggerConfig_r16__list_format.
Definition CLI_EventTriggerConfig_r16__F1 (z : CLI_EventTriggerConfig_r16__Type) : CLI_EventTriggerConfig_r16__list_type :=
  (((CLI_EventTriggerConfig_r16__eventId_r16 z, (CLI_EventTriggerConfig_r16__reportInterval_r16 z, (CLI_EventTriggerConfig_r16__reportAmount_r16 z, (CLI_EventTriggerConfig_r16__maxReportCLI_r16 z, tt))))), (
tt)).
Definition CLI_EventTriggerConfig_r16__F2 (y : CLI_EventTriggerConfig_r16__list_type) : CLI_EventTriggerConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__CLI_EventTriggerConfig_r16__Type j0 j1 j2 j3
  end.
Definition CLI_EventTriggerConfig_r16__helper1 : (forall a : CLI_EventTriggerConfig_r16__Type, CLI_EventTriggerConfig_r16__cond a -> CLI_EventTriggerConfig_r16__list_cond (CLI_EventTriggerConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CLI_EventTriggerConfig_r16__helper2 : (forall a : CLI_EventTriggerConfig_r16__Type, CLI_EventTriggerConfig_r16__F2 (CLI_EventTriggerConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CLI_EventTriggerConfig_r16__helper3 : (forall b : CLI_EventTriggerConfig_r16__list_type, CLI_EventTriggerConfig_r16__list_cond b -> CLI_EventTriggerConfig_r16__cond (CLI_EventTriggerConfig_r16__F2 b) /\ CLI_EventTriggerConfig_r16__F1 (CLI_EventTriggerConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CLI_EventTriggerConfig_r16__cond, CLI_EventTriggerConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CLI_EventTriggerConfig_r16__Format : T_Format CLI_EventTriggerConfig_r16__Type CLI_EventTriggerConfig_r16__cond :=
 proj2_format CLI_EventTriggerConfig_r16__cond CLI_EventTriggerConfig_r16__list_format  CLI_EventTriggerConfig_r16__F1 CLI_EventTriggerConfig_r16__F2 CLI_EventTriggerConfig_r16__helper1 CLI_EventTriggerConfig_r16__helper2 CLI_EventTriggerConfig_r16__helper3.

Opaque CLI_EventTriggerConfig_r16__cond CLI_EventTriggerConfig_r16__Format.

