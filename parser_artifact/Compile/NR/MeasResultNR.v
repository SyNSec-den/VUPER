Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Record MeasResultNR__measResult__cellResults__Type : Set :=
  make__MeasResultNR__measResult__cellResults__Type {
    MeasResultNR__measResult__cellResults__resultsSSB_Cell : option MeasQuantityResults__Type ;
    MeasResultNR__measResult__cellResults__resultsCSI_RS_Cell : option MeasQuantityResults__Type ;
}.
Definition MeasResultNR__measResult__cellResults__list := (
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 nil).
Definition MeasResultNR__measResult__cellResults__cond z := 
  opt_cond MeasQuantityResults__cond (MeasResultNR__measResult__cellResults__resultsSSB_Cell z) /\
  opt_cond MeasQuantityResults__cond (MeasResultNR__measResult__cellResults__resultsCSI_RS_Cell z) /\
  True.

Require Import NR.ResultsPerSSB_IndexList.

Opaque ResultsPerSSB_IndexList__cond ResultsPerSSB_IndexList__Format.

Require Import NR.ResultsPerCSI_RS_IndexList.

Opaque ResultsPerCSI_RS_IndexList__cond ResultsPerCSI_RS_IndexList__Format.

Record MeasResultNR__measResult__rsIndexResults__Type : Set :=
  make__MeasResultNR__measResult__rsIndexResults__Type {
    MeasResultNR__measResult__rsIndexResults__resultsSSB_Indexes : option ResultsPerSSB_IndexList__Type ;
    MeasResultNR__measResult__rsIndexResults__resultsCSI_RS_Indexes : option ResultsPerCSI_RS_IndexList__Type ;
}.
Definition MeasResultNR__measResult__rsIndexResults__list := (
 Opt ResultsPerSSB_IndexList__Type ResultsPerSSB_IndexList__cond ::
 Opt ResultsPerCSI_RS_IndexList__Type ResultsPerCSI_RS_IndexList__cond ::
 nil).
Definition MeasResultNR__measResult__rsIndexResults__cond z := 
  opt_cond ResultsPerSSB_IndexList__cond (MeasResultNR__measResult__rsIndexResults__resultsSSB_Indexes z) /\
  opt_cond ResultsPerCSI_RS_IndexList__cond (MeasResultNR__measResult__rsIndexResults__resultsCSI_RS_Indexes z) /\
  True.

Record MeasResultNR__measResult__Type : Set :=
  make__MeasResultNR__measResult__Type {
    MeasResultNR__measResult__cellResults : MeasResultNR__measResult__cellResults__Type ;
    MeasResultNR__measResult__rsIndexResults : option MeasResultNR__measResult__rsIndexResults__Type ;
}.
Definition MeasResultNR__measResult__list := (
 Nor MeasResultNR__measResult__cellResults__Type MeasResultNR__measResult__cellResults__cond ::
 Opt MeasResultNR__measResult__rsIndexResults__Type MeasResultNR__measResult__rsIndexResults__cond ::
 nil).
Definition MeasResultNR__measResult__cond z := 
  MeasResultNR__measResult__cellResults__cond (MeasResultNR__measResult__cellResults z) /\
  opt_cond MeasResultNR__measResult__rsIndexResults__cond (MeasResultNR__measResult__rsIndexResults z) /\
  True.

Require Import NR.CGI_InfoNR.

Opaque CGI_InfoNR__cond CGI_InfoNR__Format.

Record MeasResultNR__ext0O__Type : Set :=
  make__MeasResultNR__ext0O__Type {
    MeasResultNR__ext0O__cgi_Info : option CGI_InfoNR__Type ;
}.
Definition MeasResultNR__ext0O__list := (
 Opt CGI_InfoNR__Type CGI_InfoNR__cond ::
 nil).
Definition MeasResultNR__ext0O__cond z := 
  opt_cond CGI_InfoNR__cond (MeasResultNR__ext0O__cgi_Info z) /\
  True.

Definition MeasResultNR__ext0__Type := MeasResultNR__ext0O__Type.
Definition MeasResultNR__ext0__cond := MeasResultNR__ext0O__cond.

Inductive MeasResultNR__ext1O__choCandidate_r17__Type : Set :=
 | MeasResultNR__ext1O__choCandidate_r17__true
.
Definition MeasResultNR__ext1O__choCandidate_r17__cond := (fun (_ : MeasResultNR__ext1O__choCandidate_r17__Type) => True).
Lemma MeasResultNR__ext1O__choCandidate_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasResultNR__ext1O__choCandidate_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasResultNR__ext1O__choCandidate_r17__nat__helper.

Definition MeasResultNR__ext1O__choCandidate_r17__F1 t :=
  match t with
  | MeasResultNR__ext1O__choCandidate_r17__true => 0
  end.
Definition MeasResultNR__ext1O__choCandidate_r17__F2 n :=
  match n with
  | 0 => MeasResultNR__ext1O__choCandidate_r17__true
  | _ => MeasResultNR__ext1O__choCandidate_r17__true
  end.
Lemma MeasResultNR__ext1O__choCandidate_r17__F1F2 : forall x : MeasResultNR__ext1O__choCandidate_r17__Type, (MeasResultNR__ext1O__choCandidate_r17__F1 x <= 0) /\ MeasResultNR__ext1O__choCandidate_r17__F2 (MeasResultNR__ext1O__choCandidate_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasResultNR__ext1O__choCandidate_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasResultNR__ext1O__choCandidate_r17__F1 (MeasResultNR__ext1O__choCandidate_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CondTriggerConfig_r16.

Opaque CondTriggerConfig_r16__cond CondTriggerConfig_r16__Format.

Definition MeasResultNR__ext1O__choConfig_r17__Type := list CondTriggerConfig_r16__Type.

Lemma MeasResultNR__ext1O__choConfig_r17__helper1 : (0 <= 1 <= 2)%Z.  lia. Qed.
Lemma MeasResultNR__ext1O__choConfig_r17__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultNR__ext1O__choConfig_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultNR__ext1O__choConfig_r17__cond (z : MeasResultNR__ext1O__choConfig_r17__Type) :=  (1 <= Z.of_nat (length z) <= 2)%Z /\ (list_and CondTriggerConfig_r16__cond z) .

Require Import NR.TimeBetweenEvent_r17.

Opaque TimeBetweenEvent_r17__cond TimeBetweenEvent_r17__Format.

Inductive MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type : Set :=
 | MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condFirstEvent
 | MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condSecondEvent
.
Definition MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__cond := (fun (_ : MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type) => True).
Lemma MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__nat__helper.

Definition MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1 t :=
  match t with
  | MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condFirstEvent => 0
  | MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condSecondEvent => 1
  end.
Definition MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2 n :=
  match n with
  | 0 => MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condFirstEvent
  | 1 => MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condSecondEvent
  | _ => MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condFirstEvent
  end.
Lemma MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1F2 : forall x : MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type, (MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1 x <= 1) /\ MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2 (MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1 x) = x. imp_solve. Qed.
Lemma MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2F1 : forall (y : nat) (H : y <= 1), MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1 (MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2 y) = y. enum_solve H y. Qed.

Record MeasResultNR__ext1O__triggeredEvent_r17__Type : Set :=
  make__MeasResultNR__ext1O__triggeredEvent_r17__Type {
    MeasResultNR__ext1O__triggeredEvent_r17__timeBetweenEvents_r17 : option TimeBetweenEvent_r17__Type ;
    MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent : option MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type ;
}.
Definition MeasResultNR__ext1O__triggeredEvent_r17__list := (
 Opt TimeBetweenEvent_r17__Type TimeBetweenEvent_r17__cond ::
 Opt MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__cond ::
 nil).
Definition MeasResultNR__ext1O__triggeredEvent_r17__cond z := 
  opt_cond TimeBetweenEvent_r17__cond (MeasResultNR__ext1O__triggeredEvent_r17__timeBetweenEvents_r17 z) /\
  opt_cond MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__cond (MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent z) /\
  True.

Record MeasResultNR__ext1O__Type : Set :=
  make__MeasResultNR__ext1O__Type {
    MeasResultNR__ext1O__choCandidate_r17 : option MeasResultNR__ext1O__choCandidate_r17__Type ;
    MeasResultNR__ext1O__choConfig_r17 : option MeasResultNR__ext1O__choConfig_r17__Type ;
    MeasResultNR__ext1O__triggeredEvent_r17 : option MeasResultNR__ext1O__triggeredEvent_r17__Type ;
}.
Definition MeasResultNR__ext1O__list := (
 Opt MeasResultNR__ext1O__choCandidate_r17__Type MeasResultNR__ext1O__choCandidate_r17__cond ::
 Opt MeasResultNR__ext1O__choConfig_r17__Type MeasResultNR__ext1O__choConfig_r17__cond ::
 Opt MeasResultNR__ext1O__triggeredEvent_r17__Type MeasResultNR__ext1O__triggeredEvent_r17__cond ::
 nil).
Definition MeasResultNR__ext1O__cond z := 
  opt_cond MeasResultNR__ext1O__choCandidate_r17__cond (MeasResultNR__ext1O__choCandidate_r17 z) /\
  opt_cond MeasResultNR__ext1O__choConfig_r17__cond (MeasResultNR__ext1O__choConfig_r17 z) /\
  opt_cond MeasResultNR__ext1O__triggeredEvent_r17__cond (MeasResultNR__ext1O__triggeredEvent_r17 z) /\
  True.

Definition MeasResultNR__ext1__Type := MeasResultNR__ext1O__Type.
Definition MeasResultNR__ext1__cond := MeasResultNR__ext1O__cond.

Record MeasResultNR__Type : Set :=
  make__MeasResultNR__Type {
    MeasResultNR__physCellId : option PhysCellId__Type ;
    MeasResultNR__measResult : MeasResultNR__measResult__Type ;
    MeasResultNR__ext0 : option MeasResultNR__ext0__Type ;
    MeasResultNR__ext1 : option MeasResultNR__ext1__Type ;
}.
Definition MeasResultNR__root_list : list seq_elem := (
 Opt PhysCellId__Type PhysCellId__cond ::
 Nor MeasResultNR__measResult__Type MeasResultNR__measResult__cond ::
 nil).
Definition MeasResultNR__ext_list : list typ := (
  typ_cons MeasResultNR__ext0__Type MeasResultNR__ext0__cond ::
  typ_cons MeasResultNR__ext1__Type MeasResultNR__ext1__cond ::
  nil).
Definition MeasResultNR__cond (z : MeasResultNR__Type) := 
(  opt_cond PhysCellId__cond (MeasResultNR__physCellId z) /\
  MeasResultNR__measResult__cond (MeasResultNR__measResult z) /\
  True) /\ 
(  opt_cond MeasResultNR__ext0__cond (MeasResultNR__ext0 z) /\
  opt_cond MeasResultNR__ext1__cond (MeasResultNR__ext1 z) /\
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

Definition MeasResultNR__measResult__cellResults__Format_Type := Eval cbn in seq_format_prod MeasResultNR__measResult__cellResults__list.
Definition MeasResultNR__measResult__cellResults__Format_list : MeasResultNR__measResult__cellResults__Format_Type :=
  (MeasQuantityResults__Format, (MeasQuantityResults__Format, unit_format)).
Definition MeasResultNR__measResult__cellResults__list__Format := (*Eval compute in *) seq_format MeasResultNR__measResult__cellResults__list MeasResultNR__measResult__cellResults__Format_list.
Definition MeasResultNR__measResult__cellResults__F1 z :=
  (MeasResultNR__measResult__cellResults__resultsSSB_Cell z, (MeasResultNR__measResult__cellResults__resultsCSI_RS_Cell z, tt)).
Definition MeasResultNR__measResult__cellResults__F2 (y : seq_type MeasResultNR__measResult__cellResults__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultNR__measResult__cellResults__Type i0 i1
  end.
Lemma MeasResultNR__measResult__cellResults__F1F2_cond (z : MeasResultNR__measResult__cellResults__Type)
  : MeasResultNR__measResult__cellResults__cond z ->
  (seq_cond MeasResultNR__measResult__cellResults__list (MeasResultNR__measResult__cellResults__F1 z)).
intro H. unfold MeasResultNR__measResult__cellResults__cond in H. simpl. auto. Qed.
Lemma MeasResultNR__measResult__cellResults__F1F2_cond2 (z : MeasResultNR__measResult__cellResults__Type)
 : MeasResultNR__measResult__cellResults__F2 (MeasResultNR__measResult__cellResults__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultNR__measResult__cellResults__F2F1_cond (y : seq_type MeasResultNR__measResult__cellResults__list)
  : seq_cond MeasResultNR__measResult__cellResults__list y ->
 (MeasResultNR__measResult__cellResults__cond (MeasResultNR__measResult__cellResults__F2 y)) /\  MeasResultNR__measResult__cellResults__F1 (MeasResultNR__measResult__cellResults__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultNR__measResult__cellResults__cond. simpl in *. auto.
 - simpl. unfold MeasResultNR__measResult__cellResults__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultNR__measResult__cellResults__Format : T_Format MeasResultNR__measResult__cellResults__Type MeasResultNR__measResult__cellResults__cond :=
        proj2_format  MeasResultNR__measResult__cellResults__cond MeasResultNR__measResult__cellResults__list__Format
    MeasResultNR__measResult__cellResults__F1 MeasResultNR__measResult__cellResults__F2 MeasResultNR__measResult__cellResults__F1F2_cond  MeasResultNR__measResult__cellResults__F1F2_cond2 MeasResultNR__measResult__cellResults__F2F1_cond.
Opaque MeasResultNR__measResult__cellResults__cond MeasResultNR__measResult__cellResults__Format.


Definition MeasResultNR__measResult__rsIndexResults__Format_Type := Eval cbn in seq_format_prod MeasResultNR__measResult__rsIndexResults__list.
Definition MeasResultNR__measResult__rsIndexResults__Format_list : MeasResultNR__measResult__rsIndexResults__Format_Type :=
  (ResultsPerSSB_IndexList__Format, (ResultsPerCSI_RS_IndexList__Format, unit_format)).
Definition MeasResultNR__measResult__rsIndexResults__list__Format := (*Eval compute in *) seq_format MeasResultNR__measResult__rsIndexResults__list MeasResultNR__measResult__rsIndexResults__Format_list.
Definition MeasResultNR__measResult__rsIndexResults__F1 z :=
  (MeasResultNR__measResult__rsIndexResults__resultsSSB_Indexes z, (MeasResultNR__measResult__rsIndexResults__resultsCSI_RS_Indexes z, tt)).
Definition MeasResultNR__measResult__rsIndexResults__F2 (y : seq_type MeasResultNR__measResult__rsIndexResults__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultNR__measResult__rsIndexResults__Type i0 i1
  end.
Lemma MeasResultNR__measResult__rsIndexResults__F1F2_cond (z : MeasResultNR__measResult__rsIndexResults__Type)
  : MeasResultNR__measResult__rsIndexResults__cond z ->
  (seq_cond MeasResultNR__measResult__rsIndexResults__list (MeasResultNR__measResult__rsIndexResults__F1 z)).
intro H. unfold MeasResultNR__measResult__rsIndexResults__cond in H. simpl. auto. Qed.
Lemma MeasResultNR__measResult__rsIndexResults__F1F2_cond2 (z : MeasResultNR__measResult__rsIndexResults__Type)
 : MeasResultNR__measResult__rsIndexResults__F2 (MeasResultNR__measResult__rsIndexResults__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultNR__measResult__rsIndexResults__F2F1_cond (y : seq_type MeasResultNR__measResult__rsIndexResults__list)
  : seq_cond MeasResultNR__measResult__rsIndexResults__list y ->
 (MeasResultNR__measResult__rsIndexResults__cond (MeasResultNR__measResult__rsIndexResults__F2 y)) /\  MeasResultNR__measResult__rsIndexResults__F1 (MeasResultNR__measResult__rsIndexResults__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultNR__measResult__rsIndexResults__cond. simpl in *. auto.
 - simpl. unfold MeasResultNR__measResult__rsIndexResults__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultNR__measResult__rsIndexResults__Format : T_Format MeasResultNR__measResult__rsIndexResults__Type MeasResultNR__measResult__rsIndexResults__cond :=
        proj2_format  MeasResultNR__measResult__rsIndexResults__cond MeasResultNR__measResult__rsIndexResults__list__Format
    MeasResultNR__measResult__rsIndexResults__F1 MeasResultNR__measResult__rsIndexResults__F2 MeasResultNR__measResult__rsIndexResults__F1F2_cond  MeasResultNR__measResult__rsIndexResults__F1F2_cond2 MeasResultNR__measResult__rsIndexResults__F2F1_cond.
Opaque MeasResultNR__measResult__rsIndexResults__cond MeasResultNR__measResult__rsIndexResults__Format.


Definition MeasResultNR__measResult__Format_Type := Eval cbn in seq_format_prod MeasResultNR__measResult__list.
Definition MeasResultNR__measResult__Format_list : MeasResultNR__measResult__Format_Type :=
  (MeasResultNR__measResult__cellResults__Format, (MeasResultNR__measResult__rsIndexResults__Format, unit_format)).
Definition MeasResultNR__measResult__list__Format := (*Eval compute in *) seq_format MeasResultNR__measResult__list MeasResultNR__measResult__Format_list.
Definition MeasResultNR__measResult__F1 z :=
  (MeasResultNR__measResult__cellResults z, (MeasResultNR__measResult__rsIndexResults z, tt)).
Definition MeasResultNR__measResult__F2 (y : seq_type MeasResultNR__measResult__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultNR__measResult__Type i0 i1
  end.
Lemma MeasResultNR__measResult__F1F2_cond (z : MeasResultNR__measResult__Type)
  : MeasResultNR__measResult__cond z ->
  (seq_cond MeasResultNR__measResult__list (MeasResultNR__measResult__F1 z)).
intro H. unfold MeasResultNR__measResult__cond in H. simpl. auto. Qed.
Lemma MeasResultNR__measResult__F1F2_cond2 (z : MeasResultNR__measResult__Type)
 : MeasResultNR__measResult__F2 (MeasResultNR__measResult__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultNR__measResult__F2F1_cond (y : seq_type MeasResultNR__measResult__list)
  : seq_cond MeasResultNR__measResult__list y ->
 (MeasResultNR__measResult__cond (MeasResultNR__measResult__F2 y)) /\  MeasResultNR__measResult__F1 (MeasResultNR__measResult__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultNR__measResult__cond. simpl in *. auto.
 - simpl. unfold MeasResultNR__measResult__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultNR__measResult__Format : T_Format MeasResultNR__measResult__Type MeasResultNR__measResult__cond :=
        proj2_format  MeasResultNR__measResult__cond MeasResultNR__measResult__list__Format
    MeasResultNR__measResult__F1 MeasResultNR__measResult__F2 MeasResultNR__measResult__F1F2_cond  MeasResultNR__measResult__F1F2_cond2 MeasResultNR__measResult__F2F1_cond.
Opaque MeasResultNR__measResult__cond MeasResultNR__measResult__Format.


Definition MeasResultNR__ext0O__Format_Type := Eval cbn in seq_format_prod MeasResultNR__ext0O__list.
Definition MeasResultNR__ext0O__Format_list : MeasResultNR__ext0O__Format_Type :=
  (CGI_InfoNR__Format, unit_format).
Definition MeasResultNR__ext0O__list__Format := (*Eval compute in *) seq_format MeasResultNR__ext0O__list MeasResultNR__ext0O__Format_list.
Definition MeasResultNR__ext0O__F1 z :=
  (MeasResultNR__ext0O__cgi_Info z, tt).
Definition MeasResultNR__ext0O__F2 (y : seq_type MeasResultNR__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MeasResultNR__ext0O__Type i0
  end.
Lemma MeasResultNR__ext0O__F1F2_cond (z : MeasResultNR__ext0O__Type)
  : MeasResultNR__ext0O__cond z ->
  (seq_cond MeasResultNR__ext0O__list (MeasResultNR__ext0O__F1 z)).
intro H. unfold MeasResultNR__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasResultNR__ext0O__F1F2_cond2 (z : MeasResultNR__ext0O__Type)
 : MeasResultNR__ext0O__F2 (MeasResultNR__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultNR__ext0O__F2F1_cond (y : seq_type MeasResultNR__ext0O__list)
  : seq_cond MeasResultNR__ext0O__list y ->
 (MeasResultNR__ext0O__cond (MeasResultNR__ext0O__F2 y)) /\  MeasResultNR__ext0O__F1 (MeasResultNR__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultNR__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasResultNR__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultNR__ext0O__Format : T_Format MeasResultNR__ext0O__Type MeasResultNR__ext0O__cond :=
        proj2_format  MeasResultNR__ext0O__cond MeasResultNR__ext0O__list__Format
    MeasResultNR__ext0O__F1 MeasResultNR__ext0O__F2 MeasResultNR__ext0O__F1F2_cond  MeasResultNR__ext0O__F1F2_cond2 MeasResultNR__ext0O__F2F1_cond.
Opaque MeasResultNR__ext0O__cond MeasResultNR__ext0O__Format.

Definition MeasResultNR__ext0__check_all_none (b : MeasResultNR__ext0O__Type) : bool :=
match b with 
  | make__MeasResultNR__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MeasResultNR__ext0__Format : T_Format MeasResultNR__ext0__Type MeasResultNR__ext0__cond :=
  restrict_add_format MeasResultNR__ext0__check_all_none MeasResultNR__ext0O__Format.

Opaque MeasResultNR__ext0__cond MeasResultNR__ext0__Format.

Definition MeasResultNR__ext1O__choCandidate_r17__Format : T_Format MeasResultNR__ext1O__choCandidate_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasResultNR__ext1O__choCandidate_r17__nat__Format MeasResultNR__ext1O__choCandidate_r17__F1 MeasResultNR__ext1O__choCandidate_r17__F2 MeasResultNR__ext1O__choCandidate_r17__F1F2 MeasResultNR__ext1O__choCandidate_r17__F2F1.

Opaque MeasResultNR__ext1O__choCandidate_r17__cond MeasResultNR__ext1O__choCandidate_r17__Format.

Definition MeasResultNR__ext1O__choConfig_r17__Format : T_Format MeasResultNR__ext1O__choConfig_r17__Type MeasResultNR__ext1O__choConfig_r17__cond := seq_of_format CondTriggerConfig_r16__Format 1 2 MeasResultNR__ext1O__choConfig_r17__helper1 MeasResultNR__ext1O__choConfig_r17__helper2.

Opaque MeasResultNR__ext1O__choConfig_r17__cond MeasResultNR__ext1O__choConfig_r17__Format.

Definition MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Format : T_Format MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__nat__Format MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1 MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2 MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1F2 MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2F1.

Opaque MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__cond MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Format.


Definition MeasResultNR__ext1O__triggeredEvent_r17__Format_Type := Eval cbn in seq_format_prod MeasResultNR__ext1O__triggeredEvent_r17__list.
Definition MeasResultNR__ext1O__triggeredEvent_r17__Format_list : MeasResultNR__ext1O__triggeredEvent_r17__Format_Type :=
  (TimeBetweenEvent_r17__Format, (MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Format, unit_format)).
Definition MeasResultNR__ext1O__triggeredEvent_r17__list__Format := (*Eval compute in *) seq_format MeasResultNR__ext1O__triggeredEvent_r17__list MeasResultNR__ext1O__triggeredEvent_r17__Format_list.
Definition MeasResultNR__ext1O__triggeredEvent_r17__F1 z :=
  (MeasResultNR__ext1O__triggeredEvent_r17__timeBetweenEvents_r17 z, (MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent z, tt)).
Definition MeasResultNR__ext1O__triggeredEvent_r17__F2 (y : seq_type MeasResultNR__ext1O__triggeredEvent_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultNR__ext1O__triggeredEvent_r17__Type i0 i1
  end.
Lemma MeasResultNR__ext1O__triggeredEvent_r17__F1F2_cond (z : MeasResultNR__ext1O__triggeredEvent_r17__Type)
  : MeasResultNR__ext1O__triggeredEvent_r17__cond z ->
  (seq_cond MeasResultNR__ext1O__triggeredEvent_r17__list (MeasResultNR__ext1O__triggeredEvent_r17__F1 z)).
intro H. unfold MeasResultNR__ext1O__triggeredEvent_r17__cond in H. simpl. auto. Qed.
Lemma MeasResultNR__ext1O__triggeredEvent_r17__F1F2_cond2 (z : MeasResultNR__ext1O__triggeredEvent_r17__Type)
 : MeasResultNR__ext1O__triggeredEvent_r17__F2 (MeasResultNR__ext1O__triggeredEvent_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultNR__ext1O__triggeredEvent_r17__F2F1_cond (y : seq_type MeasResultNR__ext1O__triggeredEvent_r17__list)
  : seq_cond MeasResultNR__ext1O__triggeredEvent_r17__list y ->
 (MeasResultNR__ext1O__triggeredEvent_r17__cond (MeasResultNR__ext1O__triggeredEvent_r17__F2 y)) /\  MeasResultNR__ext1O__triggeredEvent_r17__F1 (MeasResultNR__ext1O__triggeredEvent_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultNR__ext1O__triggeredEvent_r17__cond. simpl in *. auto.
 - simpl. unfold MeasResultNR__ext1O__triggeredEvent_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultNR__ext1O__triggeredEvent_r17__Format : T_Format MeasResultNR__ext1O__triggeredEvent_r17__Type MeasResultNR__ext1O__triggeredEvent_r17__cond :=
        proj2_format  MeasResultNR__ext1O__triggeredEvent_r17__cond MeasResultNR__ext1O__triggeredEvent_r17__list__Format
    MeasResultNR__ext1O__triggeredEvent_r17__F1 MeasResultNR__ext1O__triggeredEvent_r17__F2 MeasResultNR__ext1O__triggeredEvent_r17__F1F2_cond  MeasResultNR__ext1O__triggeredEvent_r17__F1F2_cond2 MeasResultNR__ext1O__triggeredEvent_r17__F2F1_cond.
Opaque MeasResultNR__ext1O__triggeredEvent_r17__cond MeasResultNR__ext1O__triggeredEvent_r17__Format.


Definition MeasResultNR__ext1O__Format_Type := Eval cbn in seq_format_prod MeasResultNR__ext1O__list.
Definition MeasResultNR__ext1O__Format_list : MeasResultNR__ext1O__Format_Type :=
  (MeasResultNR__ext1O__choCandidate_r17__Format, (MeasResultNR__ext1O__choConfig_r17__Format, (MeasResultNR__ext1O__triggeredEvent_r17__Format, unit_format))).
Definition MeasResultNR__ext1O__list__Format := (*Eval compute in *) seq_format MeasResultNR__ext1O__list MeasResultNR__ext1O__Format_list.
Definition MeasResultNR__ext1O__F1 z :=
  (MeasResultNR__ext1O__choCandidate_r17 z, (MeasResultNR__ext1O__choConfig_r17 z, (MeasResultNR__ext1O__triggeredEvent_r17 z, tt))).
Definition MeasResultNR__ext1O__F2 (y : seq_type MeasResultNR__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasResultNR__ext1O__Type i0 i1 i2
  end.
Lemma MeasResultNR__ext1O__F1F2_cond (z : MeasResultNR__ext1O__Type)
  : MeasResultNR__ext1O__cond z ->
  (seq_cond MeasResultNR__ext1O__list (MeasResultNR__ext1O__F1 z)).
intro H. unfold MeasResultNR__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasResultNR__ext1O__F1F2_cond2 (z : MeasResultNR__ext1O__Type)
 : MeasResultNR__ext1O__F2 (MeasResultNR__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultNR__ext1O__F2F1_cond (y : seq_type MeasResultNR__ext1O__list)
  : seq_cond MeasResultNR__ext1O__list y ->
 (MeasResultNR__ext1O__cond (MeasResultNR__ext1O__F2 y)) /\  MeasResultNR__ext1O__F1 (MeasResultNR__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultNR__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasResultNR__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultNR__ext1O__Format : T_Format MeasResultNR__ext1O__Type MeasResultNR__ext1O__cond :=
        proj2_format  MeasResultNR__ext1O__cond MeasResultNR__ext1O__list__Format
    MeasResultNR__ext1O__F1 MeasResultNR__ext1O__F2 MeasResultNR__ext1O__F1F2_cond  MeasResultNR__ext1O__F1F2_cond2 MeasResultNR__ext1O__F2F1_cond.
Opaque MeasResultNR__ext1O__cond MeasResultNR__ext1O__Format.

Definition MeasResultNR__ext1__check_all_none (b : MeasResultNR__ext1O__Type) : bool :=
match b with 
  | make__MeasResultNR__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition MeasResultNR__ext1__Format : T_Format MeasResultNR__ext1__Type MeasResultNR__ext1__cond :=
  restrict_add_format MeasResultNR__ext1__check_all_none MeasResultNR__ext1O__Format.

Opaque MeasResultNR__ext1__cond MeasResultNR__ext1__Format.


Definition MeasResultNR__root_Format_Type := Eval cbn in seq_format_prod MeasResultNR__root_list.
Definition MeasResultNR__root_Format_list : MeasResultNR__root_Format_Type :=
  (PhysCellId__Format, (MeasResultNR__measResult__Format, unit_format)).

Definition MeasResultNR__ext_Format_Type := Eval cbn in get_formats MeasResultNR__ext_list.
Definition MeasResultNR__ext_Format_list : MeasResultNR__ext_Format_Type :=
  (MeasResultNR__ext0__Format, (MeasResultNR__ext1__Format, unit__Format)).

Definition MeasResultNR__list_type : Set := (seq_type MeasResultNR__root_list) * (seq_ext_type MeasResultNR__ext_list).
Definition MeasResultNR__list_cond (z : MeasResultNR__list_type) : Prop :=
        (seq_cond MeasResultNR__root_list (fst z)) /\ (seq_ext_cond MeasResultNR__ext_list (snd z)).
Definition MeasResultNR__list_format : T_Format MeasResultNR__list_type MeasResultNR__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultNR__root_list MeasResultNR__root_Format_list MeasResultNR__ext_list MeasResultNR__ext_Format_list.

Opaque MeasResultNR__list_format.
Definition MeasResultNR__F1 (z : MeasResultNR__Type) : MeasResultNR__list_type :=
  (((MeasResultNR__physCellId z, (MeasResultNR__measResult z, tt))), (
(MeasResultNR__ext0 z, (MeasResultNR__ext1 z, tt)))).
Definition MeasResultNR__F2 (y : MeasResultNR__list_type) : MeasResultNR__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, _)))=>
    make__MeasResultNR__Type j0 j1 i0 i1
  end.
Definition MeasResultNR__helper1 : (forall a : MeasResultNR__Type, MeasResultNR__cond a -> MeasResultNR__list_cond (MeasResultNR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultNR__helper2 : (forall a : MeasResultNR__Type, MeasResultNR__F2 (MeasResultNR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultNR__helper3 : (forall b : MeasResultNR__list_type, MeasResultNR__list_cond b -> MeasResultNR__cond (MeasResultNR__F2 b) /\ MeasResultNR__F1 (MeasResultNR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultNR__cond, MeasResultNR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultNR__Format : T_Format MeasResultNR__Type MeasResultNR__cond :=
 proj2_format MeasResultNR__cond MeasResultNR__list_format  MeasResultNR__F1 MeasResultNR__F2 MeasResultNR__helper1 MeasResultNR__helper2 MeasResultNR__helper3.

Opaque MeasResultNR__cond MeasResultNR__Format.

