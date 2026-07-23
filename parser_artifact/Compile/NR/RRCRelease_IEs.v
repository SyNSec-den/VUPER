Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RedirectedCarrierInfo.

Opaque RedirectedCarrierInfo__cond RedirectedCarrierInfo__Format.

Require Import NR.CellReselectionPriorities.

Opaque CellReselectionPriorities__cond CellReselectionPriorities__Format.

Require Import NR.SuspendConfig.

Opaque SuspendConfig__cond SuspendConfig__Format.

Inductive RRCRelease_IEs__deprioritisationReq__deprioritisationType__Type : Set :=
 | RRCRelease_IEs__deprioritisationReq__deprioritisationType__frequency
 | RRCRelease_IEs__deprioritisationReq__deprioritisationType__nr
.
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationType__cond := (fun (_ : RRCRelease_IEs__deprioritisationReq__deprioritisationType__Type) => True).
Lemma RRCRelease_IEs__deprioritisationReq__deprioritisationType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RRCRelease_IEs__deprioritisationReq__deprioritisationType__nat__helper.

Definition RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1 t :=
  match t with
  | RRCRelease_IEs__deprioritisationReq__deprioritisationType__frequency => 0
  | RRCRelease_IEs__deprioritisationReq__deprioritisationType__nr => 1
  end.
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationType__F2 n :=
  match n with
  | 0 => RRCRelease_IEs__deprioritisationReq__deprioritisationType__frequency
  | 1 => RRCRelease_IEs__deprioritisationReq__deprioritisationType__nr
  | _ => RRCRelease_IEs__deprioritisationReq__deprioritisationType__frequency
  end.
Lemma RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1F2 : forall x : RRCRelease_IEs__deprioritisationReq__deprioritisationType__Type, (RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1 x <= 1) /\ RRCRelease_IEs__deprioritisationReq__deprioritisationType__F2 (RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1 x) = x. imp_solve. Qed.
Lemma RRCRelease_IEs__deprioritisationReq__deprioritisationType__F2F1 : forall (y : nat) (H : y <= 1), RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1 (RRCRelease_IEs__deprioritisationReq__deprioritisationType__F2 y) = y. enum_solve H y. Qed.

Inductive RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Type : Set :=
 | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min5
 | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min10
 | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min15
 | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min30
.
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__cond := (fun (_ : RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Type) => True).
Lemma RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__nat__helper.

Definition RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1 t :=
  match t with
  | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min5 => 0
  | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min10 => 1
  | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min15 => 2
  | RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min30 => 3
  end.
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F2 n :=
  match n with
  | 0 => RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min5
  | 1 => RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min10
  | 2 => RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min15
  | 3 => RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min30
  | _ => RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__min5
  end.
Lemma RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1F2 : forall x : RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Type, (RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1 x <= 3) /\ RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F2 (RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1 x) = x. imp_solve. Qed.
Lemma RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F2F1 : forall (y : nat) (H : y <= 3), RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1 (RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F2 y) = y. enum_solve H y. Qed.

Record RRCRelease_IEs__deprioritisationReq__Type : Set :=
  make__RRCRelease_IEs__deprioritisationReq__Type {
    RRCRelease_IEs__deprioritisationReq__deprioritisationType : RRCRelease_IEs__deprioritisationReq__deprioritisationType__Type ;
    RRCRelease_IEs__deprioritisationReq__deprioritisationTimer : RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Type ;
}.
Definition RRCRelease_IEs__deprioritisationReq__list := (
 Nor RRCRelease_IEs__deprioritisationReq__deprioritisationType__Type RRCRelease_IEs__deprioritisationReq__deprioritisationType__cond ::
 Nor RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Type RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__cond ::
 nil).
Definition RRCRelease_IEs__deprioritisationReq__cond z := 
  RRCRelease_IEs__deprioritisationReq__deprioritisationType__cond (RRCRelease_IEs__deprioritisationReq__deprioritisationType z) /\
  RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__cond (RRCRelease_IEs__deprioritisationReq__deprioritisationTimer z) /\
  True.

Require Import NR.RRCRelease_v1540_IEs.

Opaque RRCRelease_v1540_IEs__cond RRCRelease_v1540_IEs__Format.

Record RRCRelease_IEs__Type : Set :=
  make__RRCRelease_IEs__Type {
    RRCRelease_IEs__redirectedCarrierInfo : option RedirectedCarrierInfo__Type ;
    RRCRelease_IEs__cellReselectionPriorities : option CellReselectionPriorities__Type ;
    RRCRelease_IEs__suspendConfig : option SuspendConfig__Type ;
    RRCRelease_IEs__deprioritisationReq : option RRCRelease_IEs__deprioritisationReq__Type ;
    RRCRelease_IEs__lateNonCriticalExtension : option octet_string ;
    RRCRelease_IEs__nonCriticalExtension : option RRCRelease_v1540_IEs__Type ;
}.
Definition RRCRelease_IEs__list := (
 Opt RedirectedCarrierInfo__Type RedirectedCarrierInfo__cond ::
 Opt CellReselectionPriorities__Type CellReselectionPriorities__cond ::
 Opt SuspendConfig__Type SuspendConfig__cond ::
 Opt RRCRelease_IEs__deprioritisationReq__Type RRCRelease_IEs__deprioritisationReq__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCRelease_v1540_IEs__Type RRCRelease_v1540_IEs__cond ::
 nil).
Definition RRCRelease_IEs__cond z := 
  opt_cond RedirectedCarrierInfo__cond (RRCRelease_IEs__redirectedCarrierInfo z) /\
  opt_cond CellReselectionPriorities__cond (RRCRelease_IEs__cellReselectionPriorities z) /\
  opt_cond SuspendConfig__cond (RRCRelease_IEs__suspendConfig z) /\
  opt_cond RRCRelease_IEs__deprioritisationReq__cond (RRCRelease_IEs__deprioritisationReq z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCRelease_IEs__lateNonCriticalExtension z) /\
  opt_cond RRCRelease_v1540_IEs__cond (RRCRelease_IEs__nonCriticalExtension z) /\
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
Definition RRCRelease_IEs__deprioritisationReq__deprioritisationType__Format : T_Format RRCRelease_IEs__deprioritisationReq__deprioritisationType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCRelease_IEs__deprioritisationReq__deprioritisationType__nat__Format RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1 RRCRelease_IEs__deprioritisationReq__deprioritisationType__F2 RRCRelease_IEs__deprioritisationReq__deprioritisationType__F1F2 RRCRelease_IEs__deprioritisationReq__deprioritisationType__F2F1.

Opaque RRCRelease_IEs__deprioritisationReq__deprioritisationType__cond RRCRelease_IEs__deprioritisationReq__deprioritisationType__Format.

Definition RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Format : T_Format RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__nat__Format RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1 RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F2 RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F1F2 RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__F2F1.

Opaque RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__cond RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Format.


Definition RRCRelease_IEs__deprioritisationReq__Format_Type := Eval cbn in seq_format_prod RRCRelease_IEs__deprioritisationReq__list.
Definition RRCRelease_IEs__deprioritisationReq__Format_list : RRCRelease_IEs__deprioritisationReq__Format_Type :=
  (RRCRelease_IEs__deprioritisationReq__deprioritisationType__Format, (RRCRelease_IEs__deprioritisationReq__deprioritisationTimer__Format, unit_format)).
Definition RRCRelease_IEs__deprioritisationReq__list__Format := (*Eval compute in *) seq_format RRCRelease_IEs__deprioritisationReq__list RRCRelease_IEs__deprioritisationReq__Format_list.
Definition RRCRelease_IEs__deprioritisationReq__F1 z :=
  (RRCRelease_IEs__deprioritisationReq__deprioritisationType z, (RRCRelease_IEs__deprioritisationReq__deprioritisationTimer z, tt)).
Definition RRCRelease_IEs__deprioritisationReq__F2 (y : seq_type RRCRelease_IEs__deprioritisationReq__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCRelease_IEs__deprioritisationReq__Type i0 i1
  end.
Lemma RRCRelease_IEs__deprioritisationReq__F1F2_cond (z : RRCRelease_IEs__deprioritisationReq__Type)
  : RRCRelease_IEs__deprioritisationReq__cond z ->
  (seq_cond RRCRelease_IEs__deprioritisationReq__list (RRCRelease_IEs__deprioritisationReq__F1 z)).
intro H. unfold RRCRelease_IEs__deprioritisationReq__cond in H. simpl. auto. Qed.
Lemma RRCRelease_IEs__deprioritisationReq__F1F2_cond2 (z : RRCRelease_IEs__deprioritisationReq__Type)
 : RRCRelease_IEs__deprioritisationReq__F2 (RRCRelease_IEs__deprioritisationReq__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCRelease_IEs__deprioritisationReq__F2F1_cond (y : seq_type RRCRelease_IEs__deprioritisationReq__list)
  : seq_cond RRCRelease_IEs__deprioritisationReq__list y ->
 (RRCRelease_IEs__deprioritisationReq__cond (RRCRelease_IEs__deprioritisationReq__F2 y)) /\  RRCRelease_IEs__deprioritisationReq__F1 (RRCRelease_IEs__deprioritisationReq__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCRelease_IEs__deprioritisationReq__cond. simpl in *. auto.
 - simpl. unfold RRCRelease_IEs__deprioritisationReq__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCRelease_IEs__deprioritisationReq__Format : T_Format RRCRelease_IEs__deprioritisationReq__Type RRCRelease_IEs__deprioritisationReq__cond :=
        proj2_format  RRCRelease_IEs__deprioritisationReq__cond RRCRelease_IEs__deprioritisationReq__list__Format
    RRCRelease_IEs__deprioritisationReq__F1 RRCRelease_IEs__deprioritisationReq__F2 RRCRelease_IEs__deprioritisationReq__F1F2_cond  RRCRelease_IEs__deprioritisationReq__F1F2_cond2 RRCRelease_IEs__deprioritisationReq__F2F1_cond.
Opaque RRCRelease_IEs__deprioritisationReq__cond RRCRelease_IEs__deprioritisationReq__Format.


Definition RRCRelease_IEs__Format_Type := Eval cbn in seq_format_prod RRCRelease_IEs__list.
Definition RRCRelease_IEs__Format_list : RRCRelease_IEs__Format_Type :=
  (RedirectedCarrierInfo__Format, (CellReselectionPriorities__Format, (SuspendConfig__Format, (RRCRelease_IEs__deprioritisationReq__Format, (octet_string_nc__Format, (RRCRelease_v1540_IEs__Format, unit_format)))))).
Definition RRCRelease_IEs__list__Format := (*Eval compute in *) seq_format RRCRelease_IEs__list RRCRelease_IEs__Format_list.
Definition RRCRelease_IEs__F1 z :=
  (RRCRelease_IEs__redirectedCarrierInfo z, (RRCRelease_IEs__cellReselectionPriorities z, (RRCRelease_IEs__suspendConfig z, (RRCRelease_IEs__deprioritisationReq z, (RRCRelease_IEs__lateNonCriticalExtension z, (RRCRelease_IEs__nonCriticalExtension z, tt)))))).
Definition RRCRelease_IEs__F2 (y : seq_type RRCRelease_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__RRCRelease_IEs__Type i0 i1 i2 i3 i4 i5
  end.
Lemma RRCRelease_IEs__F1F2_cond (z : RRCRelease_IEs__Type)
  : RRCRelease_IEs__cond z ->
  (seq_cond RRCRelease_IEs__list (RRCRelease_IEs__F1 z)).
intro H. unfold RRCRelease_IEs__cond in H. simpl. auto. Qed.
Lemma RRCRelease_IEs__F1F2_cond2 (z : RRCRelease_IEs__Type)
 : RRCRelease_IEs__F2 (RRCRelease_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCRelease_IEs__F2F1_cond (y : seq_type RRCRelease_IEs__list)
  : seq_cond RRCRelease_IEs__list y ->
 (RRCRelease_IEs__cond (RRCRelease_IEs__F2 y)) /\  RRCRelease_IEs__F1 (RRCRelease_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCRelease_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCRelease_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCRelease_IEs__Format : T_Format RRCRelease_IEs__Type RRCRelease_IEs__cond :=
        proj2_format  RRCRelease_IEs__cond RRCRelease_IEs__list__Format
    RRCRelease_IEs__F1 RRCRelease_IEs__F2 RRCRelease_IEs__F1F2_cond  RRCRelease_IEs__F1F2_cond2 RRCRelease_IEs__F2F1_cond.
Opaque RRCRelease_IEs__cond RRCRelease_IEs__Format.

