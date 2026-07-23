Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CarrierFreqListMBS_r17.

Opaque CarrierFreqListMBS_r17__cond CarrierFreqListMBS_r17__Format.

Inductive MBSInterestIndication_r17_IEs__mbs_Priority_r17__Type : Set :=
 | MBSInterestIndication_r17_IEs__mbs_Priority_r17__true
.
Definition MBSInterestIndication_r17_IEs__mbs_Priority_r17__cond := (fun (_ : MBSInterestIndication_r17_IEs__mbs_Priority_r17__Type) => True).
Lemma MBSInterestIndication_r17_IEs__mbs_Priority_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MBSInterestIndication_r17_IEs__mbs_Priority_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MBSInterestIndication_r17_IEs__mbs_Priority_r17__nat__helper.

Definition MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1 t :=
  match t with
  | MBSInterestIndication_r17_IEs__mbs_Priority_r17__true => 0
  end.
Definition MBSInterestIndication_r17_IEs__mbs_Priority_r17__F2 n :=
  match n with
  | 0 => MBSInterestIndication_r17_IEs__mbs_Priority_r17__true
  | _ => MBSInterestIndication_r17_IEs__mbs_Priority_r17__true
  end.
Lemma MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1F2 : forall x : MBSInterestIndication_r17_IEs__mbs_Priority_r17__Type, (MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1 x <= 0) /\ MBSInterestIndication_r17_IEs__mbs_Priority_r17__F2 (MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1 x) = x. imp_solve. Qed.
Lemma MBSInterestIndication_r17_IEs__mbs_Priority_r17__F2F1 : forall (y : nat) (H : y <= 0), MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1 (MBSInterestIndication_r17_IEs__mbs_Priority_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MBS_ServiceList_r17.

Opaque MBS_ServiceList_r17__cond MBS_ServiceList_r17__Format.

Record MBSInterestIndication_r17_IEs__nonCriticalExtension__Type : Set := make__MBSInterestIndication_r17_IEs__nonCriticalExtension__Type {}.
Definition MBSInterestIndication_r17_IEs__nonCriticalExtension__cond (z : MBSInterestIndication_r17_IEs__nonCriticalExtension__Type) := True.
Record MBSInterestIndication_r17_IEs__Type : Set :=
  make__MBSInterestIndication_r17_IEs__Type {
    MBSInterestIndication_r17_IEs__mbs_FreqList_r17 : option CarrierFreqListMBS_r17__Type ;
    MBSInterestIndication_r17_IEs__mbs_Priority_r17 : option MBSInterestIndication_r17_IEs__mbs_Priority_r17__Type ;
    MBSInterestIndication_r17_IEs__mbs_ServiceList_r17 : option MBS_ServiceList_r17__Type ;
    MBSInterestIndication_r17_IEs__lateNonCriticalExtension : option octet_string ;
    MBSInterestIndication_r17_IEs__nonCriticalExtension : option MBSInterestIndication_r17_IEs__nonCriticalExtension__Type ;
}.
Definition MBSInterestIndication_r17_IEs__list := (
 Opt CarrierFreqListMBS_r17__Type CarrierFreqListMBS_r17__cond ::
 Opt MBSInterestIndication_r17_IEs__mbs_Priority_r17__Type MBSInterestIndication_r17_IEs__mbs_Priority_r17__cond ::
 Opt MBS_ServiceList_r17__Type MBS_ServiceList_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MBSInterestIndication_r17_IEs__nonCriticalExtension__Type MBSInterestIndication_r17_IEs__nonCriticalExtension__cond ::
 nil).
Definition MBSInterestIndication_r17_IEs__cond z := 
  opt_cond CarrierFreqListMBS_r17__cond (MBSInterestIndication_r17_IEs__mbs_FreqList_r17 z) /\
  opt_cond MBSInterestIndication_r17_IEs__mbs_Priority_r17__cond (MBSInterestIndication_r17_IEs__mbs_Priority_r17 z) /\
  opt_cond MBS_ServiceList_r17__cond (MBSInterestIndication_r17_IEs__mbs_ServiceList_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MBSInterestIndication_r17_IEs__lateNonCriticalExtension z) /\
  opt_cond MBSInterestIndication_r17_IEs__nonCriticalExtension__cond (MBSInterestIndication_r17_IEs__nonCriticalExtension z) /\
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
Definition MBSInterestIndication_r17_IEs__mbs_Priority_r17__Format : T_Format MBSInterestIndication_r17_IEs__mbs_Priority_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MBSInterestIndication_r17_IEs__mbs_Priority_r17__nat__Format MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1 MBSInterestIndication_r17_IEs__mbs_Priority_r17__F2 MBSInterestIndication_r17_IEs__mbs_Priority_r17__F1F2 MBSInterestIndication_r17_IEs__mbs_Priority_r17__F2F1.

Opaque MBSInterestIndication_r17_IEs__mbs_Priority_r17__cond MBSInterestIndication_r17_IEs__mbs_Priority_r17__Format.

Definition MBSInterestIndication_r17_IEs__nonCriticalExtension__helper : forall a : MBSInterestIndication_r17_IEs__nonCriticalExtension__Type, True -> True /\ make__MBSInterestIndication_r17_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition MBSInterestIndication_r17_IEs__nonCriticalExtension__Format : T_Format MBSInterestIndication_r17_IEs__nonCriticalExtension__Type MBSInterestIndication_r17_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MBSInterestIndication_r17_IEs__nonCriticalExtension__Type)
    MBSInterestIndication_r17_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque MBSInterestIndication_r17_IEs__nonCriticalExtension__cond MBSInterestIndication_r17_IEs__nonCriticalExtension__Format.


Definition MBSInterestIndication_r17_IEs__Format_Type := Eval cbn in seq_format_prod MBSInterestIndication_r17_IEs__list.
Definition MBSInterestIndication_r17_IEs__Format_list : MBSInterestIndication_r17_IEs__Format_Type :=
  (CarrierFreqListMBS_r17__Format, (MBSInterestIndication_r17_IEs__mbs_Priority_r17__Format, (MBS_ServiceList_r17__Format, (octet_string_nc__Format, (MBSInterestIndication_r17_IEs__nonCriticalExtension__Format, unit_format))))).
Definition MBSInterestIndication_r17_IEs__list__Format := (*Eval compute in *) seq_format MBSInterestIndication_r17_IEs__list MBSInterestIndication_r17_IEs__Format_list.
Definition MBSInterestIndication_r17_IEs__F1 z :=
  (MBSInterestIndication_r17_IEs__mbs_FreqList_r17 z, (MBSInterestIndication_r17_IEs__mbs_Priority_r17 z, (MBSInterestIndication_r17_IEs__mbs_ServiceList_r17 z, (MBSInterestIndication_r17_IEs__lateNonCriticalExtension z, (MBSInterestIndication_r17_IEs__nonCriticalExtension z, tt))))).
Definition MBSInterestIndication_r17_IEs__F2 (y : seq_type MBSInterestIndication_r17_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MBSInterestIndication_r17_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma MBSInterestIndication_r17_IEs__F1F2_cond (z : MBSInterestIndication_r17_IEs__Type)
  : MBSInterestIndication_r17_IEs__cond z ->
  (seq_cond MBSInterestIndication_r17_IEs__list (MBSInterestIndication_r17_IEs__F1 z)).
intro H. unfold MBSInterestIndication_r17_IEs__cond in H. simpl. auto. Qed.
Lemma MBSInterestIndication_r17_IEs__F1F2_cond2 (z : MBSInterestIndication_r17_IEs__Type)
 : MBSInterestIndication_r17_IEs__F2 (MBSInterestIndication_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MBSInterestIndication_r17_IEs__F2F1_cond (y : seq_type MBSInterestIndication_r17_IEs__list)
  : seq_cond MBSInterestIndication_r17_IEs__list y ->
 (MBSInterestIndication_r17_IEs__cond (MBSInterestIndication_r17_IEs__F2 y)) /\  MBSInterestIndication_r17_IEs__F1 (MBSInterestIndication_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MBSInterestIndication_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold MBSInterestIndication_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MBSInterestIndication_r17_IEs__Format : T_Format MBSInterestIndication_r17_IEs__Type MBSInterestIndication_r17_IEs__cond :=
        proj2_format  MBSInterestIndication_r17_IEs__cond MBSInterestIndication_r17_IEs__list__Format
    MBSInterestIndication_r17_IEs__F1 MBSInterestIndication_r17_IEs__F2 MBSInterestIndication_r17_IEs__F1F2_cond  MBSInterestIndication_r17_IEs__F1F2_cond2 MBSInterestIndication_r17_IEs__F2F1_cond.
Opaque MBSInterestIndication_r17_IEs__cond MBSInterestIndication_r17_IEs__Format.

