Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RRCReconfiguration_v1530_IEs__fullConfig__Type : Set :=
 | RRCReconfiguration_v1530_IEs__fullConfig__true
.
Definition RRCReconfiguration_v1530_IEs__fullConfig__cond := (fun (_ : RRCReconfiguration_v1530_IEs__fullConfig__Type) => True).
Lemma RRCReconfiguration_v1530_IEs__fullConfig__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCReconfiguration_v1530_IEs__fullConfig__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCReconfiguration_v1530_IEs__fullConfig__nat__helper.

Definition RRCReconfiguration_v1530_IEs__fullConfig__F1 t :=
  match t with
  | RRCReconfiguration_v1530_IEs__fullConfig__true => 0
  end.
Definition RRCReconfiguration_v1530_IEs__fullConfig__F2 n :=
  match n with
  | 0 => RRCReconfiguration_v1530_IEs__fullConfig__true
  | _ => RRCReconfiguration_v1530_IEs__fullConfig__true
  end.
Lemma RRCReconfiguration_v1530_IEs__fullConfig__F1F2 : forall x : RRCReconfiguration_v1530_IEs__fullConfig__Type, (RRCReconfiguration_v1530_IEs__fullConfig__F1 x <= 0) /\ RRCReconfiguration_v1530_IEs__fullConfig__F2 (RRCReconfiguration_v1530_IEs__fullConfig__F1 x) = x. imp_solve. Qed.
Lemma RRCReconfiguration_v1530_IEs__fullConfig__F2F1 : forall (y : nat) (H : y <= 0), RRCReconfiguration_v1530_IEs__fullConfig__F1 (RRCReconfiguration_v1530_IEs__fullConfig__F2 y) = y. enum_solve H y. Qed.

Require Import NR.DedicatedNAS_Message.

Opaque DedicatedNAS_Message__cond DedicatedNAS_Message__Format.

Definition RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Type := list DedicatedNAS_Message__Type.

Lemma RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__helper1 : (0 <= 1 <= maxDRB)%Z. unfold maxDRB.
 lia. Qed.
Lemma RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__helper2 : to_bit_sz (Z.to_nat (maxDRB - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDRB - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__cond (z : RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Type) :=  (1 <= Z.of_nat (length z) <= maxDRB)%Z /\ (list_and DedicatedNAS_Message__cond z) .

Require Import NR.MasterKeyUpdate.

Opaque MasterKeyUpdate__cond MasterKeyUpdate__Format.

Require Import NR.OtherConfig.

Opaque OtherConfig__cond OtherConfig__Format.

Require Import NR.RRCReconfiguration_v1540_IEs.

Opaque RRCReconfiguration_v1540_IEs__cond RRCReconfiguration_v1540_IEs__Format.

Record RRCReconfiguration_v1530_IEs__Type : Set :=
  make__RRCReconfiguration_v1530_IEs__Type {
    RRCReconfiguration_v1530_IEs__masterCellGroup : option octet_string ;
    RRCReconfiguration_v1530_IEs__fullConfig : option RRCReconfiguration_v1530_IEs__fullConfig__Type ;
    RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList : option RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Type ;
    RRCReconfiguration_v1530_IEs__masterKeyUpdate : option MasterKeyUpdate__Type ;
    RRCReconfiguration_v1530_IEs__dedicatedSIB1_Delivery : option octet_string ;
    RRCReconfiguration_v1530_IEs__dedicatedSystemInformationDelivery : option octet_string ;
    RRCReconfiguration_v1530_IEs__otherConfig : option OtherConfig__Type ;
    RRCReconfiguration_v1530_IEs__nonCriticalExtension : option RRCReconfiguration_v1540_IEs__Type ;
}.
Definition RRCReconfiguration_v1530_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCReconfiguration_v1530_IEs__fullConfig__Type RRCReconfiguration_v1530_IEs__fullConfig__cond ::
 Opt RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Type RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__cond ::
 Opt MasterKeyUpdate__Type MasterKeyUpdate__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt OtherConfig__Type OtherConfig__cond ::
 Opt RRCReconfiguration_v1540_IEs__Type RRCReconfiguration_v1540_IEs__cond ::
 nil).
Definition RRCReconfiguration_v1530_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_v1530_IEs__masterCellGroup z) /\
  opt_cond RRCReconfiguration_v1530_IEs__fullConfig__cond (RRCReconfiguration_v1530_IEs__fullConfig z) /\
  opt_cond RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__cond (RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList z) /\
  opt_cond MasterKeyUpdate__cond (RRCReconfiguration_v1530_IEs__masterKeyUpdate z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_v1530_IEs__dedicatedSIB1_Delivery z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_v1530_IEs__dedicatedSystemInformationDelivery z) /\
  opt_cond OtherConfig__cond (RRCReconfiguration_v1530_IEs__otherConfig z) /\
  opt_cond RRCReconfiguration_v1540_IEs__cond (RRCReconfiguration_v1530_IEs__nonCriticalExtension z) /\
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
Definition RRCReconfiguration_v1530_IEs__fullConfig__Format : T_Format RRCReconfiguration_v1530_IEs__fullConfig__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCReconfiguration_v1530_IEs__fullConfig__nat__Format RRCReconfiguration_v1530_IEs__fullConfig__F1 RRCReconfiguration_v1530_IEs__fullConfig__F2 RRCReconfiguration_v1530_IEs__fullConfig__F1F2 RRCReconfiguration_v1530_IEs__fullConfig__F2F1.

Opaque RRCReconfiguration_v1530_IEs__fullConfig__cond RRCReconfiguration_v1530_IEs__fullConfig__Format.

Definition RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Format : T_Format RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Type RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__cond := seq_of_format DedicatedNAS_Message__Format 1 maxDRB RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__helper1 RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__helper2.

Opaque RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__cond RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Format.


Definition RRCReconfiguration_v1530_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfiguration_v1530_IEs__list.
Definition RRCReconfiguration_v1530_IEs__Format_list : RRCReconfiguration_v1530_IEs__Format_Type :=
  (octet_string_nc__Format, (RRCReconfiguration_v1530_IEs__fullConfig__Format, (RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList__Format, (MasterKeyUpdate__Format, (octet_string_nc__Format, (octet_string_nc__Format, (OtherConfig__Format, (RRCReconfiguration_v1540_IEs__Format, unit_format)))))))).
Definition RRCReconfiguration_v1530_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfiguration_v1530_IEs__list RRCReconfiguration_v1530_IEs__Format_list.
Definition RRCReconfiguration_v1530_IEs__F1 z :=
  (RRCReconfiguration_v1530_IEs__masterCellGroup z, (RRCReconfiguration_v1530_IEs__fullConfig z, (RRCReconfiguration_v1530_IEs__dedicatedNAS_MessageList z, (RRCReconfiguration_v1530_IEs__masterKeyUpdate z, (RRCReconfiguration_v1530_IEs__dedicatedSIB1_Delivery z, (RRCReconfiguration_v1530_IEs__dedicatedSystemInformationDelivery z, (RRCReconfiguration_v1530_IEs__otherConfig z, (RRCReconfiguration_v1530_IEs__nonCriticalExtension z, tt)))))))).
Definition RRCReconfiguration_v1530_IEs__F2 (y : seq_type RRCReconfiguration_v1530_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__RRCReconfiguration_v1530_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma RRCReconfiguration_v1530_IEs__F1F2_cond (z : RRCReconfiguration_v1530_IEs__Type)
  : RRCReconfiguration_v1530_IEs__cond z ->
  (seq_cond RRCReconfiguration_v1530_IEs__list (RRCReconfiguration_v1530_IEs__F1 z)).
intro H. unfold RRCReconfiguration_v1530_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfiguration_v1530_IEs__F1F2_cond2 (z : RRCReconfiguration_v1530_IEs__Type)
 : RRCReconfiguration_v1530_IEs__F2 (RRCReconfiguration_v1530_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfiguration_v1530_IEs__F2F1_cond (y : seq_type RRCReconfiguration_v1530_IEs__list)
  : seq_cond RRCReconfiguration_v1530_IEs__list y ->
 (RRCReconfiguration_v1530_IEs__cond (RRCReconfiguration_v1530_IEs__F2 y)) /\  RRCReconfiguration_v1530_IEs__F1 (RRCReconfiguration_v1530_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfiguration_v1530_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfiguration_v1530_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfiguration_v1530_IEs__Format : T_Format RRCReconfiguration_v1530_IEs__Type RRCReconfiguration_v1530_IEs__cond :=
        proj2_format  RRCReconfiguration_v1530_IEs__cond RRCReconfiguration_v1530_IEs__list__Format
    RRCReconfiguration_v1530_IEs__F1 RRCReconfiguration_v1530_IEs__F2 RRCReconfiguration_v1530_IEs__F1F2_cond  RRCReconfiguration_v1530_IEs__F1F2_cond2 RRCReconfiguration_v1530_IEs__F2F1_cond.
Opaque RRCReconfiguration_v1530_IEs__cond RRCReconfiguration_v1530_IEs__Format.

