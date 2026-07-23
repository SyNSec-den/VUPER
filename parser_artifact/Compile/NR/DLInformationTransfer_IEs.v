Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DedicatedNAS_Message.

Opaque DedicatedNAS_Message__cond DedicatedNAS_Message__Format.

Require Import NR.DLInformationTransfer_v1610_IEs.

Opaque DLInformationTransfer_v1610_IEs__cond DLInformationTransfer_v1610_IEs__Format.

Record DLInformationTransfer_IEs__Type : Set :=
  make__DLInformationTransfer_IEs__Type {
    DLInformationTransfer_IEs__dedicatedNAS_Message : option DedicatedNAS_Message__Type ;
    DLInformationTransfer_IEs__lateNonCriticalExtension : option octet_string ;
    DLInformationTransfer_IEs__nonCriticalExtension : option DLInformationTransfer_v1610_IEs__Type ;
}.
Definition DLInformationTransfer_IEs__list := (
 Opt DedicatedNAS_Message__Type DedicatedNAS_Message__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt DLInformationTransfer_v1610_IEs__Type DLInformationTransfer_v1610_IEs__cond ::
 nil).
Definition DLInformationTransfer_IEs__cond z := 
  opt_cond DedicatedNAS_Message__cond (DLInformationTransfer_IEs__dedicatedNAS_Message z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (DLInformationTransfer_IEs__lateNonCriticalExtension z) /\
  opt_cond DLInformationTransfer_v1610_IEs__cond (DLInformationTransfer_IEs__nonCriticalExtension z) /\
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

Definition DLInformationTransfer_IEs__Format_Type := Eval cbn in seq_format_prod DLInformationTransfer_IEs__list.
Definition DLInformationTransfer_IEs__Format_list : DLInformationTransfer_IEs__Format_Type :=
  (DedicatedNAS_Message__Format, (octet_string_nc__Format, (DLInformationTransfer_v1610_IEs__Format, unit_format))).
Definition DLInformationTransfer_IEs__list__Format := (*Eval compute in *) seq_format DLInformationTransfer_IEs__list DLInformationTransfer_IEs__Format_list.
Definition DLInformationTransfer_IEs__F1 z :=
  (DLInformationTransfer_IEs__dedicatedNAS_Message z, (DLInformationTransfer_IEs__lateNonCriticalExtension z, (DLInformationTransfer_IEs__nonCriticalExtension z, tt))).
Definition DLInformationTransfer_IEs__F2 (y : seq_type DLInformationTransfer_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__DLInformationTransfer_IEs__Type i0 i1 i2
  end.
Lemma DLInformationTransfer_IEs__F1F2_cond (z : DLInformationTransfer_IEs__Type)
  : DLInformationTransfer_IEs__cond z ->
  (seq_cond DLInformationTransfer_IEs__list (DLInformationTransfer_IEs__F1 z)).
intro H. unfold DLInformationTransfer_IEs__cond in H. simpl. auto. Qed.
Lemma DLInformationTransfer_IEs__F1F2_cond2 (z : DLInformationTransfer_IEs__Type)
 : DLInformationTransfer_IEs__F2 (DLInformationTransfer_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DLInformationTransfer_IEs__F2F1_cond (y : seq_type DLInformationTransfer_IEs__list)
  : seq_cond DLInformationTransfer_IEs__list y ->
 (DLInformationTransfer_IEs__cond (DLInformationTransfer_IEs__F2 y)) /\  DLInformationTransfer_IEs__F1 (DLInformationTransfer_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DLInformationTransfer_IEs__cond. simpl in *. auto.
 - simpl. unfold DLInformationTransfer_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DLInformationTransfer_IEs__Format : T_Format DLInformationTransfer_IEs__Type DLInformationTransfer_IEs__cond :=
        proj2_format  DLInformationTransfer_IEs__cond DLInformationTransfer_IEs__list__Format
    DLInformationTransfer_IEs__F1 DLInformationTransfer_IEs__F2 DLInformationTransfer_IEs__F1F2_cond  DLInformationTransfer_IEs__F1F2_cond2 DLInformationTransfer_IEs__F2F1_cond.
Opaque DLInformationTransfer_IEs__cond DLInformationTransfer_IEs__Format.

