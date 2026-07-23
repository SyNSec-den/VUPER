Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Record DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type : Set := make__DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type {}.
Definition DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__cond (z : DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type) := True.
Record DLInformationTransferMRDC_r16_IEs__Type : Set :=
  make__DLInformationTransferMRDC_r16_IEs__Type {
    DLInformationTransferMRDC_r16_IEs__dl_DCCH_MessageNR_r16 : option octet_string ;
    DLInformationTransferMRDC_r16_IEs__dl_DCCH_MessageEUTRA_r16 : option octet_string ;
    DLInformationTransferMRDC_r16_IEs__lateNonCriticalExtension : option octet_string ;
    DLInformationTransferMRDC_r16_IEs__nonCriticalExtension : option DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type ;
}.
Definition DLInformationTransferMRDC_r16_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__cond ::
 nil).
Definition DLInformationTransferMRDC_r16_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (DLInformationTransferMRDC_r16_IEs__dl_DCCH_MessageNR_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (DLInformationTransferMRDC_r16_IEs__dl_DCCH_MessageEUTRA_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (DLInformationTransferMRDC_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__cond (DLInformationTransferMRDC_r16_IEs__nonCriticalExtension z) /\
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
Definition DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__helper : forall a : DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type, True -> True /\ make__DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Format : T_Format DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Type)
    DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__cond DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Format.


Definition DLInformationTransferMRDC_r16_IEs__Format_Type := Eval cbn in seq_format_prod DLInformationTransferMRDC_r16_IEs__list.
Definition DLInformationTransferMRDC_r16_IEs__Format_list : DLInformationTransferMRDC_r16_IEs__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, (DLInformationTransferMRDC_r16_IEs__nonCriticalExtension__Format, unit_format)))).
Definition DLInformationTransferMRDC_r16_IEs__list__Format := (*Eval compute in *) seq_format DLInformationTransferMRDC_r16_IEs__list DLInformationTransferMRDC_r16_IEs__Format_list.
Definition DLInformationTransferMRDC_r16_IEs__F1 z :=
  (DLInformationTransferMRDC_r16_IEs__dl_DCCH_MessageNR_r16 z, (DLInformationTransferMRDC_r16_IEs__dl_DCCH_MessageEUTRA_r16 z, (DLInformationTransferMRDC_r16_IEs__lateNonCriticalExtension z, (DLInformationTransferMRDC_r16_IEs__nonCriticalExtension z, tt)))).
Definition DLInformationTransferMRDC_r16_IEs__F2 (y : seq_type DLInformationTransferMRDC_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__DLInformationTransferMRDC_r16_IEs__Type i0 i1 i2 i3
  end.
Lemma DLInformationTransferMRDC_r16_IEs__F1F2_cond (z : DLInformationTransferMRDC_r16_IEs__Type)
  : DLInformationTransferMRDC_r16_IEs__cond z ->
  (seq_cond DLInformationTransferMRDC_r16_IEs__list (DLInformationTransferMRDC_r16_IEs__F1 z)).
intro H. unfold DLInformationTransferMRDC_r16_IEs__cond in H. simpl. auto. Qed.
Lemma DLInformationTransferMRDC_r16_IEs__F1F2_cond2 (z : DLInformationTransferMRDC_r16_IEs__Type)
 : DLInformationTransferMRDC_r16_IEs__F2 (DLInformationTransferMRDC_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DLInformationTransferMRDC_r16_IEs__F2F1_cond (y : seq_type DLInformationTransferMRDC_r16_IEs__list)
  : seq_cond DLInformationTransferMRDC_r16_IEs__list y ->
 (DLInformationTransferMRDC_r16_IEs__cond (DLInformationTransferMRDC_r16_IEs__F2 y)) /\  DLInformationTransferMRDC_r16_IEs__F1 (DLInformationTransferMRDC_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DLInformationTransferMRDC_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold DLInformationTransferMRDC_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DLInformationTransferMRDC_r16_IEs__Format : T_Format DLInformationTransferMRDC_r16_IEs__Type DLInformationTransferMRDC_r16_IEs__cond :=
        proj2_format  DLInformationTransferMRDC_r16_IEs__cond DLInformationTransferMRDC_r16_IEs__list__Format
    DLInformationTransferMRDC_r16_IEs__F1 DLInformationTransferMRDC_r16_IEs__F2 DLInformationTransferMRDC_r16_IEs__F1F2_cond  DLInformationTransferMRDC_r16_IEs__F1F2_cond2 DLInformationTransferMRDC_r16_IEs__F2F1_cond.
Opaque DLInformationTransferMRDC_r16_IEs__cond DLInformationTransferMRDC_r16_IEs__Format.

