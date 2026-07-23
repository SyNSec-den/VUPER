Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Definition CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type := bit_string_fixed.
Definition CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 28 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Definition CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type := bit_string_fixed.
Definition CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type := bit_string_fixed.
Definition CGI_InfoEUTRALogging__cellIdentity_eutra_epc__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 28 /\ bit_string_len_prop (fst z) (snd z)).
Record CGI_InfoEUTRALogging__Type : Set :=
  make__CGI_InfoEUTRALogging__Type {
    CGI_InfoEUTRALogging__plmn_Identity_eutra_5gc : option PLMN_Identity__Type ;
    CGI_InfoEUTRALogging__trackingAreaCode_eutra_5gc : option TrackingAreaCode__Type ;
    CGI_InfoEUTRALogging__cellIdentity_eutra_5gc : option CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type ;
    CGI_InfoEUTRALogging__plmn_Identity_eutra_epc : option PLMN_Identity__Type ;
    CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc : option CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type ;
    CGI_InfoEUTRALogging__cellIdentity_eutra_epc : option CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type ;
}.
Definition CGI_InfoEUTRALogging__list := (
 Opt PLMN_Identity__Type PLMN_Identity__cond ::
 Opt TrackingAreaCode__Type TrackingAreaCode__cond ::
 Opt CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__cond ::
 Opt PLMN_Identity__Type PLMN_Identity__cond ::
 Opt CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__cond ::
 Opt CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type CGI_InfoEUTRALogging__cellIdentity_eutra_epc__cond ::
 nil).
Definition CGI_InfoEUTRALogging__cond z := 
  opt_cond PLMN_Identity__cond (CGI_InfoEUTRALogging__plmn_Identity_eutra_5gc z) /\
  opt_cond TrackingAreaCode__cond (CGI_InfoEUTRALogging__trackingAreaCode_eutra_5gc z) /\
  opt_cond CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__cond (CGI_InfoEUTRALogging__cellIdentity_eutra_5gc z) /\
  opt_cond PLMN_Identity__cond (CGI_InfoEUTRALogging__plmn_Identity_eutra_epc z) /\
  opt_cond CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__cond (CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc z) /\
  opt_cond CGI_InfoEUTRALogging__cellIdentity_eutra_epc__cond (CGI_InfoEUTRALogging__cellIdentity_eutra_epc z) /\
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
Definition CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Format : T_Format CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__cond := (* Eval compute in *) bit_string_fixed_format 28.
Opaque CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__cond CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Format.

Definition CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Format : T_Format CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__cond CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Format.

Definition CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Format : T_Format CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type CGI_InfoEUTRALogging__cellIdentity_eutra_epc__cond := (* Eval compute in *) bit_string_fixed_format 28.
Opaque CGI_InfoEUTRALogging__cellIdentity_eutra_epc__cond CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Format.


Definition CGI_InfoEUTRALogging__Format_Type := Eval cbn in seq_format_prod CGI_InfoEUTRALogging__list.
Definition CGI_InfoEUTRALogging__Format_list : CGI_InfoEUTRALogging__Format_Type :=
  (PLMN_Identity__Format, (TrackingAreaCode__Format, (CGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Format, (PLMN_Identity__Format, (CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Format, (CGI_InfoEUTRALogging__cellIdentity_eutra_epc__Format, unit_format)))))).
Definition CGI_InfoEUTRALogging__list__Format := (*Eval compute in *) seq_format CGI_InfoEUTRALogging__list CGI_InfoEUTRALogging__Format_list.
Definition CGI_InfoEUTRALogging__F1 z :=
  (CGI_InfoEUTRALogging__plmn_Identity_eutra_5gc z, (CGI_InfoEUTRALogging__trackingAreaCode_eutra_5gc z, (CGI_InfoEUTRALogging__cellIdentity_eutra_5gc z, (CGI_InfoEUTRALogging__plmn_Identity_eutra_epc z, (CGI_InfoEUTRALogging__trackingAreaCode_eutra_epc z, (CGI_InfoEUTRALogging__cellIdentity_eutra_epc z, tt)))))).
Definition CGI_InfoEUTRALogging__F2 (y : seq_type CGI_InfoEUTRALogging__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__CGI_InfoEUTRALogging__Type i0 i1 i2 i3 i4 i5
  end.
Lemma CGI_InfoEUTRALogging__F1F2_cond (z : CGI_InfoEUTRALogging__Type)
  : CGI_InfoEUTRALogging__cond z ->
  (seq_cond CGI_InfoEUTRALogging__list (CGI_InfoEUTRALogging__F1 z)).
intro H. unfold CGI_InfoEUTRALogging__cond in H. simpl. auto. Qed.
Lemma CGI_InfoEUTRALogging__F1F2_cond2 (z : CGI_InfoEUTRALogging__Type)
 : CGI_InfoEUTRALogging__F2 (CGI_InfoEUTRALogging__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_InfoEUTRALogging__F2F1_cond (y : seq_type CGI_InfoEUTRALogging__list)
  : seq_cond CGI_InfoEUTRALogging__list y ->
 (CGI_InfoEUTRALogging__cond (CGI_InfoEUTRALogging__F2 y)) /\  CGI_InfoEUTRALogging__F1 (CGI_InfoEUTRALogging__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_InfoEUTRALogging__cond. simpl in *. auto.
 - simpl. unfold CGI_InfoEUTRALogging__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_InfoEUTRALogging__Format : T_Format CGI_InfoEUTRALogging__Type CGI_InfoEUTRALogging__cond :=
        proj2_format  CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__list__Format
    CGI_InfoEUTRALogging__F1 CGI_InfoEUTRALogging__F2 CGI_InfoEUTRALogging__F1F2_cond  CGI_InfoEUTRALogging__F1F2_cond2 CGI_InfoEUTRALogging__F2F1_cond.
Opaque CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__Format.

