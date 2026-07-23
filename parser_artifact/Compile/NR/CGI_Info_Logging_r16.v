Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.CellIdentity.

Opaque CellIdentity__cond CellIdentity__Format.

Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Record CGI_Info_Logging_r16__Type : Set :=
  make__CGI_Info_Logging_r16__Type {
    CGI_Info_Logging_r16__plmn_Identity_r16 : PLMN_Identity__Type ;
    CGI_Info_Logging_r16__cellIdentity_r16 : CellIdentity__Type ;
    CGI_Info_Logging_r16__trackingAreaCode_r16 : option TrackingAreaCode__Type ;
}.
Definition CGI_Info_Logging_r16__list := (
 Nor PLMN_Identity__Type PLMN_Identity__cond ::
 Nor CellIdentity__Type CellIdentity__cond ::
 Opt TrackingAreaCode__Type TrackingAreaCode__cond ::
 nil).
Definition CGI_Info_Logging_r16__cond z := 
  PLMN_Identity__cond (CGI_Info_Logging_r16__plmn_Identity_r16 z) /\
  CellIdentity__cond (CGI_Info_Logging_r16__cellIdentity_r16 z) /\
  opt_cond TrackingAreaCode__cond (CGI_Info_Logging_r16__trackingAreaCode_r16 z) /\
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

Definition CGI_Info_Logging_r16__Format_Type := Eval cbn in seq_format_prod CGI_Info_Logging_r16__list.
Definition CGI_Info_Logging_r16__Format_list : CGI_Info_Logging_r16__Format_Type :=
  (PLMN_Identity__Format, (CellIdentity__Format, (TrackingAreaCode__Format, unit_format))).
Definition CGI_Info_Logging_r16__list__Format := (*Eval compute in *) seq_format CGI_Info_Logging_r16__list CGI_Info_Logging_r16__Format_list.
Definition CGI_Info_Logging_r16__F1 z :=
  (CGI_Info_Logging_r16__plmn_Identity_r16 z, (CGI_Info_Logging_r16__cellIdentity_r16 z, (CGI_Info_Logging_r16__trackingAreaCode_r16 z, tt))).
Definition CGI_Info_Logging_r16__F2 (y : seq_type CGI_Info_Logging_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CGI_Info_Logging_r16__Type i0 i1 i2
  end.
Lemma CGI_Info_Logging_r16__F1F2_cond (z : CGI_Info_Logging_r16__Type)
  : CGI_Info_Logging_r16__cond z ->
  (seq_cond CGI_Info_Logging_r16__list (CGI_Info_Logging_r16__F1 z)).
intro H. unfold CGI_Info_Logging_r16__cond in H. simpl. auto. Qed.
Lemma CGI_Info_Logging_r16__F1F2_cond2 (z : CGI_Info_Logging_r16__Type)
 : CGI_Info_Logging_r16__F2 (CGI_Info_Logging_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_Info_Logging_r16__F2F1_cond (y : seq_type CGI_Info_Logging_r16__list)
  : seq_cond CGI_Info_Logging_r16__list y ->
 (CGI_Info_Logging_r16__cond (CGI_Info_Logging_r16__F2 y)) /\  CGI_Info_Logging_r16__F1 (CGI_Info_Logging_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_Info_Logging_r16__cond. simpl in *. auto.
 - simpl. unfold CGI_Info_Logging_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_Info_Logging_r16__Format : T_Format CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond :=
        proj2_format  CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__list__Format
    CGI_Info_Logging_r16__F1 CGI_Info_Logging_r16__F2 CGI_Info_Logging_r16__F1F2_cond  CGI_Info_Logging_r16__F1F2_cond2 CGI_Info_Logging_r16__F2F1_cond.
Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

