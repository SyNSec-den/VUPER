Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Record TrackingAreaIdentity_r16__Type : Set :=
  make__TrackingAreaIdentity_r16__Type {
    TrackingAreaIdentity_r16__plmn_Identity_r16 : PLMN_Identity__Type ;
    TrackingAreaIdentity_r16__trackingAreaCode_r16 : TrackingAreaCode__Type ;
}.
Definition TrackingAreaIdentity_r16__list := (
 Nor PLMN_Identity__Type PLMN_Identity__cond ::
 Nor TrackingAreaCode__Type TrackingAreaCode__cond ::
 nil).
Definition TrackingAreaIdentity_r16__cond z := 
  PLMN_Identity__cond (TrackingAreaIdentity_r16__plmn_Identity_r16 z) /\
  TrackingAreaCode__cond (TrackingAreaIdentity_r16__trackingAreaCode_r16 z) /\
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

Definition TrackingAreaIdentity_r16__Format_Type := Eval cbn in seq_format_prod TrackingAreaIdentity_r16__list.
Definition TrackingAreaIdentity_r16__Format_list : TrackingAreaIdentity_r16__Format_Type :=
  (PLMN_Identity__Format, (TrackingAreaCode__Format, unit_format)).
Definition TrackingAreaIdentity_r16__list__Format := (*Eval compute in *) seq_format TrackingAreaIdentity_r16__list TrackingAreaIdentity_r16__Format_list.
Definition TrackingAreaIdentity_r16__F1 z :=
  (TrackingAreaIdentity_r16__plmn_Identity_r16 z, (TrackingAreaIdentity_r16__trackingAreaCode_r16 z, tt)).
Definition TrackingAreaIdentity_r16__F2 (y : seq_type TrackingAreaIdentity_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TrackingAreaIdentity_r16__Type i0 i1
  end.
Lemma TrackingAreaIdentity_r16__F1F2_cond (z : TrackingAreaIdentity_r16__Type)
  : TrackingAreaIdentity_r16__cond z ->
  (seq_cond TrackingAreaIdentity_r16__list (TrackingAreaIdentity_r16__F1 z)).
intro H. unfold TrackingAreaIdentity_r16__cond in H. simpl. auto. Qed.
Lemma TrackingAreaIdentity_r16__F1F2_cond2 (z : TrackingAreaIdentity_r16__Type)
 : TrackingAreaIdentity_r16__F2 (TrackingAreaIdentity_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TrackingAreaIdentity_r16__F2F1_cond (y : seq_type TrackingAreaIdentity_r16__list)
  : seq_cond TrackingAreaIdentity_r16__list y ->
 (TrackingAreaIdentity_r16__cond (TrackingAreaIdentity_r16__F2 y)) /\  TrackingAreaIdentity_r16__F1 (TrackingAreaIdentity_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TrackingAreaIdentity_r16__cond. simpl in *. auto.
 - simpl. unfold TrackingAreaIdentity_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TrackingAreaIdentity_r16__Format : T_Format TrackingAreaIdentity_r16__Type TrackingAreaIdentity_r16__cond :=
        proj2_format  TrackingAreaIdentity_r16__cond TrackingAreaIdentity_r16__list__Format
    TrackingAreaIdentity_r16__F1 TrackingAreaIdentity_r16__F2 TrackingAreaIdentity_r16__F1F2_cond  TrackingAreaIdentity_r16__F1F2_cond2 TrackingAreaIdentity_r16__F2F1_cond.
Opaque TrackingAreaIdentity_r16__cond TrackingAreaIdentity_r16__Format.

