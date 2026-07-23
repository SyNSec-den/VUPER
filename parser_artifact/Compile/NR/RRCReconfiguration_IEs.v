Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RadioBearerConfig.

Opaque RadioBearerConfig__cond RadioBearerConfig__Format.

Require Import NR.MeasConfig.

Opaque MeasConfig__cond MeasConfig__Format.

Require Import NR.RRCReconfiguration_v1530_IEs.

Opaque RRCReconfiguration_v1530_IEs__cond RRCReconfiguration_v1530_IEs__Format.

Record RRCReconfiguration_IEs__Type : Set :=
  make__RRCReconfiguration_IEs__Type {
    RRCReconfiguration_IEs__radioBearerConfig : option RadioBearerConfig__Type ;
    RRCReconfiguration_IEs__secondaryCellGroup : option octet_string ;
    RRCReconfiguration_IEs__measConfig : option MeasConfig__Type ;
    RRCReconfiguration_IEs__lateNonCriticalExtension : option octet_string ;
    RRCReconfiguration_IEs__nonCriticalExtension : option RRCReconfiguration_v1530_IEs__Type ;
}.
Definition RRCReconfiguration_IEs__list := (
 Opt RadioBearerConfig__Type RadioBearerConfig__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasConfig__Type MeasConfig__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCReconfiguration_v1530_IEs__Type RRCReconfiguration_v1530_IEs__cond ::
 nil).
Definition RRCReconfiguration_IEs__cond z := 
  opt_cond RadioBearerConfig__cond (RRCReconfiguration_IEs__radioBearerConfig z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_IEs__secondaryCellGroup z) /\
  opt_cond MeasConfig__cond (RRCReconfiguration_IEs__measConfig z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_IEs__lateNonCriticalExtension z) /\
  opt_cond RRCReconfiguration_v1530_IEs__cond (RRCReconfiguration_IEs__nonCriticalExtension z) /\
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

Definition RRCReconfiguration_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfiguration_IEs__list.
Definition RRCReconfiguration_IEs__Format_list : RRCReconfiguration_IEs__Format_Type :=
  (RadioBearerConfig__Format, (octet_string_nc__Format, (MeasConfig__Format, (octet_string_nc__Format, (RRCReconfiguration_v1530_IEs__Format, unit_format))))).
Definition RRCReconfiguration_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfiguration_IEs__list RRCReconfiguration_IEs__Format_list.
Definition RRCReconfiguration_IEs__F1 z :=
  (RRCReconfiguration_IEs__radioBearerConfig z, (RRCReconfiguration_IEs__secondaryCellGroup z, (RRCReconfiguration_IEs__measConfig z, (RRCReconfiguration_IEs__lateNonCriticalExtension z, (RRCReconfiguration_IEs__nonCriticalExtension z, tt))))).
Definition RRCReconfiguration_IEs__F2 (y : seq_type RRCReconfiguration_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__RRCReconfiguration_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma RRCReconfiguration_IEs__F1F2_cond (z : RRCReconfiguration_IEs__Type)
  : RRCReconfiguration_IEs__cond z ->
  (seq_cond RRCReconfiguration_IEs__list (RRCReconfiguration_IEs__F1 z)).
intro H. unfold RRCReconfiguration_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfiguration_IEs__F1F2_cond2 (z : RRCReconfiguration_IEs__Type)
 : RRCReconfiguration_IEs__F2 (RRCReconfiguration_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfiguration_IEs__F2F1_cond (y : seq_type RRCReconfiguration_IEs__list)
  : seq_cond RRCReconfiguration_IEs__list y ->
 (RRCReconfiguration_IEs__cond (RRCReconfiguration_IEs__F2 y)) /\  RRCReconfiguration_IEs__F1 (RRCReconfiguration_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfiguration_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfiguration_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfiguration_IEs__Format : T_Format RRCReconfiguration_IEs__Type RRCReconfiguration_IEs__cond :=
        proj2_format  RRCReconfiguration_IEs__cond RRCReconfiguration_IEs__list__Format
    RRCReconfiguration_IEs__F1 RRCReconfiguration_IEs__F2 RRCReconfiguration_IEs__F1F2_cond  RRCReconfiguration_IEs__F1F2_cond2 RRCReconfiguration_IEs__F2F1_cond.
Opaque RRCReconfiguration_IEs__cond RRCReconfiguration_IEs__Format.

