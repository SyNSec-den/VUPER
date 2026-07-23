Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RRCReconfigurationCompleteSidelink_v1710_IEs.

Opaque RRCReconfigurationCompleteSidelink_v1710_IEs__cond RRCReconfigurationCompleteSidelink_v1710_IEs__Format.

Record RRCReconfigurationCompleteSidelink_r16_IEs__Type : Set :=
  make__RRCReconfigurationCompleteSidelink_r16_IEs__Type {
    RRCReconfigurationCompleteSidelink_r16_IEs__lateNonCriticalExtension : option octet_string ;
    RRCReconfigurationCompleteSidelink_r16_IEs__nonCriticalExtension : option RRCReconfigurationCompleteSidelink_v1710_IEs__Type ;
}.
Definition RRCReconfigurationCompleteSidelink_r16_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCReconfigurationCompleteSidelink_v1710_IEs__Type RRCReconfigurationCompleteSidelink_v1710_IEs__cond ::
 nil).
Definition RRCReconfigurationCompleteSidelink_r16_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfigurationCompleteSidelink_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond RRCReconfigurationCompleteSidelink_v1710_IEs__cond (RRCReconfigurationCompleteSidelink_r16_IEs__nonCriticalExtension z) /\
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

Definition RRCReconfigurationCompleteSidelink_r16_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationCompleteSidelink_r16_IEs__list.
Definition RRCReconfigurationCompleteSidelink_r16_IEs__Format_list : RRCReconfigurationCompleteSidelink_r16_IEs__Format_Type :=
  (octet_string_nc__Format, (RRCReconfigurationCompleteSidelink_v1710_IEs__Format, unit_format)).
Definition RRCReconfigurationCompleteSidelink_r16_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfigurationCompleteSidelink_r16_IEs__list RRCReconfigurationCompleteSidelink_r16_IEs__Format_list.
Definition RRCReconfigurationCompleteSidelink_r16_IEs__F1 z :=
  (RRCReconfigurationCompleteSidelink_r16_IEs__lateNonCriticalExtension z, (RRCReconfigurationCompleteSidelink_r16_IEs__nonCriticalExtension z, tt)).
Definition RRCReconfigurationCompleteSidelink_r16_IEs__F2 (y : seq_type RRCReconfigurationCompleteSidelink_r16_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfigurationCompleteSidelink_r16_IEs__Type i0 i1
  end.
Lemma RRCReconfigurationCompleteSidelink_r16_IEs__F1F2_cond (z : RRCReconfigurationCompleteSidelink_r16_IEs__Type)
  : RRCReconfigurationCompleteSidelink_r16_IEs__cond z ->
  (seq_cond RRCReconfigurationCompleteSidelink_r16_IEs__list (RRCReconfigurationCompleteSidelink_r16_IEs__F1 z)).
intro H. unfold RRCReconfigurationCompleteSidelink_r16_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationCompleteSidelink_r16_IEs__F1F2_cond2 (z : RRCReconfigurationCompleteSidelink_r16_IEs__Type)
 : RRCReconfigurationCompleteSidelink_r16_IEs__F2 (RRCReconfigurationCompleteSidelink_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationCompleteSidelink_r16_IEs__F2F1_cond (y : seq_type RRCReconfigurationCompleteSidelink_r16_IEs__list)
  : seq_cond RRCReconfigurationCompleteSidelink_r16_IEs__list y ->
 (RRCReconfigurationCompleteSidelink_r16_IEs__cond (RRCReconfigurationCompleteSidelink_r16_IEs__F2 y)) /\  RRCReconfigurationCompleteSidelink_r16_IEs__F1 (RRCReconfigurationCompleteSidelink_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationCompleteSidelink_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationCompleteSidelink_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationCompleteSidelink_r16_IEs__Format : T_Format RRCReconfigurationCompleteSidelink_r16_IEs__Type RRCReconfigurationCompleteSidelink_r16_IEs__cond :=
        proj2_format  RRCReconfigurationCompleteSidelink_r16_IEs__cond RRCReconfigurationCompleteSidelink_r16_IEs__list__Format
    RRCReconfigurationCompleteSidelink_r16_IEs__F1 RRCReconfigurationCompleteSidelink_r16_IEs__F2 RRCReconfigurationCompleteSidelink_r16_IEs__F1F2_cond  RRCReconfigurationCompleteSidelink_r16_IEs__F1F2_cond2 RRCReconfigurationCompleteSidelink_r16_IEs__F2F1_cond.
Opaque RRCReconfigurationCompleteSidelink_r16_IEs__cond RRCReconfigurationCompleteSidelink_r16_IEs__Format.

