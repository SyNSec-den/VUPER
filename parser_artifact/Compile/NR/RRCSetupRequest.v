Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRCSetupRequest_IEs.

Opaque RRCSetupRequest_IEs__cond RRCSetupRequest_IEs__Format.

Record RRCSetupRequest__Type : Set :=
  make__RRCSetupRequest__Type {
    RRCSetupRequest__rrcSetupRequest : RRCSetupRequest_IEs__Type ;
}.
Definition RRCSetupRequest__list := (
 Nor RRCSetupRequest_IEs__Type RRCSetupRequest_IEs__cond ::
 nil).
Definition RRCSetupRequest__cond z := 
  RRCSetupRequest_IEs__cond (RRCSetupRequest__rrcSetupRequest z) /\
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

Definition RRCSetupRequest__Format_Type := Eval cbn in seq_format_prod RRCSetupRequest__list.
Definition RRCSetupRequest__Format_list : RRCSetupRequest__Format_Type :=
  (RRCSetupRequest_IEs__Format, unit_format).
Definition RRCSetupRequest__list__Format := (*Eval compute in *) seq_format RRCSetupRequest__list RRCSetupRequest__Format_list.
Definition RRCSetupRequest__F1 z :=
  (RRCSetupRequest__rrcSetupRequest z, tt).
Definition RRCSetupRequest__F2 (y : seq_type RRCSetupRequest__list) :=
  match y with
  | (i0, _)=>
    make__RRCSetupRequest__Type i0
  end.
Lemma RRCSetupRequest__F1F2_cond (z : RRCSetupRequest__Type)
  : RRCSetupRequest__cond z ->
  (seq_cond RRCSetupRequest__list (RRCSetupRequest__F1 z)).
intro H. unfold RRCSetupRequest__cond in H. simpl. auto. Qed.
Lemma RRCSetupRequest__F1F2_cond2 (z : RRCSetupRequest__Type)
 : RRCSetupRequest__F2 (RRCSetupRequest__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetupRequest__F2F1_cond (y : seq_type RRCSetupRequest__list)
  : seq_cond RRCSetupRequest__list y ->
 (RRCSetupRequest__cond (RRCSetupRequest__F2 y)) /\  RRCSetupRequest__F1 (RRCSetupRequest__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetupRequest__cond. simpl in *. auto.
 - simpl. unfold RRCSetupRequest__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetupRequest__Format : T_Format RRCSetupRequest__Type RRCSetupRequest__cond :=
        proj2_format  RRCSetupRequest__cond RRCSetupRequest__list__Format
    RRCSetupRequest__F1 RRCSetupRequest__F2 RRCSetupRequest__F1F2_cond  RRCSetupRequest__F1F2_cond2 RRCSetupRequest__F2F1_cond.
Opaque RRCSetupRequest__cond RRCSetupRequest__Format.

