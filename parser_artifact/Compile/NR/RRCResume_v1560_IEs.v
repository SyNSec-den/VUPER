Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SK_Counter.

Opaque SK_Counter__cond SK_Counter__Format.

Require Import NR.RRCResume_v1610_IEs.

Opaque RRCResume_v1610_IEs__cond RRCResume_v1610_IEs__Format.

Record RRCResume_v1560_IEs__Type : Set :=
  make__RRCResume_v1560_IEs__Type {
    RRCResume_v1560_IEs__radioBearerConfig2 : option octet_string ;
    RRCResume_v1560_IEs__sk_Counter : option SK_Counter__Type ;
    RRCResume_v1560_IEs__nonCriticalExtension : option RRCResume_v1610_IEs__Type ;
}.
Definition RRCResume_v1560_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SK_Counter__Type SK_Counter__cond ::
 Opt RRCResume_v1610_IEs__Type RRCResume_v1610_IEs__cond ::
 nil).
Definition RRCResume_v1560_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCResume_v1560_IEs__radioBearerConfig2 z) /\
  opt_cond SK_Counter__cond (RRCResume_v1560_IEs__sk_Counter z) /\
  opt_cond RRCResume_v1610_IEs__cond (RRCResume_v1560_IEs__nonCriticalExtension z) /\
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

Definition RRCResume_v1560_IEs__Format_Type := Eval cbn in seq_format_prod RRCResume_v1560_IEs__list.
Definition RRCResume_v1560_IEs__Format_list : RRCResume_v1560_IEs__Format_Type :=
  (octet_string_nc__Format, (SK_Counter__Format, (RRCResume_v1610_IEs__Format, unit_format))).
Definition RRCResume_v1560_IEs__list__Format := (*Eval compute in *) seq_format RRCResume_v1560_IEs__list RRCResume_v1560_IEs__Format_list.
Definition RRCResume_v1560_IEs__F1 z :=
  (RRCResume_v1560_IEs__radioBearerConfig2 z, (RRCResume_v1560_IEs__sk_Counter z, (RRCResume_v1560_IEs__nonCriticalExtension z, tt))).
Definition RRCResume_v1560_IEs__F2 (y : seq_type RRCResume_v1560_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RRCResume_v1560_IEs__Type i0 i1 i2
  end.
Lemma RRCResume_v1560_IEs__F1F2_cond (z : RRCResume_v1560_IEs__Type)
  : RRCResume_v1560_IEs__cond z ->
  (seq_cond RRCResume_v1560_IEs__list (RRCResume_v1560_IEs__F1 z)).
intro H. unfold RRCResume_v1560_IEs__cond in H. simpl. auto. Qed.
Lemma RRCResume_v1560_IEs__F1F2_cond2 (z : RRCResume_v1560_IEs__Type)
 : RRCResume_v1560_IEs__F2 (RRCResume_v1560_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResume_v1560_IEs__F2F1_cond (y : seq_type RRCResume_v1560_IEs__list)
  : seq_cond RRCResume_v1560_IEs__list y ->
 (RRCResume_v1560_IEs__cond (RRCResume_v1560_IEs__F2 y)) /\  RRCResume_v1560_IEs__F1 (RRCResume_v1560_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResume_v1560_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCResume_v1560_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResume_v1560_IEs__Format : T_Format RRCResume_v1560_IEs__Type RRCResume_v1560_IEs__cond :=
        proj2_format  RRCResume_v1560_IEs__cond RRCResume_v1560_IEs__list__Format
    RRCResume_v1560_IEs__F1 RRCResume_v1560_IEs__F2 RRCResume_v1560_IEs__F1F2_cond  RRCResume_v1560_IEs__F1F2_cond2 RRCResume_v1560_IEs__F2F1_cond.
Opaque RRCResume_v1560_IEs__cond RRCResume_v1560_IEs__Format.

