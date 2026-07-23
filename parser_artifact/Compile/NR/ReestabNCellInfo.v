Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.CellIdentity.

Opaque CellIdentity__cond CellIdentity__Format.

Definition ReestabNCellInfo__key_gNodeB_Star__Type := bit_string_fixed.
Definition ReestabNCellInfo__key_gNodeB_Star__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 256 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.ShortMAC_I.

Opaque ShortMAC_I__cond ShortMAC_I__Format.

Record ReestabNCellInfo__Type : Set :=
  make__ReestabNCellInfo__Type {
    ReestabNCellInfo__cellIdentity : CellIdentity__Type ;
    ReestabNCellInfo__key_gNodeB_Star : ReestabNCellInfo__key_gNodeB_Star__Type ;
    ReestabNCellInfo__shortMAC_I : ShortMAC_I__Type ;
}.
Definition ReestabNCellInfo__list := (
 Nor CellIdentity__Type CellIdentity__cond ::
 Nor ReestabNCellInfo__key_gNodeB_Star__Type ReestabNCellInfo__key_gNodeB_Star__cond ::
 Nor ShortMAC_I__Type ShortMAC_I__cond ::
 nil).
Definition ReestabNCellInfo__cond z := 
  CellIdentity__cond (ReestabNCellInfo__cellIdentity z) /\
  ReestabNCellInfo__key_gNodeB_Star__cond (ReestabNCellInfo__key_gNodeB_Star z) /\
  ShortMAC_I__cond (ReestabNCellInfo__shortMAC_I z) /\
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
Definition ReestabNCellInfo__key_gNodeB_Star__Format : T_Format ReestabNCellInfo__key_gNodeB_Star__Type ReestabNCellInfo__key_gNodeB_Star__cond := (* Eval compute in *) bit_string_fixed_format 256.
Opaque ReestabNCellInfo__key_gNodeB_Star__cond ReestabNCellInfo__key_gNodeB_Star__Format.


Definition ReestabNCellInfo__Format_Type := Eval cbn in seq_format_prod ReestabNCellInfo__list.
Definition ReestabNCellInfo__Format_list : ReestabNCellInfo__Format_Type :=
  (CellIdentity__Format, (ReestabNCellInfo__key_gNodeB_Star__Format, (ShortMAC_I__Format, unit_format))).
Definition ReestabNCellInfo__list__Format := (*Eval compute in *) seq_format ReestabNCellInfo__list ReestabNCellInfo__Format_list.
Definition ReestabNCellInfo__F1 z :=
  (ReestabNCellInfo__cellIdentity z, (ReestabNCellInfo__key_gNodeB_Star z, (ReestabNCellInfo__shortMAC_I z, tt))).
Definition ReestabNCellInfo__F2 (y : seq_type ReestabNCellInfo__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ReestabNCellInfo__Type i0 i1 i2
  end.
Lemma ReestabNCellInfo__F1F2_cond (z : ReestabNCellInfo__Type)
  : ReestabNCellInfo__cond z ->
  (seq_cond ReestabNCellInfo__list (ReestabNCellInfo__F1 z)).
intro H. unfold ReestabNCellInfo__cond in H. simpl. auto. Qed.
Lemma ReestabNCellInfo__F1F2_cond2 (z : ReestabNCellInfo__Type)
 : ReestabNCellInfo__F2 (ReestabNCellInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReestabNCellInfo__F2F1_cond (y : seq_type ReestabNCellInfo__list)
  : seq_cond ReestabNCellInfo__list y ->
 (ReestabNCellInfo__cond (ReestabNCellInfo__F2 y)) /\  ReestabNCellInfo__F1 (ReestabNCellInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReestabNCellInfo__cond. simpl in *. auto.
 - simpl. unfold ReestabNCellInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReestabNCellInfo__Format : T_Format ReestabNCellInfo__Type ReestabNCellInfo__cond :=
        proj2_format  ReestabNCellInfo__cond ReestabNCellInfo__list__Format
    ReestabNCellInfo__F1 ReestabNCellInfo__F2 ReestabNCellInfo__F1F2_cond  ReestabNCellInfo__F1F2_cond2 ReestabNCellInfo__F2F1_cond.
Opaque ReestabNCellInfo__cond ReestabNCellInfo__Format.

