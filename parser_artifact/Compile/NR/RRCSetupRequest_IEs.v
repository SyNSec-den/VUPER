Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.InitialUE_Identity.

Opaque InitialUE_Identity__cond InitialUE_Identity__Format.

Require Import NR.EstablishmentCause.

Opaque EstablishmentCause__cond EstablishmentCause__Format.

Definition RRCSetupRequest_IEs__spare__Type := bit_string_fixed.
Definition RRCSetupRequest_IEs__spare__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 1 /\ bit_string_len_prop (fst z) (snd z)).
Record RRCSetupRequest_IEs__Type : Set :=
  make__RRCSetupRequest_IEs__Type {
    RRCSetupRequest_IEs__ue_Identity : InitialUE_Identity__Type ;
    RRCSetupRequest_IEs__establishmentCause : EstablishmentCause__Type ;
    RRCSetupRequest_IEs__spare : RRCSetupRequest_IEs__spare__Type ;
}.
Definition RRCSetupRequest_IEs__list := (
 Nor InitialUE_Identity__Type InitialUE_Identity__cond ::
 Nor EstablishmentCause__Type EstablishmentCause__cond ::
 Nor RRCSetupRequest_IEs__spare__Type RRCSetupRequest_IEs__spare__cond ::
 nil).
Definition RRCSetupRequest_IEs__cond z := 
  InitialUE_Identity__cond (RRCSetupRequest_IEs__ue_Identity z) /\
  EstablishmentCause__cond (RRCSetupRequest_IEs__establishmentCause z) /\
  RRCSetupRequest_IEs__spare__cond (RRCSetupRequest_IEs__spare z) /\
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
Definition RRCSetupRequest_IEs__spare__Format : T_Format RRCSetupRequest_IEs__spare__Type RRCSetupRequest_IEs__spare__cond := (* Eval compute in *) bit_string_fixed_format 1.
Opaque RRCSetupRequest_IEs__spare__cond RRCSetupRequest_IEs__spare__Format.


Definition RRCSetupRequest_IEs__Format_Type := Eval cbn in seq_format_prod RRCSetupRequest_IEs__list.
Definition RRCSetupRequest_IEs__Format_list : RRCSetupRequest_IEs__Format_Type :=
  (InitialUE_Identity__Format, (EstablishmentCause__Format, (RRCSetupRequest_IEs__spare__Format, unit_format))).
Definition RRCSetupRequest_IEs__list__Format := (*Eval compute in *) seq_format RRCSetupRequest_IEs__list RRCSetupRequest_IEs__Format_list.
Definition RRCSetupRequest_IEs__F1 z :=
  (RRCSetupRequest_IEs__ue_Identity z, (RRCSetupRequest_IEs__establishmentCause z, (RRCSetupRequest_IEs__spare z, tt))).
Definition RRCSetupRequest_IEs__F2 (y : seq_type RRCSetupRequest_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RRCSetupRequest_IEs__Type i0 i1 i2
  end.
Lemma RRCSetupRequest_IEs__F1F2_cond (z : RRCSetupRequest_IEs__Type)
  : RRCSetupRequest_IEs__cond z ->
  (seq_cond RRCSetupRequest_IEs__list (RRCSetupRequest_IEs__F1 z)).
intro H. unfold RRCSetupRequest_IEs__cond in H. simpl. auto. Qed.
Lemma RRCSetupRequest_IEs__F1F2_cond2 (z : RRCSetupRequest_IEs__Type)
 : RRCSetupRequest_IEs__F2 (RRCSetupRequest_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetupRequest_IEs__F2F1_cond (y : seq_type RRCSetupRequest_IEs__list)
  : seq_cond RRCSetupRequest_IEs__list y ->
 (RRCSetupRequest_IEs__cond (RRCSetupRequest_IEs__F2 y)) /\  RRCSetupRequest_IEs__F1 (RRCSetupRequest_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetupRequest_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCSetupRequest_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetupRequest_IEs__Format : T_Format RRCSetupRequest_IEs__Type RRCSetupRequest_IEs__cond :=
        proj2_format  RRCSetupRequest_IEs__cond RRCSetupRequest_IEs__list__Format
    RRCSetupRequest_IEs__F1 RRCSetupRequest_IEs__F2 RRCSetupRequest_IEs__F1F2_cond  RRCSetupRequest_IEs__F1F2_cond2 RRCSetupRequest_IEs__F2F1_cond.
Opaque RRCSetupRequest_IEs__cond RRCSetupRequest_IEs__Format.

