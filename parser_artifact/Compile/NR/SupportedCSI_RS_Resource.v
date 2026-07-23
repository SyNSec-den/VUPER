Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Type : Set :=
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p2
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p4
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p8
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p12
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p16
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p24
 | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p32
.
Definition SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__cond := (fun (_ : SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Type) => True).
Lemma SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__nat__helper.

Definition SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1 t :=
  match t with
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p2 => 0
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p4 => 1
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p8 => 2
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p12 => 3
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p16 => 4
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p24 => 5
  | SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p32 => 6
  end.
Definition SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F2 n :=
  match n with
  | 0 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p2
  | 1 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p4
  | 2 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p8
  | 3 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p12
  | 4 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p16
  | 5 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p24
  | 6 => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p32
  | _ => SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__p2
  end.
Lemma SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1F2 : forall x : SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Type, (SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1 x <= 6) /\ SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F2 (SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1 x) = x. imp_solve. Qed.
Lemma SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F2F1 : forall (y : nat) (H : y <= 6), SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1 (SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F2 y) = y. enum_solve H y. Qed.

Lemma SupportedCSI_RS_Resource__maxNumberResourcesPerBand__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma SupportedCSI_RS_Resource__maxNumberResourcesPerBand__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SupportedCSI_RS_Resource__maxNumberResourcesPerBand__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SupportedCSI_RS_Resource__maxNumberResourcesPerBand__Type := Z.
Definition SupportedCSI_RS_Resource__maxNumberResourcesPerBand__cond := (fun z => (1 <= z <= 64)%Z).
Lemma SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__Type := Z.
Definition SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__cond := (fun z => (2 <= z <= 256)%Z).
Record SupportedCSI_RS_Resource__Type : Set :=
  make__SupportedCSI_RS_Resource__Type {
    SupportedCSI_RS_Resource__maxNumberTxPortsPerResource : SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Type ;
    SupportedCSI_RS_Resource__maxNumberResourcesPerBand : Z ;
    SupportedCSI_RS_Resource__totalNumberTxPortsPerBand : Z ;
}.
Definition SupportedCSI_RS_Resource__list := (
 Nor SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Type SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__cond ::
 Nor Z SupportedCSI_RS_Resource__maxNumberResourcesPerBand__cond ::
 Nor Z SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__cond ::
 nil).
Definition SupportedCSI_RS_Resource__cond z := 
  SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__cond (SupportedCSI_RS_Resource__maxNumberTxPortsPerResource z) /\
  SupportedCSI_RS_Resource__maxNumberResourcesPerBand__cond (SupportedCSI_RS_Resource__maxNumberResourcesPerBand z) /\
  SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__cond (SupportedCSI_RS_Resource__totalNumberTxPortsPerBand z) /\
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
Definition SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Format : T_Format SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__nat__Format SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1 SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F2 SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F1F2 SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__F2F1.

Opaque SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__cond SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Format.

Definition SupportedCSI_RS_Resource__maxNumberResourcesPerBand__Format : T_Format Z SupportedCSI_RS_Resource__maxNumberResourcesPerBand__cond :=
 ranged_int_format (1) (64) SupportedCSI_RS_Resource__maxNumberResourcesPerBand__helper1 SupportedCSI_RS_Resource__maxNumberResourcesPerBand__helper2.

Opaque SupportedCSI_RS_Resource__maxNumberResourcesPerBand__cond SupportedCSI_RS_Resource__maxNumberResourcesPerBand__Format.

Definition SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__Format : T_Format Z SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__cond :=
 ranged_int_format (2) (256) SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__helper1 SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__helper2.

Opaque SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__cond SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__Format.


Definition SupportedCSI_RS_Resource__Format_Type := Eval cbn in seq_format_prod SupportedCSI_RS_Resource__list.
Definition SupportedCSI_RS_Resource__Format_list : SupportedCSI_RS_Resource__Format_Type :=
  (SupportedCSI_RS_Resource__maxNumberTxPortsPerResource__Format, (SupportedCSI_RS_Resource__maxNumberResourcesPerBand__Format, (SupportedCSI_RS_Resource__totalNumberTxPortsPerBand__Format, unit_format))).
Definition SupportedCSI_RS_Resource__list__Format := (*Eval compute in *) seq_format SupportedCSI_RS_Resource__list SupportedCSI_RS_Resource__Format_list.
Definition SupportedCSI_RS_Resource__F1 z :=
  (SupportedCSI_RS_Resource__maxNumberTxPortsPerResource z, (SupportedCSI_RS_Resource__maxNumberResourcesPerBand z, (SupportedCSI_RS_Resource__totalNumberTxPortsPerBand z, tt))).
Definition SupportedCSI_RS_Resource__F2 (y : seq_type SupportedCSI_RS_Resource__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SupportedCSI_RS_Resource__Type i0 i1 i2
  end.
Lemma SupportedCSI_RS_Resource__F1F2_cond (z : SupportedCSI_RS_Resource__Type)
  : SupportedCSI_RS_Resource__cond z ->
  (seq_cond SupportedCSI_RS_Resource__list (SupportedCSI_RS_Resource__F1 z)).
intro H. unfold SupportedCSI_RS_Resource__cond in H. simpl. auto. Qed.
Lemma SupportedCSI_RS_Resource__F1F2_cond2 (z : SupportedCSI_RS_Resource__Type)
 : SupportedCSI_RS_Resource__F2 (SupportedCSI_RS_Resource__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SupportedCSI_RS_Resource__F2F1_cond (y : seq_type SupportedCSI_RS_Resource__list)
  : seq_cond SupportedCSI_RS_Resource__list y ->
 (SupportedCSI_RS_Resource__cond (SupportedCSI_RS_Resource__F2 y)) /\  SupportedCSI_RS_Resource__F1 (SupportedCSI_RS_Resource__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SupportedCSI_RS_Resource__cond. simpl in *. auto.
 - simpl. unfold SupportedCSI_RS_Resource__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SupportedCSI_RS_Resource__Format : T_Format SupportedCSI_RS_Resource__Type SupportedCSI_RS_Resource__cond :=
        proj2_format  SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__list__Format
    SupportedCSI_RS_Resource__F1 SupportedCSI_RS_Resource__F2 SupportedCSI_RS_Resource__F1F2_cond  SupportedCSI_RS_Resource__F1F2_cond2 SupportedCSI_RS_Resource__F2F1_cond.
Opaque SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__Format.

