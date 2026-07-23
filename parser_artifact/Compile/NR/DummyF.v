Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DummyF__maxNumberPeriodicCSI_ReportPerBWP__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma DummyF__maxNumberPeriodicCSI_ReportPerBWP__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyF__maxNumberPeriodicCSI_ReportPerBWP__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyF__maxNumberPeriodicCSI_ReportPerBWP__Type := Z.
Definition DummyF__maxNumberPeriodicCSI_ReportPerBWP__cond := (fun z => (1 <= z <= 4)%Z).
Lemma DummyF__maxNumberAperiodicCSI_ReportPerBWP__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma DummyF__maxNumberAperiodicCSI_ReportPerBWP__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyF__maxNumberAperiodicCSI_ReportPerBWP__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyF__maxNumberAperiodicCSI_ReportPerBWP__Type := Z.
Definition DummyF__maxNumberAperiodicCSI_ReportPerBWP__cond := (fun z => (1 <= z <= 4)%Z).
Lemma DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__Type := Z.
Definition DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__cond := (fun z => (0 <= z <= 4)%Z).
Lemma DummyF__simultaneousCSI_ReportsAllCC__helper1 : (5 <= 32)%Z.  lia. Qed.
Lemma DummyF__simultaneousCSI_ReportsAllCC__helper2 : to_bit_sz (Z.to_nat (32 - 5)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 5))%Z). { apply Zorder.Zle_minus_le_0. apply DummyF__simultaneousCSI_ReportsAllCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyF__simultaneousCSI_ReportsAllCC__Type := Z.
Definition DummyF__simultaneousCSI_ReportsAllCC__cond := (fun z => (5 <= z <= 32)%Z).
Record DummyF__Type : Set :=
  make__DummyF__Type {
    DummyF__maxNumberPeriodicCSI_ReportPerBWP : Z ;
    DummyF__maxNumberAperiodicCSI_ReportPerBWP : Z ;
    DummyF__maxNumberSemiPersistentCSI_ReportPerBWP : Z ;
    DummyF__simultaneousCSI_ReportsAllCC : Z ;
}.
Definition DummyF__list := (
 Nor Z DummyF__maxNumberPeriodicCSI_ReportPerBWP__cond ::
 Nor Z DummyF__maxNumberAperiodicCSI_ReportPerBWP__cond ::
 Nor Z DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__cond ::
 Nor Z DummyF__simultaneousCSI_ReportsAllCC__cond ::
 nil).
Definition DummyF__cond z := 
  DummyF__maxNumberPeriodicCSI_ReportPerBWP__cond (DummyF__maxNumberPeriodicCSI_ReportPerBWP z) /\
  DummyF__maxNumberAperiodicCSI_ReportPerBWP__cond (DummyF__maxNumberAperiodicCSI_ReportPerBWP z) /\
  DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__cond (DummyF__maxNumberSemiPersistentCSI_ReportPerBWP z) /\
  DummyF__simultaneousCSI_ReportsAllCC__cond (DummyF__simultaneousCSI_ReportsAllCC z) /\
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
Definition DummyF__maxNumberPeriodicCSI_ReportPerBWP__Format : T_Format Z DummyF__maxNumberPeriodicCSI_ReportPerBWP__cond :=
 ranged_int_format (1) (4) DummyF__maxNumberPeriodicCSI_ReportPerBWP__helper1 DummyF__maxNumberPeriodicCSI_ReportPerBWP__helper2.

Opaque DummyF__maxNumberPeriodicCSI_ReportPerBWP__cond DummyF__maxNumberPeriodicCSI_ReportPerBWP__Format.

Definition DummyF__maxNumberAperiodicCSI_ReportPerBWP__Format : T_Format Z DummyF__maxNumberAperiodicCSI_ReportPerBWP__cond :=
 ranged_int_format (1) (4) DummyF__maxNumberAperiodicCSI_ReportPerBWP__helper1 DummyF__maxNumberAperiodicCSI_ReportPerBWP__helper2.

Opaque DummyF__maxNumberAperiodicCSI_ReportPerBWP__cond DummyF__maxNumberAperiodicCSI_ReportPerBWP__Format.

Definition DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__Format : T_Format Z DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__cond :=
 ranged_int_format (0) (4) DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__helper1 DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__helper2.

Opaque DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__cond DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__Format.

Definition DummyF__simultaneousCSI_ReportsAllCC__Format : T_Format Z DummyF__simultaneousCSI_ReportsAllCC__cond :=
 ranged_int_format (5) (32) DummyF__simultaneousCSI_ReportsAllCC__helper1 DummyF__simultaneousCSI_ReportsAllCC__helper2.

Opaque DummyF__simultaneousCSI_ReportsAllCC__cond DummyF__simultaneousCSI_ReportsAllCC__Format.


Definition DummyF__Format_Type := Eval cbn in seq_format_prod DummyF__list.
Definition DummyF__Format_list : DummyF__Format_Type :=
  (DummyF__maxNumberPeriodicCSI_ReportPerBWP__Format, (DummyF__maxNumberAperiodicCSI_ReportPerBWP__Format, (DummyF__maxNumberSemiPersistentCSI_ReportPerBWP__Format, (DummyF__simultaneousCSI_ReportsAllCC__Format, unit_format)))).
Definition DummyF__list__Format := (*Eval compute in *) seq_format DummyF__list DummyF__Format_list.
Definition DummyF__F1 z :=
  (DummyF__maxNumberPeriodicCSI_ReportPerBWP z, (DummyF__maxNumberAperiodicCSI_ReportPerBWP z, (DummyF__maxNumberSemiPersistentCSI_ReportPerBWP z, (DummyF__simultaneousCSI_ReportsAllCC z, tt)))).
Definition DummyF__F2 (y : seq_type DummyF__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__DummyF__Type i0 i1 i2 i3
  end.
Lemma DummyF__F1F2_cond (z : DummyF__Type)
  : DummyF__cond z ->
  (seq_cond DummyF__list (DummyF__F1 z)).
intro H. unfold DummyF__cond in H. simpl. auto. Qed.
Lemma DummyF__F1F2_cond2 (z : DummyF__Type)
 : DummyF__F2 (DummyF__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyF__F2F1_cond (y : seq_type DummyF__list)
  : seq_cond DummyF__list y ->
 (DummyF__cond (DummyF__F2 y)) /\  DummyF__F1 (DummyF__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyF__cond. simpl in *. auto.
 - simpl. unfold DummyF__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyF__Format : T_Format DummyF__Type DummyF__cond :=
        proj2_format  DummyF__cond DummyF__list__Format
    DummyF__F1 DummyF__F2 DummyF__F1F2_cond  DummyF__F1F2_cond2 DummyF__F2F1_cond.
Opaque DummyF__cond DummyF__Format.

