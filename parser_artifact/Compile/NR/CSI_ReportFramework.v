Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__Type := Z.
Definition CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__cond := (fun z => (1 <= z <= 4)%Z).
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__Type := Z.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__cond := (fun z => (1 <= z <= 4)%Z).
Lemma CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__Type := Z.
Definition CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__cond := (fun z => (0 <= z <= 4)%Z).
Lemma CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__Type := Z.
Definition CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__cond := (fun z => (1 <= z <= 4)%Z).
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__Type := Z.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__cond := (fun z => (1 <= z <= 4)%Z).
Inductive CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Type : Set :=
 | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n3
 | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n7
 | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n15
 | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n31
 | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n63
 | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n128
.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__cond := (fun (_ : CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Type) => True).
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__nat__helper.

Definition CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1 t :=
  match t with
  | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n3 => 0
  | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n7 => 1
  | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n15 => 2
  | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n31 => 3
  | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n63 => 4
  | CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n128 => 5
  end.
Definition CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F2 n :=
  match n with
  | 0 => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n3
  | 1 => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n7
  | 2 => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n15
  | 3 => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n31
  | 4 => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n63
  | 5 => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n128
  | _ => CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__n3
  end.
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1F2 : forall x : CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Type, (CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1 x <= 5) /\ CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F2 (CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F2F1 : forall (y : nat) (H : y <= 5), CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1 (CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__Type := Z.
Definition CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__cond := (fun z => (0 <= z <= 4)%Z).
Lemma CSI_ReportFramework__simultaneousCSI_ReportsPerCC__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma CSI_ReportFramework__simultaneousCSI_ReportsPerCC__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportFramework__simultaneousCSI_ReportsPerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportFramework__simultaneousCSI_ReportsPerCC__Type := Z.
Definition CSI_ReportFramework__simultaneousCSI_ReportsPerCC__cond := (fun z => (1 <= z <= 8)%Z).
Record CSI_ReportFramework__Type : Set :=
  make__CSI_ReportFramework__Type {
    CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report : Z ;
    CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report : Z ;
    CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report : Z ;
    CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport : Z ;
    CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport : Z ;
    CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC : CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Type ;
    CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport : Z ;
    CSI_ReportFramework__simultaneousCSI_ReportsPerCC : Z ;
}.
Definition CSI_ReportFramework__list := (
 Nor Z CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__cond ::
 Nor Z CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__cond ::
 Nor Z CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__cond ::
 Nor Z CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__cond ::
 Nor Z CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__cond ::
 Nor CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Type CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__cond ::
 Nor Z CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__cond ::
 Nor Z CSI_ReportFramework__simultaneousCSI_ReportsPerCC__cond ::
 nil).
Definition CSI_ReportFramework__cond z := 
  CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__cond (CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report z) /\
  CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__cond (CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report z) /\
  CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__cond (CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report z) /\
  CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__cond (CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport z) /\
  CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__cond (CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport z) /\
  CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__cond (CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC z) /\
  CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__cond (CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport z) /\
  CSI_ReportFramework__simultaneousCSI_ReportsPerCC__cond (CSI_ReportFramework__simultaneousCSI_ReportsPerCC z) /\
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
Definition CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__Format : T_Format Z CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__cond :=
 ranged_int_format (1) (4) CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__helper1 CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__helper2.

Opaque CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__cond CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__Format.

Definition CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__Format : T_Format Z CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__cond :=
 ranged_int_format (1) (4) CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__helper1 CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__helper2.

Opaque CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__cond CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__Format.

Definition CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__Format : T_Format Z CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__cond :=
 ranged_int_format (0) (4) CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__helper1 CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__helper2.

Opaque CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__cond CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__Format.

Definition CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__Format : T_Format Z CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__cond :=
 ranged_int_format (1) (4) CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__helper1 CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__helper2.

Opaque CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__cond CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__Format.

Definition CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__Format : T_Format Z CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__cond :=
 ranged_int_format (1) (4) CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__helper1 CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__helper2.

Opaque CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__cond CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__Format.

Definition CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Format : T_Format CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__nat__Format CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1 CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F2 CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F1F2 CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__F2F1.

Opaque CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__cond CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Format.

Definition CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__Format : T_Format Z CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__cond :=
 ranged_int_format (0) (4) CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__helper1 CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__helper2.

Opaque CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__cond CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__Format.

Definition CSI_ReportFramework__simultaneousCSI_ReportsPerCC__Format : T_Format Z CSI_ReportFramework__simultaneousCSI_ReportsPerCC__cond :=
 ranged_int_format (1) (8) CSI_ReportFramework__simultaneousCSI_ReportsPerCC__helper1 CSI_ReportFramework__simultaneousCSI_ReportsPerCC__helper2.

Opaque CSI_ReportFramework__simultaneousCSI_ReportsPerCC__cond CSI_ReportFramework__simultaneousCSI_ReportsPerCC__Format.


Definition CSI_ReportFramework__Format_Type := Eval cbn in seq_format_prod CSI_ReportFramework__list.
Definition CSI_ReportFramework__Format_list : CSI_ReportFramework__Format_Type :=
  (CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report__Format, (CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report__Format, (CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report__Format, (CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport__Format, (CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport__Format, (CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC__Format, (CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport__Format, (CSI_ReportFramework__simultaneousCSI_ReportsPerCC__Format, unit_format)))))))).
Definition CSI_ReportFramework__list__Format := (*Eval compute in *) seq_format CSI_ReportFramework__list CSI_ReportFramework__Format_list.
Definition CSI_ReportFramework__F1 z :=
  (CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForCSI_Report z, (CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForCSI_Report z, (CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForCSI_Report z, (CSI_ReportFramework__maxNumberPeriodicCSI_PerBWP_ForBeamReport z, (CSI_ReportFramework__maxNumberAperiodicCSI_PerBWP_ForBeamReport z, (CSI_ReportFramework__maxNumberAperiodicCSI_triggeringStatePerCC z, (CSI_ReportFramework__maxNumberSemiPersistentCSI_PerBWP_ForBeamReport z, (CSI_ReportFramework__simultaneousCSI_ReportsPerCC z, tt)))))))).
Definition CSI_ReportFramework__F2 (y : seq_type CSI_ReportFramework__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__CSI_ReportFramework__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma CSI_ReportFramework__F1F2_cond (z : CSI_ReportFramework__Type)
  : CSI_ReportFramework__cond z ->
  (seq_cond CSI_ReportFramework__list (CSI_ReportFramework__F1 z)).
intro H. unfold CSI_ReportFramework__cond in H. simpl. auto. Qed.
Lemma CSI_ReportFramework__F1F2_cond2 (z : CSI_ReportFramework__Type)
 : CSI_ReportFramework__F2 (CSI_ReportFramework__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportFramework__F2F1_cond (y : seq_type CSI_ReportFramework__list)
  : seq_cond CSI_ReportFramework__list y ->
 (CSI_ReportFramework__cond (CSI_ReportFramework__F2 y)) /\  CSI_ReportFramework__F1 (CSI_ReportFramework__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportFramework__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportFramework__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportFramework__Format : T_Format CSI_ReportFramework__Type CSI_ReportFramework__cond :=
        proj2_format  CSI_ReportFramework__cond CSI_ReportFramework__list__Format
    CSI_ReportFramework__F1 CSI_ReportFramework__F2 CSI_ReportFramework__F1F2_cond  CSI_ReportFramework__F1F2_cond2 CSI_ReportFramework__F2F1_cond.
Opaque CSI_ReportFramework__cond CSI_ReportFramework__Format.

