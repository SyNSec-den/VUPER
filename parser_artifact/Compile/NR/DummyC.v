Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DummyC__maxNumberTxPortsPerResource__Type : Set :=
 | DummyC__maxNumberTxPortsPerResource__p8
 | DummyC__maxNumberTxPortsPerResource__p16
 | DummyC__maxNumberTxPortsPerResource__p32
.
Definition DummyC__maxNumberTxPortsPerResource__cond := (fun (_ : DummyC__maxNumberTxPortsPerResource__Type) => True).
Lemma DummyC__maxNumberTxPortsPerResource__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyC__maxNumberTxPortsPerResource__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DummyC__maxNumberTxPortsPerResource__nat__helper.

Definition DummyC__maxNumberTxPortsPerResource__F1 t :=
  match t with
  | DummyC__maxNumberTxPortsPerResource__p8 => 0
  | DummyC__maxNumberTxPortsPerResource__p16 => 1
  | DummyC__maxNumberTxPortsPerResource__p32 => 2
  end.
Definition DummyC__maxNumberTxPortsPerResource__F2 n :=
  match n with
  | 0 => DummyC__maxNumberTxPortsPerResource__p8
  | 1 => DummyC__maxNumberTxPortsPerResource__p16
  | 2 => DummyC__maxNumberTxPortsPerResource__p32
  | _ => DummyC__maxNumberTxPortsPerResource__p8
  end.
Lemma DummyC__maxNumberTxPortsPerResource__F1F2 : forall x : DummyC__maxNumberTxPortsPerResource__Type, (DummyC__maxNumberTxPortsPerResource__F1 x <= 2) /\ DummyC__maxNumberTxPortsPerResource__F2 (DummyC__maxNumberTxPortsPerResource__F1 x) = x. imp_solve. Qed.
Lemma DummyC__maxNumberTxPortsPerResource__F2F1 : forall (y : nat) (H : y <= 2), DummyC__maxNumberTxPortsPerResource__F1 (DummyC__maxNumberTxPortsPerResource__F2 y) = y. enum_solve H y. Qed.

Lemma DummyC__maxNumberResources__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma DummyC__maxNumberResources__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyC__maxNumberResources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyC__maxNumberResources__Type := Z.
Definition DummyC__maxNumberResources__cond := (fun z => (1 <= z <= 64)%Z).
Lemma DummyC__totalNumberTxPorts__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma DummyC__totalNumberTxPorts__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DummyC__totalNumberTxPorts__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyC__totalNumberTxPorts__Type := Z.
Definition DummyC__totalNumberTxPorts__cond := (fun z => (2 <= z <= 256)%Z).
Inductive DummyC__supportedCodebookMode__Type : Set :=
 | DummyC__supportedCodebookMode__mode1
 | DummyC__supportedCodebookMode__mode2
 | DummyC__supportedCodebookMode__both
.
Definition DummyC__supportedCodebookMode__cond := (fun (_ : DummyC__supportedCodebookMode__Type) => True).
Lemma DummyC__supportedCodebookMode__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyC__supportedCodebookMode__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DummyC__supportedCodebookMode__nat__helper.

Definition DummyC__supportedCodebookMode__F1 t :=
  match t with
  | DummyC__supportedCodebookMode__mode1 => 0
  | DummyC__supportedCodebookMode__mode2 => 1
  | DummyC__supportedCodebookMode__both => 2
  end.
Definition DummyC__supportedCodebookMode__F2 n :=
  match n with
  | 0 => DummyC__supportedCodebookMode__mode1
  | 1 => DummyC__supportedCodebookMode__mode2
  | 2 => DummyC__supportedCodebookMode__both
  | _ => DummyC__supportedCodebookMode__mode1
  end.
Lemma DummyC__supportedCodebookMode__F1F2 : forall x : DummyC__supportedCodebookMode__Type, (DummyC__supportedCodebookMode__F1 x <= 2) /\ DummyC__supportedCodebookMode__F2 (DummyC__supportedCodebookMode__F1 x) = x. imp_solve. Qed.
Lemma DummyC__supportedCodebookMode__F2F1 : forall (y : nat) (H : y <= 2), DummyC__supportedCodebookMode__F1 (DummyC__supportedCodebookMode__F2 y) = y. enum_solve H y. Qed.

Inductive DummyC__supportedNumberPanels__Type : Set :=
 | DummyC__supportedNumberPanels__n2
 | DummyC__supportedNumberPanels__n4
.
Definition DummyC__supportedNumberPanels__cond := (fun (_ : DummyC__supportedNumberPanels__Type) => True).
Lemma DummyC__supportedNumberPanels__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyC__supportedNumberPanels__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DummyC__supportedNumberPanels__nat__helper.

Definition DummyC__supportedNumberPanels__F1 t :=
  match t with
  | DummyC__supportedNumberPanels__n2 => 0
  | DummyC__supportedNumberPanels__n4 => 1
  end.
Definition DummyC__supportedNumberPanels__F2 n :=
  match n with
  | 0 => DummyC__supportedNumberPanels__n2
  | 1 => DummyC__supportedNumberPanels__n4
  | _ => DummyC__supportedNumberPanels__n2
  end.
Lemma DummyC__supportedNumberPanels__F1F2 : forall x : DummyC__supportedNumberPanels__Type, (DummyC__supportedNumberPanels__F1 x <= 1) /\ DummyC__supportedNumberPanels__F2 (DummyC__supportedNumberPanels__F1 x) = x. imp_solve. Qed.
Lemma DummyC__supportedNumberPanels__F2F1 : forall (y : nat) (H : y <= 1), DummyC__supportedNumberPanels__F1 (DummyC__supportedNumberPanels__F2 y) = y. enum_solve H y. Qed.

Lemma DummyC__maxNumberCSI_RS_PerResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma DummyC__maxNumberCSI_RS_PerResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyC__maxNumberCSI_RS_PerResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyC__maxNumberCSI_RS_PerResourceSet__Type := Z.
Definition DummyC__maxNumberCSI_RS_PerResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record DummyC__Type : Set :=
  make__DummyC__Type {
    DummyC__maxNumberTxPortsPerResource : DummyC__maxNumberTxPortsPerResource__Type ;
    DummyC__maxNumberResources : Z ;
    DummyC__totalNumberTxPorts : Z ;
    DummyC__supportedCodebookMode : DummyC__supportedCodebookMode__Type ;
    DummyC__supportedNumberPanels : DummyC__supportedNumberPanels__Type ;
    DummyC__maxNumberCSI_RS_PerResourceSet : Z ;
}.
Definition DummyC__list := (
 Nor DummyC__maxNumberTxPortsPerResource__Type DummyC__maxNumberTxPortsPerResource__cond ::
 Nor Z DummyC__maxNumberResources__cond ::
 Nor Z DummyC__totalNumberTxPorts__cond ::
 Nor DummyC__supportedCodebookMode__Type DummyC__supportedCodebookMode__cond ::
 Nor DummyC__supportedNumberPanels__Type DummyC__supportedNumberPanels__cond ::
 Nor Z DummyC__maxNumberCSI_RS_PerResourceSet__cond ::
 nil).
Definition DummyC__cond z := 
  DummyC__maxNumberTxPortsPerResource__cond (DummyC__maxNumberTxPortsPerResource z) /\
  DummyC__maxNumberResources__cond (DummyC__maxNumberResources z) /\
  DummyC__totalNumberTxPorts__cond (DummyC__totalNumberTxPorts z) /\
  DummyC__supportedCodebookMode__cond (DummyC__supportedCodebookMode z) /\
  DummyC__supportedNumberPanels__cond (DummyC__supportedNumberPanels z) /\
  DummyC__maxNumberCSI_RS_PerResourceSet__cond (DummyC__maxNumberCSI_RS_PerResourceSet z) /\
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
Definition DummyC__maxNumberTxPortsPerResource__Format : T_Format DummyC__maxNumberTxPortsPerResource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyC__maxNumberTxPortsPerResource__nat__Format DummyC__maxNumberTxPortsPerResource__F1 DummyC__maxNumberTxPortsPerResource__F2 DummyC__maxNumberTxPortsPerResource__F1F2 DummyC__maxNumberTxPortsPerResource__F2F1.

Opaque DummyC__maxNumberTxPortsPerResource__cond DummyC__maxNumberTxPortsPerResource__Format.

Definition DummyC__maxNumberResources__Format : T_Format Z DummyC__maxNumberResources__cond :=
 ranged_int_format (1) (64) DummyC__maxNumberResources__helper1 DummyC__maxNumberResources__helper2.

Opaque DummyC__maxNumberResources__cond DummyC__maxNumberResources__Format.

Definition DummyC__totalNumberTxPorts__Format : T_Format Z DummyC__totalNumberTxPorts__cond :=
 ranged_int_format (2) (256) DummyC__totalNumberTxPorts__helper1 DummyC__totalNumberTxPorts__helper2.

Opaque DummyC__totalNumberTxPorts__cond DummyC__totalNumberTxPorts__Format.

Definition DummyC__supportedCodebookMode__Format : T_Format DummyC__supportedCodebookMode__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyC__supportedCodebookMode__nat__Format DummyC__supportedCodebookMode__F1 DummyC__supportedCodebookMode__F2 DummyC__supportedCodebookMode__F1F2 DummyC__supportedCodebookMode__F2F1.

Opaque DummyC__supportedCodebookMode__cond DummyC__supportedCodebookMode__Format.

Definition DummyC__supportedNumberPanels__Format : T_Format DummyC__supportedNumberPanels__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyC__supportedNumberPanels__nat__Format DummyC__supportedNumberPanels__F1 DummyC__supportedNumberPanels__F2 DummyC__supportedNumberPanels__F1F2 DummyC__supportedNumberPanels__F2F1.

Opaque DummyC__supportedNumberPanels__cond DummyC__supportedNumberPanels__Format.

Definition DummyC__maxNumberCSI_RS_PerResourceSet__Format : T_Format Z DummyC__maxNumberCSI_RS_PerResourceSet__cond :=
 ranged_int_format (1) (8) DummyC__maxNumberCSI_RS_PerResourceSet__helper1 DummyC__maxNumberCSI_RS_PerResourceSet__helper2.

Opaque DummyC__maxNumberCSI_RS_PerResourceSet__cond DummyC__maxNumberCSI_RS_PerResourceSet__Format.


Definition DummyC__Format_Type := Eval cbn in seq_format_prod DummyC__list.
Definition DummyC__Format_list : DummyC__Format_Type :=
  (DummyC__maxNumberTxPortsPerResource__Format, (DummyC__maxNumberResources__Format, (DummyC__totalNumberTxPorts__Format, (DummyC__supportedCodebookMode__Format, (DummyC__supportedNumberPanels__Format, (DummyC__maxNumberCSI_RS_PerResourceSet__Format, unit_format)))))).
Definition DummyC__list__Format := (*Eval compute in *) seq_format DummyC__list DummyC__Format_list.
Definition DummyC__F1 z :=
  (DummyC__maxNumberTxPortsPerResource z, (DummyC__maxNumberResources z, (DummyC__totalNumberTxPorts z, (DummyC__supportedCodebookMode z, (DummyC__supportedNumberPanels z, (DummyC__maxNumberCSI_RS_PerResourceSet z, tt)))))).
Definition DummyC__F2 (y : seq_type DummyC__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__DummyC__Type i0 i1 i2 i3 i4 i5
  end.
Lemma DummyC__F1F2_cond (z : DummyC__Type)
  : DummyC__cond z ->
  (seq_cond DummyC__list (DummyC__F1 z)).
intro H. unfold DummyC__cond in H. simpl. auto. Qed.
Lemma DummyC__F1F2_cond2 (z : DummyC__Type)
 : DummyC__F2 (DummyC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyC__F2F1_cond (y : seq_type DummyC__list)
  : seq_cond DummyC__list y ->
 (DummyC__cond (DummyC__F2 y)) /\  DummyC__F1 (DummyC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyC__cond. simpl in *. auto.
 - simpl. unfold DummyC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyC__Format : T_Format DummyC__Type DummyC__cond :=
        proj2_format  DummyC__cond DummyC__list__Format
    DummyC__F1 DummyC__F2 DummyC__F1F2_cond  DummyC__F1F2_cond2 DummyC__F2F1_cond.
Opaque DummyC__cond DummyC__Format.

