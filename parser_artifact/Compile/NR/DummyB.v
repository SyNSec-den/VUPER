Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DummyB__maxNumberTxPortsPerResource__Type : Set :=
 | DummyB__maxNumberTxPortsPerResource__p2
 | DummyB__maxNumberTxPortsPerResource__p4
 | DummyB__maxNumberTxPortsPerResource__p8
 | DummyB__maxNumberTxPortsPerResource__p12
 | DummyB__maxNumberTxPortsPerResource__p16
 | DummyB__maxNumberTxPortsPerResource__p24
 | DummyB__maxNumberTxPortsPerResource__p32
.
Definition DummyB__maxNumberTxPortsPerResource__cond := (fun (_ : DummyB__maxNumberTxPortsPerResource__Type) => True).
Lemma DummyB__maxNumberTxPortsPerResource__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyB__maxNumberTxPortsPerResource__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 DummyB__maxNumberTxPortsPerResource__nat__helper.

Definition DummyB__maxNumberTxPortsPerResource__F1 t :=
  match t with
  | DummyB__maxNumberTxPortsPerResource__p2 => 0
  | DummyB__maxNumberTxPortsPerResource__p4 => 1
  | DummyB__maxNumberTxPortsPerResource__p8 => 2
  | DummyB__maxNumberTxPortsPerResource__p12 => 3
  | DummyB__maxNumberTxPortsPerResource__p16 => 4
  | DummyB__maxNumberTxPortsPerResource__p24 => 5
  | DummyB__maxNumberTxPortsPerResource__p32 => 6
  end.
Definition DummyB__maxNumberTxPortsPerResource__F2 n :=
  match n with
  | 0 => DummyB__maxNumberTxPortsPerResource__p2
  | 1 => DummyB__maxNumberTxPortsPerResource__p4
  | 2 => DummyB__maxNumberTxPortsPerResource__p8
  | 3 => DummyB__maxNumberTxPortsPerResource__p12
  | 4 => DummyB__maxNumberTxPortsPerResource__p16
  | 5 => DummyB__maxNumberTxPortsPerResource__p24
  | 6 => DummyB__maxNumberTxPortsPerResource__p32
  | _ => DummyB__maxNumberTxPortsPerResource__p2
  end.
Lemma DummyB__maxNumberTxPortsPerResource__F1F2 : forall x : DummyB__maxNumberTxPortsPerResource__Type, (DummyB__maxNumberTxPortsPerResource__F1 x <= 6) /\ DummyB__maxNumberTxPortsPerResource__F2 (DummyB__maxNumberTxPortsPerResource__F1 x) = x. imp_solve. Qed.
Lemma DummyB__maxNumberTxPortsPerResource__F2F1 : forall (y : nat) (H : y <= 6), DummyB__maxNumberTxPortsPerResource__F1 (DummyB__maxNumberTxPortsPerResource__F2 y) = y. enum_solve H y. Qed.

Lemma DummyB__maxNumberResources__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma DummyB__maxNumberResources__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyB__maxNumberResources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyB__maxNumberResources__Type := Z.
Definition DummyB__maxNumberResources__cond := (fun z => (1 <= z <= 64)%Z).
Lemma DummyB__totalNumberTxPorts__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma DummyB__totalNumberTxPorts__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DummyB__totalNumberTxPorts__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyB__totalNumberTxPorts__Type := Z.
Definition DummyB__totalNumberTxPorts__cond := (fun z => (2 <= z <= 256)%Z).
Inductive DummyB__supportedCodebookMode__Type : Set :=
 | DummyB__supportedCodebookMode__mode1
 | DummyB__supportedCodebookMode__mode1AndMode2
.
Definition DummyB__supportedCodebookMode__cond := (fun (_ : DummyB__supportedCodebookMode__Type) => True).
Lemma DummyB__supportedCodebookMode__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyB__supportedCodebookMode__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DummyB__supportedCodebookMode__nat__helper.

Definition DummyB__supportedCodebookMode__F1 t :=
  match t with
  | DummyB__supportedCodebookMode__mode1 => 0
  | DummyB__supportedCodebookMode__mode1AndMode2 => 1
  end.
Definition DummyB__supportedCodebookMode__F2 n :=
  match n with
  | 0 => DummyB__supportedCodebookMode__mode1
  | 1 => DummyB__supportedCodebookMode__mode1AndMode2
  | _ => DummyB__supportedCodebookMode__mode1
  end.
Lemma DummyB__supportedCodebookMode__F1F2 : forall x : DummyB__supportedCodebookMode__Type, (DummyB__supportedCodebookMode__F1 x <= 1) /\ DummyB__supportedCodebookMode__F2 (DummyB__supportedCodebookMode__F1 x) = x. imp_solve. Qed.
Lemma DummyB__supportedCodebookMode__F2F1 : forall (y : nat) (H : y <= 1), DummyB__supportedCodebookMode__F1 (DummyB__supportedCodebookMode__F2 y) = y. enum_solve H y. Qed.

Lemma DummyB__maxNumberCSI_RS_PerResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma DummyB__maxNumberCSI_RS_PerResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyB__maxNumberCSI_RS_PerResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyB__maxNumberCSI_RS_PerResourceSet__Type := Z.
Definition DummyB__maxNumberCSI_RS_PerResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record DummyB__Type : Set :=
  make__DummyB__Type {
    DummyB__maxNumberTxPortsPerResource : DummyB__maxNumberTxPortsPerResource__Type ;
    DummyB__maxNumberResources : Z ;
    DummyB__totalNumberTxPorts : Z ;
    DummyB__supportedCodebookMode : DummyB__supportedCodebookMode__Type ;
    DummyB__maxNumberCSI_RS_PerResourceSet : Z ;
}.
Definition DummyB__list := (
 Nor DummyB__maxNumberTxPortsPerResource__Type DummyB__maxNumberTxPortsPerResource__cond ::
 Nor Z DummyB__maxNumberResources__cond ::
 Nor Z DummyB__totalNumberTxPorts__cond ::
 Nor DummyB__supportedCodebookMode__Type DummyB__supportedCodebookMode__cond ::
 Nor Z DummyB__maxNumberCSI_RS_PerResourceSet__cond ::
 nil).
Definition DummyB__cond z := 
  DummyB__maxNumberTxPortsPerResource__cond (DummyB__maxNumberTxPortsPerResource z) /\
  DummyB__maxNumberResources__cond (DummyB__maxNumberResources z) /\
  DummyB__totalNumberTxPorts__cond (DummyB__totalNumberTxPorts z) /\
  DummyB__supportedCodebookMode__cond (DummyB__supportedCodebookMode z) /\
  DummyB__maxNumberCSI_RS_PerResourceSet__cond (DummyB__maxNumberCSI_RS_PerResourceSet z) /\
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
Definition DummyB__maxNumberTxPortsPerResource__Format : T_Format DummyB__maxNumberTxPortsPerResource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyB__maxNumberTxPortsPerResource__nat__Format DummyB__maxNumberTxPortsPerResource__F1 DummyB__maxNumberTxPortsPerResource__F2 DummyB__maxNumberTxPortsPerResource__F1F2 DummyB__maxNumberTxPortsPerResource__F2F1.

Opaque DummyB__maxNumberTxPortsPerResource__cond DummyB__maxNumberTxPortsPerResource__Format.

Definition DummyB__maxNumberResources__Format : T_Format Z DummyB__maxNumberResources__cond :=
 ranged_int_format (1) (64) DummyB__maxNumberResources__helper1 DummyB__maxNumberResources__helper2.

Opaque DummyB__maxNumberResources__cond DummyB__maxNumberResources__Format.

Definition DummyB__totalNumberTxPorts__Format : T_Format Z DummyB__totalNumberTxPorts__cond :=
 ranged_int_format (2) (256) DummyB__totalNumberTxPorts__helper1 DummyB__totalNumberTxPorts__helper2.

Opaque DummyB__totalNumberTxPorts__cond DummyB__totalNumberTxPorts__Format.

Definition DummyB__supportedCodebookMode__Format : T_Format DummyB__supportedCodebookMode__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyB__supportedCodebookMode__nat__Format DummyB__supportedCodebookMode__F1 DummyB__supportedCodebookMode__F2 DummyB__supportedCodebookMode__F1F2 DummyB__supportedCodebookMode__F2F1.

Opaque DummyB__supportedCodebookMode__cond DummyB__supportedCodebookMode__Format.

Definition DummyB__maxNumberCSI_RS_PerResourceSet__Format : T_Format Z DummyB__maxNumberCSI_RS_PerResourceSet__cond :=
 ranged_int_format (1) (8) DummyB__maxNumberCSI_RS_PerResourceSet__helper1 DummyB__maxNumberCSI_RS_PerResourceSet__helper2.

Opaque DummyB__maxNumberCSI_RS_PerResourceSet__cond DummyB__maxNumberCSI_RS_PerResourceSet__Format.


Definition DummyB__Format_Type := Eval cbn in seq_format_prod DummyB__list.
Definition DummyB__Format_list : DummyB__Format_Type :=
  (DummyB__maxNumberTxPortsPerResource__Format, (DummyB__maxNumberResources__Format, (DummyB__totalNumberTxPorts__Format, (DummyB__supportedCodebookMode__Format, (DummyB__maxNumberCSI_RS_PerResourceSet__Format, unit_format))))).
Definition DummyB__list__Format := (*Eval compute in *) seq_format DummyB__list DummyB__Format_list.
Definition DummyB__F1 z :=
  (DummyB__maxNumberTxPortsPerResource z, (DummyB__maxNumberResources z, (DummyB__totalNumberTxPorts z, (DummyB__supportedCodebookMode z, (DummyB__maxNumberCSI_RS_PerResourceSet z, tt))))).
Definition DummyB__F2 (y : seq_type DummyB__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__DummyB__Type i0 i1 i2 i3 i4
  end.
Lemma DummyB__F1F2_cond (z : DummyB__Type)
  : DummyB__cond z ->
  (seq_cond DummyB__list (DummyB__F1 z)).
intro H. unfold DummyB__cond in H. simpl. auto. Qed.
Lemma DummyB__F1F2_cond2 (z : DummyB__Type)
 : DummyB__F2 (DummyB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyB__F2F1_cond (y : seq_type DummyB__list)
  : seq_cond DummyB__list y ->
 (DummyB__cond (DummyB__F2 y)) /\  DummyB__F1 (DummyB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyB__cond. simpl in *. auto.
 - simpl. unfold DummyB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyB__Format : T_Format DummyB__Type DummyB__cond :=
        proj2_format  DummyB__cond DummyB__list__Format
    DummyB__F1 DummyB__F2 DummyB__F1F2_cond  DummyB__F1F2_cond2 DummyB__F2F1_cond.
Opaque DummyB__cond DummyB__Format.

