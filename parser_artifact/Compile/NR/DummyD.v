Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DummyD__maxNumberTxPortsPerResource__Type : Set :=
 | DummyD__maxNumberTxPortsPerResource__p4
 | DummyD__maxNumberTxPortsPerResource__p8
 | DummyD__maxNumberTxPortsPerResource__p12
 | DummyD__maxNumberTxPortsPerResource__p16
 | DummyD__maxNumberTxPortsPerResource__p24
 | DummyD__maxNumberTxPortsPerResource__p32
.
Definition DummyD__maxNumberTxPortsPerResource__cond := (fun (_ : DummyD__maxNumberTxPortsPerResource__Type) => True).
Lemma DummyD__maxNumberTxPortsPerResource__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyD__maxNumberTxPortsPerResource__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 DummyD__maxNumberTxPortsPerResource__nat__helper.

Definition DummyD__maxNumberTxPortsPerResource__F1 t :=
  match t with
  | DummyD__maxNumberTxPortsPerResource__p4 => 0
  | DummyD__maxNumberTxPortsPerResource__p8 => 1
  | DummyD__maxNumberTxPortsPerResource__p12 => 2
  | DummyD__maxNumberTxPortsPerResource__p16 => 3
  | DummyD__maxNumberTxPortsPerResource__p24 => 4
  | DummyD__maxNumberTxPortsPerResource__p32 => 5
  end.
Definition DummyD__maxNumberTxPortsPerResource__F2 n :=
  match n with
  | 0 => DummyD__maxNumberTxPortsPerResource__p4
  | 1 => DummyD__maxNumberTxPortsPerResource__p8
  | 2 => DummyD__maxNumberTxPortsPerResource__p12
  | 3 => DummyD__maxNumberTxPortsPerResource__p16
  | 4 => DummyD__maxNumberTxPortsPerResource__p24
  | 5 => DummyD__maxNumberTxPortsPerResource__p32
  | _ => DummyD__maxNumberTxPortsPerResource__p4
  end.
Lemma DummyD__maxNumberTxPortsPerResource__F1F2 : forall x : DummyD__maxNumberTxPortsPerResource__Type, (DummyD__maxNumberTxPortsPerResource__F1 x <= 5) /\ DummyD__maxNumberTxPortsPerResource__F2 (DummyD__maxNumberTxPortsPerResource__F1 x) = x. imp_solve. Qed.
Lemma DummyD__maxNumberTxPortsPerResource__F2F1 : forall (y : nat) (H : y <= 5), DummyD__maxNumberTxPortsPerResource__F1 (DummyD__maxNumberTxPortsPerResource__F2 y) = y. enum_solve H y. Qed.

Lemma DummyD__maxNumberResources__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma DummyD__maxNumberResources__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyD__maxNumberResources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyD__maxNumberResources__Type := Z.
Definition DummyD__maxNumberResources__cond := (fun z => (1 <= z <= 64)%Z).
Lemma DummyD__totalNumberTxPorts__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma DummyD__totalNumberTxPorts__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DummyD__totalNumberTxPorts__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyD__totalNumberTxPorts__Type := Z.
Definition DummyD__totalNumberTxPorts__cond := (fun z => (2 <= z <= 256)%Z).
Lemma DummyD__parameterLx__helper1 : (2 <= 4)%Z.  lia. Qed.
Lemma DummyD__parameterLx__helper2 : to_bit_sz (Z.to_nat (4 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DummyD__parameterLx__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyD__parameterLx__Type := Z.
Definition DummyD__parameterLx__cond := (fun z => (2 <= z <= 4)%Z).
Inductive DummyD__amplitudeScalingType__Type : Set :=
 | DummyD__amplitudeScalingType__wideband
 | DummyD__amplitudeScalingType__widebandAndSubband
.
Definition DummyD__amplitudeScalingType__cond := (fun (_ : DummyD__amplitudeScalingType__Type) => True).
Lemma DummyD__amplitudeScalingType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyD__amplitudeScalingType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DummyD__amplitudeScalingType__nat__helper.

Definition DummyD__amplitudeScalingType__F1 t :=
  match t with
  | DummyD__amplitudeScalingType__wideband => 0
  | DummyD__amplitudeScalingType__widebandAndSubband => 1
  end.
Definition DummyD__amplitudeScalingType__F2 n :=
  match n with
  | 0 => DummyD__amplitudeScalingType__wideband
  | 1 => DummyD__amplitudeScalingType__widebandAndSubband
  | _ => DummyD__amplitudeScalingType__wideband
  end.
Lemma DummyD__amplitudeScalingType__F1F2 : forall x : DummyD__amplitudeScalingType__Type, (DummyD__amplitudeScalingType__F1 x <= 1) /\ DummyD__amplitudeScalingType__F2 (DummyD__amplitudeScalingType__F1 x) = x. imp_solve. Qed.
Lemma DummyD__amplitudeScalingType__F2F1 : forall (y : nat) (H : y <= 1), DummyD__amplitudeScalingType__F1 (DummyD__amplitudeScalingType__F2 y) = y. enum_solve H y. Qed.

Inductive DummyD__amplitudeSubsetRestriction__Type : Set :=
 | DummyD__amplitudeSubsetRestriction__supported
.
Definition DummyD__amplitudeSubsetRestriction__cond := (fun (_ : DummyD__amplitudeSubsetRestriction__Type) => True).
Lemma DummyD__amplitudeSubsetRestriction__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyD__amplitudeSubsetRestriction__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DummyD__amplitudeSubsetRestriction__nat__helper.

Definition DummyD__amplitudeSubsetRestriction__F1 t :=
  match t with
  | DummyD__amplitudeSubsetRestriction__supported => 0
  end.
Definition DummyD__amplitudeSubsetRestriction__F2 n :=
  match n with
  | 0 => DummyD__amplitudeSubsetRestriction__supported
  | _ => DummyD__amplitudeSubsetRestriction__supported
  end.
Lemma DummyD__amplitudeSubsetRestriction__F1F2 : forall x : DummyD__amplitudeSubsetRestriction__Type, (DummyD__amplitudeSubsetRestriction__F1 x <= 0) /\ DummyD__amplitudeSubsetRestriction__F2 (DummyD__amplitudeSubsetRestriction__F1 x) = x. imp_solve. Qed.
Lemma DummyD__amplitudeSubsetRestriction__F2F1 : forall (y : nat) (H : y <= 0), DummyD__amplitudeSubsetRestriction__F1 (DummyD__amplitudeSubsetRestriction__F2 y) = y. enum_solve H y. Qed.

Lemma DummyD__maxNumberCSI_RS_PerResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma DummyD__maxNumberCSI_RS_PerResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyD__maxNumberCSI_RS_PerResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyD__maxNumberCSI_RS_PerResourceSet__Type := Z.
Definition DummyD__maxNumberCSI_RS_PerResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record DummyD__Type : Set :=
  make__DummyD__Type {
    DummyD__maxNumberTxPortsPerResource : DummyD__maxNumberTxPortsPerResource__Type ;
    DummyD__maxNumberResources : Z ;
    DummyD__totalNumberTxPorts : Z ;
    DummyD__parameterLx : Z ;
    DummyD__amplitudeScalingType : DummyD__amplitudeScalingType__Type ;
    DummyD__amplitudeSubsetRestriction : option DummyD__amplitudeSubsetRestriction__Type ;
    DummyD__maxNumberCSI_RS_PerResourceSet : Z ;
}.
Definition DummyD__list := (
 Nor DummyD__maxNumberTxPortsPerResource__Type DummyD__maxNumberTxPortsPerResource__cond ::
 Nor Z DummyD__maxNumberResources__cond ::
 Nor Z DummyD__totalNumberTxPorts__cond ::
 Nor Z DummyD__parameterLx__cond ::
 Nor DummyD__amplitudeScalingType__Type DummyD__amplitudeScalingType__cond ::
 Opt DummyD__amplitudeSubsetRestriction__Type DummyD__amplitudeSubsetRestriction__cond ::
 Nor Z DummyD__maxNumberCSI_RS_PerResourceSet__cond ::
 nil).
Definition DummyD__cond z := 
  DummyD__maxNumberTxPortsPerResource__cond (DummyD__maxNumberTxPortsPerResource z) /\
  DummyD__maxNumberResources__cond (DummyD__maxNumberResources z) /\
  DummyD__totalNumberTxPorts__cond (DummyD__totalNumberTxPorts z) /\
  DummyD__parameterLx__cond (DummyD__parameterLx z) /\
  DummyD__amplitudeScalingType__cond (DummyD__amplitudeScalingType z) /\
  opt_cond DummyD__amplitudeSubsetRestriction__cond (DummyD__amplitudeSubsetRestriction z) /\
  DummyD__maxNumberCSI_RS_PerResourceSet__cond (DummyD__maxNumberCSI_RS_PerResourceSet z) /\
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
Definition DummyD__maxNumberTxPortsPerResource__Format : T_Format DummyD__maxNumberTxPortsPerResource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyD__maxNumberTxPortsPerResource__nat__Format DummyD__maxNumberTxPortsPerResource__F1 DummyD__maxNumberTxPortsPerResource__F2 DummyD__maxNumberTxPortsPerResource__F1F2 DummyD__maxNumberTxPortsPerResource__F2F1.

Opaque DummyD__maxNumberTxPortsPerResource__cond DummyD__maxNumberTxPortsPerResource__Format.

Definition DummyD__maxNumberResources__Format : T_Format Z DummyD__maxNumberResources__cond :=
 ranged_int_format (1) (64) DummyD__maxNumberResources__helper1 DummyD__maxNumberResources__helper2.

Opaque DummyD__maxNumberResources__cond DummyD__maxNumberResources__Format.

Definition DummyD__totalNumberTxPorts__Format : T_Format Z DummyD__totalNumberTxPorts__cond :=
 ranged_int_format (2) (256) DummyD__totalNumberTxPorts__helper1 DummyD__totalNumberTxPorts__helper2.

Opaque DummyD__totalNumberTxPorts__cond DummyD__totalNumberTxPorts__Format.

Definition DummyD__parameterLx__Format : T_Format Z DummyD__parameterLx__cond :=
 ranged_int_format (2) (4) DummyD__parameterLx__helper1 DummyD__parameterLx__helper2.

Opaque DummyD__parameterLx__cond DummyD__parameterLx__Format.

Definition DummyD__amplitudeScalingType__Format : T_Format DummyD__amplitudeScalingType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyD__amplitudeScalingType__nat__Format DummyD__amplitudeScalingType__F1 DummyD__amplitudeScalingType__F2 DummyD__amplitudeScalingType__F1F2 DummyD__amplitudeScalingType__F2F1.

Opaque DummyD__amplitudeScalingType__cond DummyD__amplitudeScalingType__Format.

Definition DummyD__amplitudeSubsetRestriction__Format : T_Format DummyD__amplitudeSubsetRestriction__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyD__amplitudeSubsetRestriction__nat__Format DummyD__amplitudeSubsetRestriction__F1 DummyD__amplitudeSubsetRestriction__F2 DummyD__amplitudeSubsetRestriction__F1F2 DummyD__amplitudeSubsetRestriction__F2F1.

Opaque DummyD__amplitudeSubsetRestriction__cond DummyD__amplitudeSubsetRestriction__Format.

Definition DummyD__maxNumberCSI_RS_PerResourceSet__Format : T_Format Z DummyD__maxNumberCSI_RS_PerResourceSet__cond :=
 ranged_int_format (1) (8) DummyD__maxNumberCSI_RS_PerResourceSet__helper1 DummyD__maxNumberCSI_RS_PerResourceSet__helper2.

Opaque DummyD__maxNumberCSI_RS_PerResourceSet__cond DummyD__maxNumberCSI_RS_PerResourceSet__Format.


Definition DummyD__Format_Type := Eval cbn in seq_format_prod DummyD__list.
Definition DummyD__Format_list : DummyD__Format_Type :=
  (DummyD__maxNumberTxPortsPerResource__Format, (DummyD__maxNumberResources__Format, (DummyD__totalNumberTxPorts__Format, (DummyD__parameterLx__Format, (DummyD__amplitudeScalingType__Format, (DummyD__amplitudeSubsetRestriction__Format, (DummyD__maxNumberCSI_RS_PerResourceSet__Format, unit_format))))))).
Definition DummyD__list__Format := (*Eval compute in *) seq_format DummyD__list DummyD__Format_list.
Definition DummyD__F1 z :=
  (DummyD__maxNumberTxPortsPerResource z, (DummyD__maxNumberResources z, (DummyD__totalNumberTxPorts z, (DummyD__parameterLx z, (DummyD__amplitudeScalingType z, (DummyD__amplitudeSubsetRestriction z, (DummyD__maxNumberCSI_RS_PerResourceSet z, tt))))))).
Definition DummyD__F2 (y : seq_type DummyD__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__DummyD__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma DummyD__F1F2_cond (z : DummyD__Type)
  : DummyD__cond z ->
  (seq_cond DummyD__list (DummyD__F1 z)).
intro H. unfold DummyD__cond in H. simpl. auto. Qed.
Lemma DummyD__F1F2_cond2 (z : DummyD__Type)
 : DummyD__F2 (DummyD__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyD__F2F1_cond (y : seq_type DummyD__list)
  : seq_cond DummyD__list y ->
 (DummyD__cond (DummyD__F2 y)) /\  DummyD__F1 (DummyD__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyD__cond. simpl in *. auto.
 - simpl. unfold DummyD__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyD__Format : T_Format DummyD__Type DummyD__cond :=
        proj2_format  DummyD__cond DummyD__list__Format
    DummyD__F1 DummyD__F2 DummyD__F1F2_cond  DummyD__F1F2_cond2 DummyD__F2F1_cond.
Opaque DummyD__cond DummyD__Format.

