Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DummyE__maxNumberTxPortsPerResource__Type : Set :=
 | DummyE__maxNumberTxPortsPerResource__p4
 | DummyE__maxNumberTxPortsPerResource__p8
 | DummyE__maxNumberTxPortsPerResource__p12
 | DummyE__maxNumberTxPortsPerResource__p16
 | DummyE__maxNumberTxPortsPerResource__p24
 | DummyE__maxNumberTxPortsPerResource__p32
.
Definition DummyE__maxNumberTxPortsPerResource__cond := (fun (_ : DummyE__maxNumberTxPortsPerResource__Type) => True).
Lemma DummyE__maxNumberTxPortsPerResource__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyE__maxNumberTxPortsPerResource__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 DummyE__maxNumberTxPortsPerResource__nat__helper.

Definition DummyE__maxNumberTxPortsPerResource__F1 t :=
  match t with
  | DummyE__maxNumberTxPortsPerResource__p4 => 0
  | DummyE__maxNumberTxPortsPerResource__p8 => 1
  | DummyE__maxNumberTxPortsPerResource__p12 => 2
  | DummyE__maxNumberTxPortsPerResource__p16 => 3
  | DummyE__maxNumberTxPortsPerResource__p24 => 4
  | DummyE__maxNumberTxPortsPerResource__p32 => 5
  end.
Definition DummyE__maxNumberTxPortsPerResource__F2 n :=
  match n with
  | 0 => DummyE__maxNumberTxPortsPerResource__p4
  | 1 => DummyE__maxNumberTxPortsPerResource__p8
  | 2 => DummyE__maxNumberTxPortsPerResource__p12
  | 3 => DummyE__maxNumberTxPortsPerResource__p16
  | 4 => DummyE__maxNumberTxPortsPerResource__p24
  | 5 => DummyE__maxNumberTxPortsPerResource__p32
  | _ => DummyE__maxNumberTxPortsPerResource__p4
  end.
Lemma DummyE__maxNumberTxPortsPerResource__F1F2 : forall x : DummyE__maxNumberTxPortsPerResource__Type, (DummyE__maxNumberTxPortsPerResource__F1 x <= 5) /\ DummyE__maxNumberTxPortsPerResource__F2 (DummyE__maxNumberTxPortsPerResource__F1 x) = x. imp_solve. Qed.
Lemma DummyE__maxNumberTxPortsPerResource__F2F1 : forall (y : nat) (H : y <= 5), DummyE__maxNumberTxPortsPerResource__F1 (DummyE__maxNumberTxPortsPerResource__F2 y) = y. enum_solve H y. Qed.

Lemma DummyE__maxNumberResources__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma DummyE__maxNumberResources__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyE__maxNumberResources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyE__maxNumberResources__Type := Z.
Definition DummyE__maxNumberResources__cond := (fun z => (1 <= z <= 64)%Z).
Lemma DummyE__totalNumberTxPorts__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma DummyE__totalNumberTxPorts__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DummyE__totalNumberTxPorts__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyE__totalNumberTxPorts__Type := Z.
Definition DummyE__totalNumberTxPorts__cond := (fun z => (2 <= z <= 256)%Z).
Lemma DummyE__parameterLx__helper1 : (2 <= 4)%Z.  lia. Qed.
Lemma DummyE__parameterLx__helper2 : to_bit_sz (Z.to_nat (4 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DummyE__parameterLx__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyE__parameterLx__Type := Z.
Definition DummyE__parameterLx__cond := (fun z => (2 <= z <= 4)%Z).
Inductive DummyE__amplitudeScalingType__Type : Set :=
 | DummyE__amplitudeScalingType__wideband
 | DummyE__amplitudeScalingType__widebandAndSubband
.
Definition DummyE__amplitudeScalingType__cond := (fun (_ : DummyE__amplitudeScalingType__Type) => True).
Lemma DummyE__amplitudeScalingType__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyE__amplitudeScalingType__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DummyE__amplitudeScalingType__nat__helper.

Definition DummyE__amplitudeScalingType__F1 t :=
  match t with
  | DummyE__amplitudeScalingType__wideband => 0
  | DummyE__amplitudeScalingType__widebandAndSubband => 1
  end.
Definition DummyE__amplitudeScalingType__F2 n :=
  match n with
  | 0 => DummyE__amplitudeScalingType__wideband
  | 1 => DummyE__amplitudeScalingType__widebandAndSubband
  | _ => DummyE__amplitudeScalingType__wideband
  end.
Lemma DummyE__amplitudeScalingType__F1F2 : forall x : DummyE__amplitudeScalingType__Type, (DummyE__amplitudeScalingType__F1 x <= 1) /\ DummyE__amplitudeScalingType__F2 (DummyE__amplitudeScalingType__F1 x) = x. imp_solve. Qed.
Lemma DummyE__amplitudeScalingType__F2F1 : forall (y : nat) (H : y <= 1), DummyE__amplitudeScalingType__F1 (DummyE__amplitudeScalingType__F2 y) = y. enum_solve H y. Qed.

Lemma DummyE__maxNumberCSI_RS_PerResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma DummyE__maxNumberCSI_RS_PerResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyE__maxNumberCSI_RS_PerResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyE__maxNumberCSI_RS_PerResourceSet__Type := Z.
Definition DummyE__maxNumberCSI_RS_PerResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record DummyE__Type : Set :=
  make__DummyE__Type {
    DummyE__maxNumberTxPortsPerResource : DummyE__maxNumberTxPortsPerResource__Type ;
    DummyE__maxNumberResources : Z ;
    DummyE__totalNumberTxPorts : Z ;
    DummyE__parameterLx : Z ;
    DummyE__amplitudeScalingType : DummyE__amplitudeScalingType__Type ;
    DummyE__maxNumberCSI_RS_PerResourceSet : Z ;
}.
Definition DummyE__list := (
 Nor DummyE__maxNumberTxPortsPerResource__Type DummyE__maxNumberTxPortsPerResource__cond ::
 Nor Z DummyE__maxNumberResources__cond ::
 Nor Z DummyE__totalNumberTxPorts__cond ::
 Nor Z DummyE__parameterLx__cond ::
 Nor DummyE__amplitudeScalingType__Type DummyE__amplitudeScalingType__cond ::
 Nor Z DummyE__maxNumberCSI_RS_PerResourceSet__cond ::
 nil).
Definition DummyE__cond z := 
  DummyE__maxNumberTxPortsPerResource__cond (DummyE__maxNumberTxPortsPerResource z) /\
  DummyE__maxNumberResources__cond (DummyE__maxNumberResources z) /\
  DummyE__totalNumberTxPorts__cond (DummyE__totalNumberTxPorts z) /\
  DummyE__parameterLx__cond (DummyE__parameterLx z) /\
  DummyE__amplitudeScalingType__cond (DummyE__amplitudeScalingType z) /\
  DummyE__maxNumberCSI_RS_PerResourceSet__cond (DummyE__maxNumberCSI_RS_PerResourceSet z) /\
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
Definition DummyE__maxNumberTxPortsPerResource__Format : T_Format DummyE__maxNumberTxPortsPerResource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyE__maxNumberTxPortsPerResource__nat__Format DummyE__maxNumberTxPortsPerResource__F1 DummyE__maxNumberTxPortsPerResource__F2 DummyE__maxNumberTxPortsPerResource__F1F2 DummyE__maxNumberTxPortsPerResource__F2F1.

Opaque DummyE__maxNumberTxPortsPerResource__cond DummyE__maxNumberTxPortsPerResource__Format.

Definition DummyE__maxNumberResources__Format : T_Format Z DummyE__maxNumberResources__cond :=
 ranged_int_format (1) (64) DummyE__maxNumberResources__helper1 DummyE__maxNumberResources__helper2.

Opaque DummyE__maxNumberResources__cond DummyE__maxNumberResources__Format.

Definition DummyE__totalNumberTxPorts__Format : T_Format Z DummyE__totalNumberTxPorts__cond :=
 ranged_int_format (2) (256) DummyE__totalNumberTxPorts__helper1 DummyE__totalNumberTxPorts__helper2.

Opaque DummyE__totalNumberTxPorts__cond DummyE__totalNumberTxPorts__Format.

Definition DummyE__parameterLx__Format : T_Format Z DummyE__parameterLx__cond :=
 ranged_int_format (2) (4) DummyE__parameterLx__helper1 DummyE__parameterLx__helper2.

Opaque DummyE__parameterLx__cond DummyE__parameterLx__Format.

Definition DummyE__amplitudeScalingType__Format : T_Format DummyE__amplitudeScalingType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyE__amplitudeScalingType__nat__Format DummyE__amplitudeScalingType__F1 DummyE__amplitudeScalingType__F2 DummyE__amplitudeScalingType__F1F2 DummyE__amplitudeScalingType__F2F1.

Opaque DummyE__amplitudeScalingType__cond DummyE__amplitudeScalingType__Format.

Definition DummyE__maxNumberCSI_RS_PerResourceSet__Format : T_Format Z DummyE__maxNumberCSI_RS_PerResourceSet__cond :=
 ranged_int_format (1) (8) DummyE__maxNumberCSI_RS_PerResourceSet__helper1 DummyE__maxNumberCSI_RS_PerResourceSet__helper2.

Opaque DummyE__maxNumberCSI_RS_PerResourceSet__cond DummyE__maxNumberCSI_RS_PerResourceSet__Format.


Definition DummyE__Format_Type := Eval cbn in seq_format_prod DummyE__list.
Definition DummyE__Format_list : DummyE__Format_Type :=
  (DummyE__maxNumberTxPortsPerResource__Format, (DummyE__maxNumberResources__Format, (DummyE__totalNumberTxPorts__Format, (DummyE__parameterLx__Format, (DummyE__amplitudeScalingType__Format, (DummyE__maxNumberCSI_RS_PerResourceSet__Format, unit_format)))))).
Definition DummyE__list__Format := (*Eval compute in *) seq_format DummyE__list DummyE__Format_list.
Definition DummyE__F1 z :=
  (DummyE__maxNumberTxPortsPerResource z, (DummyE__maxNumberResources z, (DummyE__totalNumberTxPorts z, (DummyE__parameterLx z, (DummyE__amplitudeScalingType z, (DummyE__maxNumberCSI_RS_PerResourceSet z, tt)))))).
Definition DummyE__F2 (y : seq_type DummyE__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__DummyE__Type i0 i1 i2 i3 i4 i5
  end.
Lemma DummyE__F1F2_cond (z : DummyE__Type)
  : DummyE__cond z ->
  (seq_cond DummyE__list (DummyE__F1 z)).
intro H. unfold DummyE__cond in H. simpl. auto. Qed.
Lemma DummyE__F1F2_cond2 (z : DummyE__Type)
 : DummyE__F2 (DummyE__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyE__F2F1_cond (y : seq_type DummyE__list)
  : seq_cond DummyE__list y ->
 (DummyE__cond (DummyE__F2 y)) /\  DummyE__F1 (DummyE__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyE__cond. simpl in *. auto.
 - simpl. unfold DummyE__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyE__Format : T_Format DummyE__Type DummyE__cond :=
        proj2_format  DummyE__cond DummyE__list__Format
    DummyE__F1 DummyE__F2 DummyE__F1F2_cond  DummyE__F1F2_cond2 DummyE__F2F1_cond.
Opaque DummyE__cond DummyE__Format.

