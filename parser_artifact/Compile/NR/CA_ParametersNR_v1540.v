Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__helper1 : (5 <= 32)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__helper2 : to_bit_sz (Z.to_nat (32 - 5)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 5))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__Type := Z.
Definition CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__cond := (fun z => (5 <= z <= 32)%Z).
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__Type := Z.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond := (fun z => (1 <= z <= 64)%Z).
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__Type := Z.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond := (fun z => (2 <= z <= 256)%Z).
Record CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type : Set :=
  make__CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type {
    CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC : option Z ;
    CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC : option Z ;
}.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list := (
 Opt Z CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond ::
 Opt Z CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond ::
 nil).
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond z := 
  opt_cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC z) /\
  opt_cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC z) /\
  True.

Lemma CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__helper1 : (5 <= 32)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__helper2 : to_bit_sz (Z.to_nat (32 - 5)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 5))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__Type := Z.
Definition CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__cond := (fun z => (5 <= z <= 32)%Z).
Inductive CA_ParametersNR_v1540__dualPA_Architecture__Type : Set :=
 | CA_ParametersNR_v1540__dualPA_Architecture__supported
.
Definition CA_ParametersNR_v1540__dualPA_Architecture__cond := (fun (_ : CA_ParametersNR_v1540__dualPA_Architecture__Type) => True).
Lemma CA_ParametersNR_v1540__dualPA_Architecture__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1540__dualPA_Architecture__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1540__dualPA_Architecture__nat__helper.

Definition CA_ParametersNR_v1540__dualPA_Architecture__F1 t :=
  match t with
  | CA_ParametersNR_v1540__dualPA_Architecture__supported => 0
  end.
Definition CA_ParametersNR_v1540__dualPA_Architecture__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1540__dualPA_Architecture__supported
  | _ => CA_ParametersNR_v1540__dualPA_Architecture__supported
  end.
Lemma CA_ParametersNR_v1540__dualPA_Architecture__F1F2 : forall x : CA_ParametersNR_v1540__dualPA_Architecture__Type, (CA_ParametersNR_v1540__dualPA_Architecture__F1 x <= 0) /\ CA_ParametersNR_v1540__dualPA_Architecture__F2 (CA_ParametersNR_v1540__dualPA_Architecture__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1540__dualPA_Architecture__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1540__dualPA_Architecture__F1 (CA_ParametersNR_v1540__dualPA_Architecture__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR_v1540__Type : Set :=
  make__CA_ParametersNR_v1540__Type {
    CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC : option Z ;
    CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb : option CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type ;
    CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC : option Z ;
    CA_ParametersNR_v1540__dualPA_Architecture : option CA_ParametersNR_v1540__dualPA_Architecture__Type ;
}.
Definition CA_ParametersNR_v1540__list := (
 Opt Z CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__cond ::
 Opt CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond ::
 Opt Z CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__cond ::
 Opt CA_ParametersNR_v1540__dualPA_Architecture__Type CA_ParametersNR_v1540__dualPA_Architecture__cond ::
 nil).
Definition CA_ParametersNR_v1540__cond z := 
  opt_cond CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__cond (CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC z) /\
  opt_cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb z) /\
  opt_cond CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__cond (CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC z) /\
  opt_cond CA_ParametersNR_v1540__dualPA_Architecture__cond (CA_ParametersNR_v1540__dualPA_Architecture z) /\
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
Definition CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__Format : T_Format Z CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__cond :=
 ranged_int_format (5) (32) CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__helper1 CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__helper2.

Opaque CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__cond CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__Format.

Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__Format : T_Format Z CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond :=
 ranged_int_format (1) (64) CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper1 CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper2.

Opaque CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__Format.

Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__Format : T_Format Z CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond :=
 ranged_int_format (2) (256) CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper1 CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__helper2.

Opaque CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__Format.


Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format_list : CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format_Type :=
  (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC__Format, (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC__Format, unit_format)).
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format_list.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1 z :=
  (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__maxNumberSimultaneousNZP_CSI_RS_ActBWP_AllCC z, (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__totalNumberPortsSimultaneousNZP_CSI_RS_ActBWP_AllCC z, tt)).
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2 (y : seq_type CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type i0 i1
  end.
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1F2_cond (z : CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type)
  : CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond z ->
  (seq_cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1 z)).
intro H. unfold CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1F2_cond2 (z : CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type)
 : CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2 (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2F1_cond (y : seq_type CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list)
  : seq_cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list y ->
 (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2 y)) /\  CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1 (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format : T_Format CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Type CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond :=
        proj2_format  CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__list__Format
    CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1 CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2 CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1F2_cond  CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F1F2_cond2 CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__F2F1_cond.
Opaque CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__cond CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format.

Definition CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__Format : T_Format Z CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__cond :=
 ranged_int_format (5) (32) CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__helper1 CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__helper2.

Opaque CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__cond CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__Format.

Definition CA_ParametersNR_v1540__dualPA_Architecture__Format : T_Format CA_ParametersNR_v1540__dualPA_Architecture__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1540__dualPA_Architecture__nat__Format CA_ParametersNR_v1540__dualPA_Architecture__F1 CA_ParametersNR_v1540__dualPA_Architecture__F2 CA_ParametersNR_v1540__dualPA_Architecture__F1F2 CA_ParametersNR_v1540__dualPA_Architecture__F2F1.

Opaque CA_ParametersNR_v1540__dualPA_Architecture__cond CA_ParametersNR_v1540__dualPA_Architecture__Format.


Definition CA_ParametersNR_v1540__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1540__list.
Definition CA_ParametersNR_v1540__Format_list : CA_ParametersNR_v1540__Format_Type :=
  (CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC__Format, (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb__Format, (CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC__Format, (CA_ParametersNR_v1540__dualPA_Architecture__Format, unit_format)))).
Definition CA_ParametersNR_v1540__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1540__list CA_ParametersNR_v1540__Format_list.
Definition CA_ParametersNR_v1540__F1 z :=
  (CA_ParametersNR_v1540__simultaneousSRS_AssocCSI_RS_AllCC z, (CA_ParametersNR_v1540__csi_RS_IM_ReceptionForFeedbackPerBandComb z, (CA_ParametersNR_v1540__simultaneousCSI_ReportsAllCC z, (CA_ParametersNR_v1540__dualPA_Architecture z, tt)))).
Definition CA_ParametersNR_v1540__F2 (y : seq_type CA_ParametersNR_v1540__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CA_ParametersNR_v1540__Type i0 i1 i2 i3
  end.
Lemma CA_ParametersNR_v1540__F1F2_cond (z : CA_ParametersNR_v1540__Type)
  : CA_ParametersNR_v1540__cond z ->
  (seq_cond CA_ParametersNR_v1540__list (CA_ParametersNR_v1540__F1 z)).
intro H. unfold CA_ParametersNR_v1540__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1540__F1F2_cond2 (z : CA_ParametersNR_v1540__Type)
 : CA_ParametersNR_v1540__F2 (CA_ParametersNR_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1540__F2F1_cond (y : seq_type CA_ParametersNR_v1540__list)
  : seq_cond CA_ParametersNR_v1540__list y ->
 (CA_ParametersNR_v1540__cond (CA_ParametersNR_v1540__F2 y)) /\  CA_ParametersNR_v1540__F1 (CA_ParametersNR_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1540__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1540__Format : T_Format CA_ParametersNR_v1540__Type CA_ParametersNR_v1540__cond :=
        proj2_format  CA_ParametersNR_v1540__cond CA_ParametersNR_v1540__list__Format
    CA_ParametersNR_v1540__F1 CA_ParametersNR_v1540__F2 CA_ParametersNR_v1540__F1F2_cond  CA_ParametersNR_v1540__F1F2_cond2 CA_ParametersNR_v1540__F2F1_cond.
Opaque CA_ParametersNR_v1540__cond CA_ParametersNR_v1540__Format.

