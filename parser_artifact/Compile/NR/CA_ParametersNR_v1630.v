Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SimulSRS_ForAntennaSwitching_r16.

Opaque SimulSRS_ForAntennaSwitching_r16__cond SimulSRS_ForAntennaSwitching_r16__Format.

Inductive CA_ParametersNR_v1630__beamManagementType_r16__Type : Set :=
 | CA_ParametersNR_v1630__beamManagementType_r16__ibm
 | CA_ParametersNR_v1630__beamManagementType_r16__dummy
.
Definition CA_ParametersNR_v1630__beamManagementType_r16__cond := (fun (_ : CA_ParametersNR_v1630__beamManagementType_r16__Type) => True).
Lemma CA_ParametersNR_v1630__beamManagementType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1630__beamManagementType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1630__beamManagementType_r16__nat__helper.

Definition CA_ParametersNR_v1630__beamManagementType_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1630__beamManagementType_r16__ibm => 0
  | CA_ParametersNR_v1630__beamManagementType_r16__dummy => 1
  end.
Definition CA_ParametersNR_v1630__beamManagementType_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1630__beamManagementType_r16__ibm
  | 1 => CA_ParametersNR_v1630__beamManagementType_r16__dummy
  | _ => CA_ParametersNR_v1630__beamManagementType_r16__ibm
  end.
Lemma CA_ParametersNR_v1630__beamManagementType_r16__F1F2 : forall x : CA_ParametersNR_v1630__beamManagementType_r16__Type, (CA_ParametersNR_v1630__beamManagementType_r16__F1 x <= 1) /\ CA_ParametersNR_v1630__beamManagementType_r16__F2 (CA_ParametersNR_v1630__beamManagementType_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1630__beamManagementType_r16__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1630__beamManagementType_r16__F1 (CA_ParametersNR_v1630__beamManagementType_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Type : Set :=
 | CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classI
 | CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classII
 | CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classIII
.
Definition CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__cond := (fun (_ : CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Type) => True).
Lemma CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__nat__helper.

Definition CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classI => 0
  | CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classII => 1
  | CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classIII => 2
  end.
Definition CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classI
  | 1 => CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classII
  | 2 => CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classIII
  | _ => CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__classI
  end.
Lemma CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1F2 : forall x : CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Type, (CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1 x <= 2) /\ CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F2 (CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1 (CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Type : Set :=
 | CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__supported
.
Definition CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__cond := (fun (_ : CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Type) => True).
Lemma CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__nat__helper.

Definition CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__supported => 0
  end.
Definition CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__supported
  | _ => CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__supported
  end.
Lemma CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1F2 : forall x : CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Type, (CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1 x <= 0) /\ CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F2 (CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1 (CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR_v1630__Type : Set :=
  make__CA_ParametersNR_v1630__Type {
    CA_ParametersNR_v1630__simulTX_SRS_AntSwitchingInterBandUL_CA_r16 : option SimulSRS_ForAntennaSwitching_r16__Type ;
    CA_ParametersNR_v1630__beamManagementType_r16 : option CA_ParametersNR_v1630__beamManagementType_r16__Type ;
    CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16 : option CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Type ;
    CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16 : option CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Type ;
}.
Definition CA_ParametersNR_v1630__list := (
 Opt SimulSRS_ForAntennaSwitching_r16__Type SimulSRS_ForAntennaSwitching_r16__cond ::
 Opt CA_ParametersNR_v1630__beamManagementType_r16__Type CA_ParametersNR_v1630__beamManagementType_r16__cond ::
 Opt CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Type CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__cond ::
 Opt CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Type CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__cond ::
 nil).
Definition CA_ParametersNR_v1630__cond z := 
  opt_cond SimulSRS_ForAntennaSwitching_r16__cond (CA_ParametersNR_v1630__simulTX_SRS_AntSwitchingInterBandUL_CA_r16 z) /\
  opt_cond CA_ParametersNR_v1630__beamManagementType_r16__cond (CA_ParametersNR_v1630__beamManagementType_r16 z) /\
  opt_cond CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__cond (CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16 z) /\
  opt_cond CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__cond (CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16 z) /\
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
Definition CA_ParametersNR_v1630__beamManagementType_r16__Format : T_Format CA_ParametersNR_v1630__beamManagementType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1630__beamManagementType_r16__nat__Format CA_ParametersNR_v1630__beamManagementType_r16__F1 CA_ParametersNR_v1630__beamManagementType_r16__F2 CA_ParametersNR_v1630__beamManagementType_r16__F1F2 CA_ParametersNR_v1630__beamManagementType_r16__F2F1.

Opaque CA_ParametersNR_v1630__beamManagementType_r16__cond CA_ParametersNR_v1630__beamManagementType_r16__Format.

Definition CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Format : T_Format CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__nat__Format CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1 CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F2 CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F1F2 CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__F2F1.

Opaque CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__cond CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Format.

Definition CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Format : T_Format CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__nat__Format CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1 CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F2 CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F1F2 CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__F2F1.

Opaque CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__cond CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Format.


Definition CA_ParametersNR_v1630__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1630__list.
Definition CA_ParametersNR_v1630__Format_list : CA_ParametersNR_v1630__Format_Type :=
  (SimulSRS_ForAntennaSwitching_r16__Format, (CA_ParametersNR_v1630__beamManagementType_r16__Format, (CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16__Format, (CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16__Format, unit_format)))).
Definition CA_ParametersNR_v1630__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1630__list CA_ParametersNR_v1630__Format_list.
Definition CA_ParametersNR_v1630__F1 z :=
  (CA_ParametersNR_v1630__simulTX_SRS_AntSwitchingInterBandUL_CA_r16 z, (CA_ParametersNR_v1630__beamManagementType_r16 z, (CA_ParametersNR_v1630__intraBandFreqSeparationUL_AggBW_GapBW_r16 z, (CA_ParametersNR_v1630__interCA_NonAlignedFrame_B_r16 z, tt)))).
Definition CA_ParametersNR_v1630__F2 (y : seq_type CA_ParametersNR_v1630__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CA_ParametersNR_v1630__Type i0 i1 i2 i3
  end.
Lemma CA_ParametersNR_v1630__F1F2_cond (z : CA_ParametersNR_v1630__Type)
  : CA_ParametersNR_v1630__cond z ->
  (seq_cond CA_ParametersNR_v1630__list (CA_ParametersNR_v1630__F1 z)).
intro H. unfold CA_ParametersNR_v1630__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1630__F1F2_cond2 (z : CA_ParametersNR_v1630__Type)
 : CA_ParametersNR_v1630__F2 (CA_ParametersNR_v1630__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1630__F2F1_cond (y : seq_type CA_ParametersNR_v1630__list)
  : seq_cond CA_ParametersNR_v1630__list y ->
 (CA_ParametersNR_v1630__cond (CA_ParametersNR_v1630__F2 y)) /\  CA_ParametersNR_v1630__F1 (CA_ParametersNR_v1630__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1630__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1630__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1630__Format : T_Format CA_ParametersNR_v1630__Type CA_ParametersNR_v1630__cond :=
        proj2_format  CA_ParametersNR_v1630__cond CA_ParametersNR_v1630__list__Format
    CA_ParametersNR_v1630__F1 CA_ParametersNR_v1630__F2 CA_ParametersNR_v1630__F1F2_cond  CA_ParametersNR_v1630__F1F2_cond2 CA_ParametersNR_v1630__F2F1_cond.
Opaque CA_ParametersNR_v1630__cond CA_ParametersNR_v1630__Format.

