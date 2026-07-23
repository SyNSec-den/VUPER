Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PDU_SessionID.

Opaque PDU_SessionID__cond PDU_SessionID__Format.

Inductive SDAP_Config__sdap_HeaderDL__Type : Set :=
 | SDAP_Config__sdap_HeaderDL__present
 | SDAP_Config__sdap_HeaderDL__absent
.
Definition SDAP_Config__sdap_HeaderDL__cond := (fun (_ : SDAP_Config__sdap_HeaderDL__Type) => True).
Lemma SDAP_Config__sdap_HeaderDL__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDAP_Config__sdap_HeaderDL__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SDAP_Config__sdap_HeaderDL__nat__helper.

Definition SDAP_Config__sdap_HeaderDL__F1 t :=
  match t with
  | SDAP_Config__sdap_HeaderDL__present => 0
  | SDAP_Config__sdap_HeaderDL__absent => 1
  end.
Definition SDAP_Config__sdap_HeaderDL__F2 n :=
  match n with
  | 0 => SDAP_Config__sdap_HeaderDL__present
  | 1 => SDAP_Config__sdap_HeaderDL__absent
  | _ => SDAP_Config__sdap_HeaderDL__present
  end.
Lemma SDAP_Config__sdap_HeaderDL__F1F2 : forall x : SDAP_Config__sdap_HeaderDL__Type, (SDAP_Config__sdap_HeaderDL__F1 x <= 1) /\ SDAP_Config__sdap_HeaderDL__F2 (SDAP_Config__sdap_HeaderDL__F1 x) = x. imp_solve. Qed.
Lemma SDAP_Config__sdap_HeaderDL__F2F1 : forall (y : nat) (H : y <= 1), SDAP_Config__sdap_HeaderDL__F1 (SDAP_Config__sdap_HeaderDL__F2 y) = y. enum_solve H y. Qed.

Inductive SDAP_Config__sdap_HeaderUL__Type : Set :=
 | SDAP_Config__sdap_HeaderUL__present
 | SDAP_Config__sdap_HeaderUL__absent
.
Definition SDAP_Config__sdap_HeaderUL__cond := (fun (_ : SDAP_Config__sdap_HeaderUL__Type) => True).
Lemma SDAP_Config__sdap_HeaderUL__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDAP_Config__sdap_HeaderUL__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SDAP_Config__sdap_HeaderUL__nat__helper.

Definition SDAP_Config__sdap_HeaderUL__F1 t :=
  match t with
  | SDAP_Config__sdap_HeaderUL__present => 0
  | SDAP_Config__sdap_HeaderUL__absent => 1
  end.
Definition SDAP_Config__sdap_HeaderUL__F2 n :=
  match n with
  | 0 => SDAP_Config__sdap_HeaderUL__present
  | 1 => SDAP_Config__sdap_HeaderUL__absent
  | _ => SDAP_Config__sdap_HeaderUL__present
  end.
Lemma SDAP_Config__sdap_HeaderUL__F1F2 : forall x : SDAP_Config__sdap_HeaderUL__Type, (SDAP_Config__sdap_HeaderUL__F1 x <= 1) /\ SDAP_Config__sdap_HeaderUL__F2 (SDAP_Config__sdap_HeaderUL__F1 x) = x. imp_solve. Qed.
Lemma SDAP_Config__sdap_HeaderUL__F2F1 : forall (y : nat) (H : y <= 1), SDAP_Config__sdap_HeaderUL__F1 (SDAP_Config__sdap_HeaderUL__F2 y) = y. enum_solve H y. Qed.

Require Import NR.QFI.

Opaque QFI__cond QFI__Format.

Definition SDAP_Config__mappedQoS_FlowsToAdd__Type := list QFI__Type.

Lemma SDAP_Config__mappedQoS_FlowsToAdd__helper1 : (0 <= 1 <= maxNrofQFIs)%Z. unfold maxNrofQFIs.
 lia. Qed.
Lemma SDAP_Config__mappedQoS_FlowsToAdd__helper2 : to_bit_sz (Z.to_nat (maxNrofQFIs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofQFIs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SDAP_Config__mappedQoS_FlowsToAdd__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SDAP_Config__mappedQoS_FlowsToAdd__cond (z : SDAP_Config__mappedQoS_FlowsToAdd__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofQFIs)%Z /\ (list_and QFI__cond z) .

Require Import NR.QFI.

Opaque QFI__cond QFI__Format.

Definition SDAP_Config__mappedQoS_FlowsToRelease__Type := list QFI__Type.

Lemma SDAP_Config__mappedQoS_FlowsToRelease__helper1 : (0 <= 1 <= maxNrofQFIs)%Z. unfold maxNrofQFIs.
 lia. Qed.
Lemma SDAP_Config__mappedQoS_FlowsToRelease__helper2 : to_bit_sz (Z.to_nat (maxNrofQFIs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofQFIs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SDAP_Config__mappedQoS_FlowsToRelease__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SDAP_Config__mappedQoS_FlowsToRelease__cond (z : SDAP_Config__mappedQoS_FlowsToRelease__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofQFIs)%Z /\ (list_and QFI__cond z) .

Record SDAP_Config__Type : Set :=
  make__SDAP_Config__Type {
    SDAP_Config__pdu_Session : PDU_SessionID__Type ;
    SDAP_Config__sdap_HeaderDL : SDAP_Config__sdap_HeaderDL__Type ;
    SDAP_Config__sdap_HeaderUL : SDAP_Config__sdap_HeaderUL__Type ;
    SDAP_Config__defaultDRB : bool ;
    SDAP_Config__mappedQoS_FlowsToAdd : option SDAP_Config__mappedQoS_FlowsToAdd__Type ;
    SDAP_Config__mappedQoS_FlowsToRelease : option SDAP_Config__mappedQoS_FlowsToRelease__Type ;
}.
Definition SDAP_Config__root_list : list seq_elem := (
 Nor PDU_SessionID__Type PDU_SessionID__cond ::
 Nor SDAP_Config__sdap_HeaderDL__Type SDAP_Config__sdap_HeaderDL__cond ::
 Nor SDAP_Config__sdap_HeaderUL__Type SDAP_Config__sdap_HeaderUL__cond ::
 Nor bool (fun _ => True) ::
 Opt SDAP_Config__mappedQoS_FlowsToAdd__Type SDAP_Config__mappedQoS_FlowsToAdd__cond ::
 Opt SDAP_Config__mappedQoS_FlowsToRelease__Type SDAP_Config__mappedQoS_FlowsToRelease__cond ::
 nil).
Definition SDAP_Config__ext_list : list typ := (
  nil).
Definition SDAP_Config__cond (z : SDAP_Config__Type) := 
(  PDU_SessionID__cond (SDAP_Config__pdu_Session z) /\
  SDAP_Config__sdap_HeaderDL__cond (SDAP_Config__sdap_HeaderDL z) /\
  SDAP_Config__sdap_HeaderUL__cond (SDAP_Config__sdap_HeaderUL z) /\
  (fun _ => True) (SDAP_Config__defaultDRB z) /\
  opt_cond SDAP_Config__mappedQoS_FlowsToAdd__cond (SDAP_Config__mappedQoS_FlowsToAdd z) /\
  opt_cond SDAP_Config__mappedQoS_FlowsToRelease__cond (SDAP_Config__mappedQoS_FlowsToRelease z) /\
  True) /\ 
(  True).


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
Definition SDAP_Config__sdap_HeaderDL__Format : T_Format SDAP_Config__sdap_HeaderDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDAP_Config__sdap_HeaderDL__nat__Format SDAP_Config__sdap_HeaderDL__F1 SDAP_Config__sdap_HeaderDL__F2 SDAP_Config__sdap_HeaderDL__F1F2 SDAP_Config__sdap_HeaderDL__F2F1.

Opaque SDAP_Config__sdap_HeaderDL__cond SDAP_Config__sdap_HeaderDL__Format.

Definition SDAP_Config__sdap_HeaderUL__Format : T_Format SDAP_Config__sdap_HeaderUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDAP_Config__sdap_HeaderUL__nat__Format SDAP_Config__sdap_HeaderUL__F1 SDAP_Config__sdap_HeaderUL__F2 SDAP_Config__sdap_HeaderUL__F1F2 SDAP_Config__sdap_HeaderUL__F2F1.

Opaque SDAP_Config__sdap_HeaderUL__cond SDAP_Config__sdap_HeaderUL__Format.

Definition SDAP_Config__mappedQoS_FlowsToAdd__Format : T_Format SDAP_Config__mappedQoS_FlowsToAdd__Type SDAP_Config__mappedQoS_FlowsToAdd__cond := seq_of_format QFI__Format 1 maxNrofQFIs SDAP_Config__mappedQoS_FlowsToAdd__helper1 SDAP_Config__mappedQoS_FlowsToAdd__helper2.

Opaque SDAP_Config__mappedQoS_FlowsToAdd__cond SDAP_Config__mappedQoS_FlowsToAdd__Format.

Definition SDAP_Config__mappedQoS_FlowsToRelease__Format : T_Format SDAP_Config__mappedQoS_FlowsToRelease__Type SDAP_Config__mappedQoS_FlowsToRelease__cond := seq_of_format QFI__Format 1 maxNrofQFIs SDAP_Config__mappedQoS_FlowsToRelease__helper1 SDAP_Config__mappedQoS_FlowsToRelease__helper2.

Opaque SDAP_Config__mappedQoS_FlowsToRelease__cond SDAP_Config__mappedQoS_FlowsToRelease__Format.


Definition SDAP_Config__root_Format_Type := Eval cbn in seq_format_prod SDAP_Config__root_list.
Definition SDAP_Config__root_Format_list : SDAP_Config__root_Format_Type :=
  (PDU_SessionID__Format, (SDAP_Config__sdap_HeaderDL__Format, (SDAP_Config__sdap_HeaderUL__Format, (bool__Format, (SDAP_Config__mappedQoS_FlowsToAdd__Format, (SDAP_Config__mappedQoS_FlowsToRelease__Format, unit_format)))))).

Definition SDAP_Config__ext_Format_Type := Eval cbn in get_formats SDAP_Config__ext_list.
Definition SDAP_Config__ext_Format_list : SDAP_Config__ext_Format_Type :=
  unit__Format.

Definition SDAP_Config__list_type : Set := (seq_type SDAP_Config__root_list) * (seq_ext_type SDAP_Config__ext_list).
Definition SDAP_Config__list_cond (z : SDAP_Config__list_type) : Prop :=
        (seq_cond SDAP_Config__root_list (fst z)) /\ (seq_ext_cond SDAP_Config__ext_list (snd z)).
Definition SDAP_Config__list_format : T_Format SDAP_Config__list_type SDAP_Config__list_cond :=
 (* Eval compute in *) seq_ext_format SDAP_Config__root_list SDAP_Config__root_Format_list SDAP_Config__ext_list SDAP_Config__ext_Format_list.

Opaque SDAP_Config__list_format.
Definition SDAP_Config__F1 (z : SDAP_Config__Type) : SDAP_Config__list_type :=
  (((SDAP_Config__pdu_Session z, (SDAP_Config__sdap_HeaderDL z, (SDAP_Config__sdap_HeaderUL z, (SDAP_Config__defaultDRB z, (SDAP_Config__mappedQoS_FlowsToAdd z, (SDAP_Config__mappedQoS_FlowsToRelease z, tt))))))), (
tt)).
Definition SDAP_Config__F2 (y : SDAP_Config__list_type) : SDAP_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SDAP_Config__Type j0 j1 j2 j3 j4 j5
  end.
Definition SDAP_Config__helper1 : (forall a : SDAP_Config__Type, SDAP_Config__cond a -> SDAP_Config__list_cond (SDAP_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SDAP_Config__helper2 : (forall a : SDAP_Config__Type, SDAP_Config__F2 (SDAP_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SDAP_Config__helper3 : (forall b : SDAP_Config__list_type, SDAP_Config__list_cond b -> SDAP_Config__cond (SDAP_Config__F2 b) /\ SDAP_Config__F1 (SDAP_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SDAP_Config__cond, SDAP_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SDAP_Config__Format : T_Format SDAP_Config__Type SDAP_Config__cond :=
 proj2_format SDAP_Config__cond SDAP_Config__list_format  SDAP_Config__F1 SDAP_Config__F2 SDAP_Config__helper1 SDAP_Config__helper2 SDAP_Config__helper3.

Opaque SDAP_Config__cond SDAP_Config__Format.

