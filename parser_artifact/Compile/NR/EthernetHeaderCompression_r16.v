Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Type : Set :=
 | EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits7
 | EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits15
.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__cond := (fun (_ : EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Type) => True).
Lemma EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__nat__helper.

Definition EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1 t :=
  match t with
  | EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits7 => 0
  | EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits15 => 1
  end.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F2 n :=
  match n with
  | 0 => EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits7
  | 1 => EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits15
  | _ => EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__bits7
  end.
Lemma EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1F2 : forall x : EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Type, (EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1 x <= 1) /\ EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F2 (EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1 x) = x. imp_solve. Qed.
Lemma EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F2F1 : forall (y : nat) (H : y <= 1), EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1 (EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F2 y) = y. enum_solve H y. Qed.

Record EthernetHeaderCompression_r16__ehc_Common_r16__Type : Set :=
  make__EthernetHeaderCompression_r16__ehc_Common_r16__Type {
    EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16 : EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Type ;
}.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__root_list : list seq_elem := (
 Nor EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Type EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__cond ::
 nil).
Definition EthernetHeaderCompression_r16__ehc_Common_r16__ext_list : list typ := (
  nil).
Definition EthernetHeaderCompression_r16__ehc_Common_r16__cond (z : EthernetHeaderCompression_r16__ehc_Common_r16__Type) := 
(  EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__cond (EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16 z) /\
  True) /\ 
(  True).

Inductive EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Type : Set :=
 | EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__true
.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__cond := (fun (_ : EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Type) => True).
Lemma EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__nat__helper.

Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1 t :=
  match t with
  | EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__true => 0
  end.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F2 n :=
  match n with
  | 0 => EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__true
  | _ => EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__true
  end.
Lemma EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1F2 : forall x : EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Type, (EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1 x <= 0) /\ EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F2 (EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1 x) = x. imp_solve. Qed.
Lemma EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F2F1 : forall (y : nat) (H : y <= 0), EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1 (EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F2 y) = y. enum_solve H y. Qed.

Record EthernetHeaderCompression_r16__ehc_Downlink_r16__Type : Set :=
  make__EthernetHeaderCompression_r16__ehc_Downlink_r16__Type {
    EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16 : option EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Type ;
}.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__root_list : list seq_elem := (
 Opt EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Type EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__cond ::
 nil).
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_list : list typ := (
  nil).
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__cond (z : EthernetHeaderCompression_r16__ehc_Downlink_r16__Type) := 
(  opt_cond EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__cond (EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16 z) /\
  True) /\ 
(  True).

Lemma EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__helper1 : (1 <= 32767)%Z.  lia. Qed.
Lemma EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__helper2 : to_bit_sz (Z.to_nat (32767 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32767 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__Type := Z.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__cond := (fun z => (1 <= z <= 32767)%Z).
Inductive EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Type : Set :=
 | EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__true
.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__cond := (fun (_ : EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Type) => True).
Lemma EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__nat__helper.

Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1 t :=
  match t with
  | EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__true => 0
  end.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F2 n :=
  match n with
  | 0 => EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__true
  | _ => EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__true
  end.
Lemma EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1F2 : forall x : EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Type, (EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1 x <= 0) /\ EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F2 (EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1 x) = x. imp_solve. Qed.
Lemma EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F2F1 : forall (y : nat) (H : y <= 0), EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1 (EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F2 y) = y. enum_solve H y. Qed.

Record EthernetHeaderCompression_r16__ehc_Uplink_r16__Type : Set :=
  make__EthernetHeaderCompression_r16__ehc_Uplink_r16__Type {
    EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16 : Z ;
    EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16 : option EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Type ;
}.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__root_list : list seq_elem := (
 Nor Z EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__cond ::
 Opt EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Type EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__cond ::
 nil).
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_list : list typ := (
  nil).
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__cond (z : EthernetHeaderCompression_r16__ehc_Uplink_r16__Type) := 
(  EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__cond (EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16 z) /\
  opt_cond EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__cond (EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16 z) /\
  True) /\ 
(  True).

Record EthernetHeaderCompression_r16__Type : Set :=
  make__EthernetHeaderCompression_r16__Type {
    EthernetHeaderCompression_r16__ehc_Common_r16 : EthernetHeaderCompression_r16__ehc_Common_r16__Type ;
    EthernetHeaderCompression_r16__ehc_Downlink_r16 : option EthernetHeaderCompression_r16__ehc_Downlink_r16__Type ;
    EthernetHeaderCompression_r16__ehc_Uplink_r16 : option EthernetHeaderCompression_r16__ehc_Uplink_r16__Type ;
}.
Definition EthernetHeaderCompression_r16__list := (
 Nor EthernetHeaderCompression_r16__ehc_Common_r16__Type EthernetHeaderCompression_r16__ehc_Common_r16__cond ::
 Opt EthernetHeaderCompression_r16__ehc_Downlink_r16__Type EthernetHeaderCompression_r16__ehc_Downlink_r16__cond ::
 Opt EthernetHeaderCompression_r16__ehc_Uplink_r16__Type EthernetHeaderCompression_r16__ehc_Uplink_r16__cond ::
 nil).
Definition EthernetHeaderCompression_r16__cond z := 
  EthernetHeaderCompression_r16__ehc_Common_r16__cond (EthernetHeaderCompression_r16__ehc_Common_r16 z) /\
  opt_cond EthernetHeaderCompression_r16__ehc_Downlink_r16__cond (EthernetHeaderCompression_r16__ehc_Downlink_r16 z) /\
  opt_cond EthernetHeaderCompression_r16__ehc_Uplink_r16__cond (EthernetHeaderCompression_r16__ehc_Uplink_r16 z) /\
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
Definition EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Format : T_Format EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__nat__Format EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1 EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F2 EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F1F2 EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__F2F1.

Opaque EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__cond EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Format.


Definition EthernetHeaderCompression_r16__ehc_Common_r16__root_Format_Type := Eval cbn in seq_format_prod EthernetHeaderCompression_r16__ehc_Common_r16__root_list.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__root_Format_list : EthernetHeaderCompression_r16__ehc_Common_r16__root_Format_Type :=
  (EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16__Format, unit_format).

Definition EthernetHeaderCompression_r16__ehc_Common_r16__ext_Format_Type := Eval cbn in get_formats EthernetHeaderCompression_r16__ehc_Common_r16__ext_list.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__ext_Format_list : EthernetHeaderCompression_r16__ehc_Common_r16__ext_Format_Type :=
  unit__Format.

Definition EthernetHeaderCompression_r16__ehc_Common_r16__list_type : Set := (seq_type EthernetHeaderCompression_r16__ehc_Common_r16__root_list) * (seq_ext_type EthernetHeaderCompression_r16__ehc_Common_r16__ext_list).
Definition EthernetHeaderCompression_r16__ehc_Common_r16__list_cond (z : EthernetHeaderCompression_r16__ehc_Common_r16__list_type) : Prop :=
        (seq_cond EthernetHeaderCompression_r16__ehc_Common_r16__root_list (fst z)) /\ (seq_ext_cond EthernetHeaderCompression_r16__ehc_Common_r16__ext_list (snd z)).
Definition EthernetHeaderCompression_r16__ehc_Common_r16__list_format : T_Format EthernetHeaderCompression_r16__ehc_Common_r16__list_type EthernetHeaderCompression_r16__ehc_Common_r16__list_cond :=
 (* Eval compute in *) seq_ext_format EthernetHeaderCompression_r16__ehc_Common_r16__root_list EthernetHeaderCompression_r16__ehc_Common_r16__root_Format_list EthernetHeaderCompression_r16__ehc_Common_r16__ext_list EthernetHeaderCompression_r16__ehc_Common_r16__ext_Format_list.

Opaque EthernetHeaderCompression_r16__ehc_Common_r16__list_format.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__F1 (z : EthernetHeaderCompression_r16__ehc_Common_r16__Type) : EthernetHeaderCompression_r16__ehc_Common_r16__list_type :=
  (((EthernetHeaderCompression_r16__ehc_Common_r16__ehc_CID_Length_r16 z, tt)), (
tt)).
Definition EthernetHeaderCompression_r16__ehc_Common_r16__F2 (y : EthernetHeaderCompression_r16__ehc_Common_r16__list_type) : EthernetHeaderCompression_r16__ehc_Common_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__EthernetHeaderCompression_r16__ehc_Common_r16__Type j0
  end.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__helper1 : (forall a : EthernetHeaderCompression_r16__ehc_Common_r16__Type, EthernetHeaderCompression_r16__ehc_Common_r16__cond a -> EthernetHeaderCompression_r16__ehc_Common_r16__list_cond (EthernetHeaderCompression_r16__ehc_Common_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__helper2 : (forall a : EthernetHeaderCompression_r16__ehc_Common_r16__Type, EthernetHeaderCompression_r16__ehc_Common_r16__F2 (EthernetHeaderCompression_r16__ehc_Common_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__helper3 : (forall b : EthernetHeaderCompression_r16__ehc_Common_r16__list_type, EthernetHeaderCompression_r16__ehc_Common_r16__list_cond b -> EthernetHeaderCompression_r16__ehc_Common_r16__cond (EthernetHeaderCompression_r16__ehc_Common_r16__F2 b) /\ EthernetHeaderCompression_r16__ehc_Common_r16__F1 (EthernetHeaderCompression_r16__ehc_Common_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EthernetHeaderCompression_r16__ehc_Common_r16__cond, EthernetHeaderCompression_r16__ehc_Common_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EthernetHeaderCompression_r16__ehc_Common_r16__Format : T_Format EthernetHeaderCompression_r16__ehc_Common_r16__Type EthernetHeaderCompression_r16__ehc_Common_r16__cond :=
 proj2_format EthernetHeaderCompression_r16__ehc_Common_r16__cond EthernetHeaderCompression_r16__ehc_Common_r16__list_format  EthernetHeaderCompression_r16__ehc_Common_r16__F1 EthernetHeaderCompression_r16__ehc_Common_r16__F2 EthernetHeaderCompression_r16__ehc_Common_r16__helper1 EthernetHeaderCompression_r16__ehc_Common_r16__helper2 EthernetHeaderCompression_r16__ehc_Common_r16__helper3.

Opaque EthernetHeaderCompression_r16__ehc_Common_r16__cond EthernetHeaderCompression_r16__ehc_Common_r16__Format.

Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Format : T_Format EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__nat__Format EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1 EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F2 EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F1F2 EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__F2F1.

Opaque EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__cond EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Format.


Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__root_Format_Type := Eval cbn in seq_format_prod EthernetHeaderCompression_r16__ehc_Downlink_r16__root_list.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__root_Format_list : EthernetHeaderCompression_r16__ehc_Downlink_r16__root_Format_Type :=
  (EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16__Format, unit_format).

Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_Format_Type := Eval cbn in get_formats EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_list.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_Format_list : EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_Format_Type :=
  unit__Format.

Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__list_type : Set := (seq_type EthernetHeaderCompression_r16__ehc_Downlink_r16__root_list) * (seq_ext_type EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_list).
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__list_cond (z : EthernetHeaderCompression_r16__ehc_Downlink_r16__list_type) : Prop :=
        (seq_cond EthernetHeaderCompression_r16__ehc_Downlink_r16__root_list (fst z)) /\ (seq_ext_cond EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_list (snd z)).
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__list_format : T_Format EthernetHeaderCompression_r16__ehc_Downlink_r16__list_type EthernetHeaderCompression_r16__ehc_Downlink_r16__list_cond :=
 (* Eval compute in *) seq_ext_format EthernetHeaderCompression_r16__ehc_Downlink_r16__root_list EthernetHeaderCompression_r16__ehc_Downlink_r16__root_Format_list EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_list EthernetHeaderCompression_r16__ehc_Downlink_r16__ext_Format_list.

Opaque EthernetHeaderCompression_r16__ehc_Downlink_r16__list_format.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__F1 (z : EthernetHeaderCompression_r16__ehc_Downlink_r16__Type) : EthernetHeaderCompression_r16__ehc_Downlink_r16__list_type :=
  (((EthernetHeaderCompression_r16__ehc_Downlink_r16__drb_ContinueEHC_DL_r16 z, tt)), (
tt)).
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__F2 (y : EthernetHeaderCompression_r16__ehc_Downlink_r16__list_type) : EthernetHeaderCompression_r16__ehc_Downlink_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__EthernetHeaderCompression_r16__ehc_Downlink_r16__Type j0
  end.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__helper1 : (forall a : EthernetHeaderCompression_r16__ehc_Downlink_r16__Type, EthernetHeaderCompression_r16__ehc_Downlink_r16__cond a -> EthernetHeaderCompression_r16__ehc_Downlink_r16__list_cond (EthernetHeaderCompression_r16__ehc_Downlink_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__helper2 : (forall a : EthernetHeaderCompression_r16__ehc_Downlink_r16__Type, EthernetHeaderCompression_r16__ehc_Downlink_r16__F2 (EthernetHeaderCompression_r16__ehc_Downlink_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__helper3 : (forall b : EthernetHeaderCompression_r16__ehc_Downlink_r16__list_type, EthernetHeaderCompression_r16__ehc_Downlink_r16__list_cond b -> EthernetHeaderCompression_r16__ehc_Downlink_r16__cond (EthernetHeaderCompression_r16__ehc_Downlink_r16__F2 b) /\ EthernetHeaderCompression_r16__ehc_Downlink_r16__F1 (EthernetHeaderCompression_r16__ehc_Downlink_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EthernetHeaderCompression_r16__ehc_Downlink_r16__cond, EthernetHeaderCompression_r16__ehc_Downlink_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EthernetHeaderCompression_r16__ehc_Downlink_r16__Format : T_Format EthernetHeaderCompression_r16__ehc_Downlink_r16__Type EthernetHeaderCompression_r16__ehc_Downlink_r16__cond :=
 proj2_format EthernetHeaderCompression_r16__ehc_Downlink_r16__cond EthernetHeaderCompression_r16__ehc_Downlink_r16__list_format  EthernetHeaderCompression_r16__ehc_Downlink_r16__F1 EthernetHeaderCompression_r16__ehc_Downlink_r16__F2 EthernetHeaderCompression_r16__ehc_Downlink_r16__helper1 EthernetHeaderCompression_r16__ehc_Downlink_r16__helper2 EthernetHeaderCompression_r16__ehc_Downlink_r16__helper3.

Opaque EthernetHeaderCompression_r16__ehc_Downlink_r16__cond EthernetHeaderCompression_r16__ehc_Downlink_r16__Format.

Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__Format : T_Format Z EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__cond :=
 ranged_int_format (1) (32767) EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__helper1 EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__helper2.

Opaque EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__cond EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__Format.

Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Format : T_Format EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__nat__Format EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1 EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F2 EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F1F2 EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__F2F1.

Opaque EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__cond EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Format.


Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__root_Format_Type := Eval cbn in seq_format_prod EthernetHeaderCompression_r16__ehc_Uplink_r16__root_list.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__root_Format_list : EthernetHeaderCompression_r16__ehc_Uplink_r16__root_Format_Type :=
  (EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16__Format, (EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16__Format, unit_format)).

Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_Format_Type := Eval cbn in get_formats EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_list.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_Format_list : EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_Format_Type :=
  unit__Format.

Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__list_type : Set := (seq_type EthernetHeaderCompression_r16__ehc_Uplink_r16__root_list) * (seq_ext_type EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_list).
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__list_cond (z : EthernetHeaderCompression_r16__ehc_Uplink_r16__list_type) : Prop :=
        (seq_cond EthernetHeaderCompression_r16__ehc_Uplink_r16__root_list (fst z)) /\ (seq_ext_cond EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_list (snd z)).
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__list_format : T_Format EthernetHeaderCompression_r16__ehc_Uplink_r16__list_type EthernetHeaderCompression_r16__ehc_Uplink_r16__list_cond :=
 (* Eval compute in *) seq_ext_format EthernetHeaderCompression_r16__ehc_Uplink_r16__root_list EthernetHeaderCompression_r16__ehc_Uplink_r16__root_Format_list EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_list EthernetHeaderCompression_r16__ehc_Uplink_r16__ext_Format_list.

Opaque EthernetHeaderCompression_r16__ehc_Uplink_r16__list_format.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__F1 (z : EthernetHeaderCompression_r16__ehc_Uplink_r16__Type) : EthernetHeaderCompression_r16__ehc_Uplink_r16__list_type :=
  (((EthernetHeaderCompression_r16__ehc_Uplink_r16__maxCID_EHC_UL_r16 z, (EthernetHeaderCompression_r16__ehc_Uplink_r16__drb_ContinueEHC_UL_r16 z, tt))), (
tt)).
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__F2 (y : EthernetHeaderCompression_r16__ehc_Uplink_r16__list_type) : EthernetHeaderCompression_r16__ehc_Uplink_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__EthernetHeaderCompression_r16__ehc_Uplink_r16__Type j0 j1
  end.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__helper1 : (forall a : EthernetHeaderCompression_r16__ehc_Uplink_r16__Type, EthernetHeaderCompression_r16__ehc_Uplink_r16__cond a -> EthernetHeaderCompression_r16__ehc_Uplink_r16__list_cond (EthernetHeaderCompression_r16__ehc_Uplink_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__helper2 : (forall a : EthernetHeaderCompression_r16__ehc_Uplink_r16__Type, EthernetHeaderCompression_r16__ehc_Uplink_r16__F2 (EthernetHeaderCompression_r16__ehc_Uplink_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__helper3 : (forall b : EthernetHeaderCompression_r16__ehc_Uplink_r16__list_type, EthernetHeaderCompression_r16__ehc_Uplink_r16__list_cond b -> EthernetHeaderCompression_r16__ehc_Uplink_r16__cond (EthernetHeaderCompression_r16__ehc_Uplink_r16__F2 b) /\ EthernetHeaderCompression_r16__ehc_Uplink_r16__F1 (EthernetHeaderCompression_r16__ehc_Uplink_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EthernetHeaderCompression_r16__ehc_Uplink_r16__cond, EthernetHeaderCompression_r16__ehc_Uplink_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EthernetHeaderCompression_r16__ehc_Uplink_r16__Format : T_Format EthernetHeaderCompression_r16__ehc_Uplink_r16__Type EthernetHeaderCompression_r16__ehc_Uplink_r16__cond :=
 proj2_format EthernetHeaderCompression_r16__ehc_Uplink_r16__cond EthernetHeaderCompression_r16__ehc_Uplink_r16__list_format  EthernetHeaderCompression_r16__ehc_Uplink_r16__F1 EthernetHeaderCompression_r16__ehc_Uplink_r16__F2 EthernetHeaderCompression_r16__ehc_Uplink_r16__helper1 EthernetHeaderCompression_r16__ehc_Uplink_r16__helper2 EthernetHeaderCompression_r16__ehc_Uplink_r16__helper3.

Opaque EthernetHeaderCompression_r16__ehc_Uplink_r16__cond EthernetHeaderCompression_r16__ehc_Uplink_r16__Format.


Definition EthernetHeaderCompression_r16__Format_Type := Eval cbn in seq_format_prod EthernetHeaderCompression_r16__list.
Definition EthernetHeaderCompression_r16__Format_list : EthernetHeaderCompression_r16__Format_Type :=
  (EthernetHeaderCompression_r16__ehc_Common_r16__Format, (EthernetHeaderCompression_r16__ehc_Downlink_r16__Format, (EthernetHeaderCompression_r16__ehc_Uplink_r16__Format, unit_format))).
Definition EthernetHeaderCompression_r16__list__Format := (*Eval compute in *) seq_format EthernetHeaderCompression_r16__list EthernetHeaderCompression_r16__Format_list.
Definition EthernetHeaderCompression_r16__F1 z :=
  (EthernetHeaderCompression_r16__ehc_Common_r16 z, (EthernetHeaderCompression_r16__ehc_Downlink_r16 z, (EthernetHeaderCompression_r16__ehc_Uplink_r16 z, tt))).
Definition EthernetHeaderCompression_r16__F2 (y : seq_type EthernetHeaderCompression_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__EthernetHeaderCompression_r16__Type i0 i1 i2
  end.
Lemma EthernetHeaderCompression_r16__F1F2_cond (z : EthernetHeaderCompression_r16__Type)
  : EthernetHeaderCompression_r16__cond z ->
  (seq_cond EthernetHeaderCompression_r16__list (EthernetHeaderCompression_r16__F1 z)).
intro H. unfold EthernetHeaderCompression_r16__cond in H. simpl. auto. Qed.
Lemma EthernetHeaderCompression_r16__F1F2_cond2 (z : EthernetHeaderCompression_r16__Type)
 : EthernetHeaderCompression_r16__F2 (EthernetHeaderCompression_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EthernetHeaderCompression_r16__F2F1_cond (y : seq_type EthernetHeaderCompression_r16__list)
  : seq_cond EthernetHeaderCompression_r16__list y ->
 (EthernetHeaderCompression_r16__cond (EthernetHeaderCompression_r16__F2 y)) /\  EthernetHeaderCompression_r16__F1 (EthernetHeaderCompression_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EthernetHeaderCompression_r16__cond. simpl in *. auto.
 - simpl. unfold EthernetHeaderCompression_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EthernetHeaderCompression_r16__Format : T_Format EthernetHeaderCompression_r16__Type EthernetHeaderCompression_r16__cond :=
        proj2_format  EthernetHeaderCompression_r16__cond EthernetHeaderCompression_r16__list__Format
    EthernetHeaderCompression_r16__F1 EthernetHeaderCompression_r16__F2 EthernetHeaderCompression_r16__F1F2_cond  EthernetHeaderCompression_r16__F1F2_cond2 EthernetHeaderCompression_r16__F2F1_cond.
Opaque EthernetHeaderCompression_r16__cond EthernetHeaderCompression_r16__Format.

