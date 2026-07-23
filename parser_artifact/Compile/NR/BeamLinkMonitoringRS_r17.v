Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BeamLinkMonitoringRS_Id_r17.

Opaque BeamLinkMonitoringRS_Id_r17__cond BeamLinkMonitoringRS_Id_r17__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.


Inductive BeamLinkMonitoringRS_r17__detectionResource_r17__Type : Set :=
  | BeamLinkMonitoringRS_r17__detectionResource_r17__ssb_Index : SSB_Index__Type -> BeamLinkMonitoringRS_r17__detectionResource_r17__Type
  | BeamLinkMonitoringRS_r17__detectionResource_r17__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> BeamLinkMonitoringRS_r17__detectionResource_r17__Type
.
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__cond (c : BeamLinkMonitoringRS_r17__detectionResource_r17__Type) := 
  match c with
  | BeamLinkMonitoringRS_r17__detectionResource_r17__ssb_Index t => SSB_Index__cond t 
  | BeamLinkMonitoringRS_r17__detectionResource_r17__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  end.

Lemma BeamLinkMonitoringRS_r17__detectionResource_r17__len_helper1 : to_bit_sz (length BeamLinkMonitoringRS_r17__detectionResource_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BeamLinkMonitoringRS_r17__detectionResource_r17__len_helper2 : 2 <= length2 BeamLinkMonitoringRS_r17__detectionResource_r17__list.
 simpl. lia. Qed.
Record BeamLinkMonitoringRS_r17__Type : Set :=
  make__BeamLinkMonitoringRS_r17__Type {
    BeamLinkMonitoringRS_r17__beamLinkMonitoringRS_Id_r17 : BeamLinkMonitoringRS_Id_r17__Type ;
    BeamLinkMonitoringRS_r17__detectionResource_r17 : BeamLinkMonitoringRS_r17__detectionResource_r17__Type ;
}.
Definition BeamLinkMonitoringRS_r17__root_list : list seq_elem := (
 Nor BeamLinkMonitoringRS_Id_r17__Type BeamLinkMonitoringRS_Id_r17__cond ::
 Nor BeamLinkMonitoringRS_r17__detectionResource_r17__Type BeamLinkMonitoringRS_r17__detectionResource_r17__cond ::
 nil).
Definition BeamLinkMonitoringRS_r17__ext_list : list typ := (
  nil).
Definition BeamLinkMonitoringRS_r17__cond (z : BeamLinkMonitoringRS_r17__Type) := 
(  BeamLinkMonitoringRS_Id_r17__cond (BeamLinkMonitoringRS_r17__beamLinkMonitoringRS_Id_r17 z) /\
  BeamLinkMonitoringRS_r17__detectionResource_r17__cond (BeamLinkMonitoringRS_r17__detectionResource_r17 z) /\
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

Definition BeamLinkMonitoringRS_r17__detectionResource_r17__Format_Type := Eval cbn in get_formats BeamLinkMonitoringRS_r17__detectionResource_r17__list.
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__Format_list : BeamLinkMonitoringRS_r17__detectionResource_r17__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, unit__Format)).
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__list__Format := Eval compute in choice_format BeamLinkMonitoringRS_r17__detectionResource_r17__list BeamLinkMonitoringRS_r17__detectionResource_r17__len_helper1 BeamLinkMonitoringRS_r17__detectionResource_r17__len_helper2  BeamLinkMonitoringRS_r17__detectionResource_r17__Format_list.
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__F1 (z : BeamLinkMonitoringRS_r17__detectionResource_r17__Type) : (choice BeamLinkMonitoringRS_r17__detectionResource_r17__list) :=
  match z with
   | BeamLinkMonitoringRS_r17__detectionResource_r17__ssb_Index t => existT _ 0 t
  | BeamLinkMonitoringRS_r17__detectionResource_r17__csi_RS_Index t => existT _ 1 t
  end.
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__g := (fun n => typ_set (get_nth_typ BeamLinkMonitoringRS_r17__detectionResource_r17__list n)).
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__F2 (y : choice BeamLinkMonitoringRS_r17__detectionResource_r17__list) : BeamLinkMonitoringRS_r17__detectionResource_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BeamLinkMonitoringRS_r17__detectionResource_r17__g n -> BeamLinkMonitoringRS_r17__detectionResource_r17__Type) with
    | 0 => fun (t : SSB_Index__Type) => BeamLinkMonitoringRS_r17__detectionResource_r17__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => BeamLinkMonitoringRS_r17__detectionResource_r17__csi_RS_Index t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BeamLinkMonitoringRS_r17__detectionResource_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BeamLinkMonitoringRS_r17__detectionResource_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BeamLinkMonitoringRS_r17__detectionResource_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BeamLinkMonitoringRS_r17__detectionResource_r17__Type with end) n0
           end t0).

Lemma BeamLinkMonitoringRS_r17__detectionResource_r17__helper2 :  forall (y : BeamLinkMonitoringRS_r17__detectionResource_r17__Type), BeamLinkMonitoringRS_r17__detectionResource_r17__cond y -> choice_cond BeamLinkMonitoringRS_r17__detectionResource_r17__list (BeamLinkMonitoringRS_r17__detectionResource_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BeamLinkMonitoringRS_r17__detectionResource_r17__helper3 :  forall (y : BeamLinkMonitoringRS_r17__detectionResource_r17__Type), BeamLinkMonitoringRS_r17__detectionResource_r17__F2 (BeamLinkMonitoringRS_r17__detectionResource_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BeamLinkMonitoringRS_r17__detectionResource_r17__helper4 : (forall b : choice BeamLinkMonitoringRS_r17__detectionResource_r17__list, choice_cond BeamLinkMonitoringRS_r17__detectionResource_r17__list b -> BeamLinkMonitoringRS_r17__detectionResource_r17__cond (BeamLinkMonitoringRS_r17__detectionResource_r17__F2 b) /\ BeamLinkMonitoringRS_r17__detectionResource_r17__F1 (BeamLinkMonitoringRS_r17__detectionResource_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BeamLinkMonitoringRS_r17__detectionResource_r17__F1 BeamLinkMonitoringRS_r17__detectionResource_r17__F2.
Definition BeamLinkMonitoringRS_r17__detectionResource_r17__Format : T_Format BeamLinkMonitoringRS_r17__detectionResource_r17__Type BeamLinkMonitoringRS_r17__detectionResource_r17__cond :=
  (* Eval compute in *) proj2_format BeamLinkMonitoringRS_r17__detectionResource_r17__cond BeamLinkMonitoringRS_r17__detectionResource_r17__list__Format BeamLinkMonitoringRS_r17__detectionResource_r17__F1 BeamLinkMonitoringRS_r17__detectionResource_r17__F2 BeamLinkMonitoringRS_r17__detectionResource_r17__helper2 BeamLinkMonitoringRS_r17__detectionResource_r17__helper3 BeamLinkMonitoringRS_r17__detectionResource_r17__helper4.
Opaque BeamLinkMonitoringRS_r17__detectionResource_r17__cond BeamLinkMonitoringRS_r17__detectionResource_r17__Format.


Definition BeamLinkMonitoringRS_r17__root_Format_Type := Eval cbn in seq_format_prod BeamLinkMonitoringRS_r17__root_list.
Definition BeamLinkMonitoringRS_r17__root_Format_list : BeamLinkMonitoringRS_r17__root_Format_Type :=
  (BeamLinkMonitoringRS_Id_r17__Format, (BeamLinkMonitoringRS_r17__detectionResource_r17__Format, unit_format)).

Definition BeamLinkMonitoringRS_r17__ext_Format_Type := Eval cbn in get_formats BeamLinkMonitoringRS_r17__ext_list.
Definition BeamLinkMonitoringRS_r17__ext_Format_list : BeamLinkMonitoringRS_r17__ext_Format_Type :=
  unit__Format.

Definition BeamLinkMonitoringRS_r17__list_type : Set := (seq_type BeamLinkMonitoringRS_r17__root_list) * (seq_ext_type BeamLinkMonitoringRS_r17__ext_list).
Definition BeamLinkMonitoringRS_r17__list_cond (z : BeamLinkMonitoringRS_r17__list_type) : Prop :=
        (seq_cond BeamLinkMonitoringRS_r17__root_list (fst z)) /\ (seq_ext_cond BeamLinkMonitoringRS_r17__ext_list (snd z)).
Definition BeamLinkMonitoringRS_r17__list_format : T_Format BeamLinkMonitoringRS_r17__list_type BeamLinkMonitoringRS_r17__list_cond :=
 (* Eval compute in *) seq_ext_format BeamLinkMonitoringRS_r17__root_list BeamLinkMonitoringRS_r17__root_Format_list BeamLinkMonitoringRS_r17__ext_list BeamLinkMonitoringRS_r17__ext_Format_list.

Opaque BeamLinkMonitoringRS_r17__list_format.
Definition BeamLinkMonitoringRS_r17__F1 (z : BeamLinkMonitoringRS_r17__Type) : BeamLinkMonitoringRS_r17__list_type :=
  (((BeamLinkMonitoringRS_r17__beamLinkMonitoringRS_Id_r17 z, (BeamLinkMonitoringRS_r17__detectionResource_r17 z, tt))), (
tt)).
Definition BeamLinkMonitoringRS_r17__F2 (y : BeamLinkMonitoringRS_r17__list_type) : BeamLinkMonitoringRS_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__BeamLinkMonitoringRS_r17__Type j0 j1
  end.
Definition BeamLinkMonitoringRS_r17__helper1 : (forall a : BeamLinkMonitoringRS_r17__Type, BeamLinkMonitoringRS_r17__cond a -> BeamLinkMonitoringRS_r17__list_cond (BeamLinkMonitoringRS_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BeamLinkMonitoringRS_r17__helper2 : (forall a : BeamLinkMonitoringRS_r17__Type, BeamLinkMonitoringRS_r17__F2 (BeamLinkMonitoringRS_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BeamLinkMonitoringRS_r17__helper3 : (forall b : BeamLinkMonitoringRS_r17__list_type, BeamLinkMonitoringRS_r17__list_cond b -> BeamLinkMonitoringRS_r17__cond (BeamLinkMonitoringRS_r17__F2 b) /\ BeamLinkMonitoringRS_r17__F1 (BeamLinkMonitoringRS_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BeamLinkMonitoringRS_r17__cond, BeamLinkMonitoringRS_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BeamLinkMonitoringRS_r17__Format : T_Format BeamLinkMonitoringRS_r17__Type BeamLinkMonitoringRS_r17__cond :=
 proj2_format BeamLinkMonitoringRS_r17__cond BeamLinkMonitoringRS_r17__list_format  BeamLinkMonitoringRS_r17__F1 BeamLinkMonitoringRS_r17__F2 BeamLinkMonitoringRS_r17__helper1 BeamLinkMonitoringRS_r17__helper2 BeamLinkMonitoringRS_r17__helper3.

Opaque BeamLinkMonitoringRS_r17__cond BeamLinkMonitoringRS_r17__Format.

