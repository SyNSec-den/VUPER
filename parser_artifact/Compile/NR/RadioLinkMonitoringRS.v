Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RadioLinkMonitoringRS_Id.

Opaque RadioLinkMonitoringRS_Id__cond RadioLinkMonitoringRS_Id__Format.

Inductive RadioLinkMonitoringRS__purpose__Type : Set :=
 | RadioLinkMonitoringRS__purpose__beamFailure
 | RadioLinkMonitoringRS__purpose__rlf
 | RadioLinkMonitoringRS__purpose__both
.
Definition RadioLinkMonitoringRS__purpose__cond := (fun (_ : RadioLinkMonitoringRS__purpose__Type) => True).
Lemma RadioLinkMonitoringRS__purpose__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RadioLinkMonitoringRS__purpose__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 RadioLinkMonitoringRS__purpose__nat__helper.

Definition RadioLinkMonitoringRS__purpose__F1 t :=
  match t with
  | RadioLinkMonitoringRS__purpose__beamFailure => 0
  | RadioLinkMonitoringRS__purpose__rlf => 1
  | RadioLinkMonitoringRS__purpose__both => 2
  end.
Definition RadioLinkMonitoringRS__purpose__F2 n :=
  match n with
  | 0 => RadioLinkMonitoringRS__purpose__beamFailure
  | 1 => RadioLinkMonitoringRS__purpose__rlf
  | 2 => RadioLinkMonitoringRS__purpose__both
  | _ => RadioLinkMonitoringRS__purpose__beamFailure
  end.
Lemma RadioLinkMonitoringRS__purpose__F1F2 : forall x : RadioLinkMonitoringRS__purpose__Type, (RadioLinkMonitoringRS__purpose__F1 x <= 2) /\ RadioLinkMonitoringRS__purpose__F2 (RadioLinkMonitoringRS__purpose__F1 x) = x. imp_solve. Qed.
Lemma RadioLinkMonitoringRS__purpose__F2F1 : forall (y : nat) (H : y <= 2), RadioLinkMonitoringRS__purpose__F1 (RadioLinkMonitoringRS__purpose__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.


Inductive RadioLinkMonitoringRS__detectionResource__Type : Set :=
  | RadioLinkMonitoringRS__detectionResource__ssb_Index : SSB_Index__Type -> RadioLinkMonitoringRS__detectionResource__Type
  | RadioLinkMonitoringRS__detectionResource__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> RadioLinkMonitoringRS__detectionResource__Type
.
Definition RadioLinkMonitoringRS__detectionResource__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition RadioLinkMonitoringRS__detectionResource__cond (c : RadioLinkMonitoringRS__detectionResource__Type) := 
  match c with
  | RadioLinkMonitoringRS__detectionResource__ssb_Index t => SSB_Index__cond t 
  | RadioLinkMonitoringRS__detectionResource__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  end.

Lemma RadioLinkMonitoringRS__detectionResource__len_helper1 : to_bit_sz (length RadioLinkMonitoringRS__detectionResource__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RadioLinkMonitoringRS__detectionResource__len_helper2 : 2 <= length2 RadioLinkMonitoringRS__detectionResource__list.
 simpl. lia. Qed.
Record RadioLinkMonitoringRS__Type : Set :=
  make__RadioLinkMonitoringRS__Type {
    RadioLinkMonitoringRS__radioLinkMonitoringRS_Id : RadioLinkMonitoringRS_Id__Type ;
    RadioLinkMonitoringRS__purpose : RadioLinkMonitoringRS__purpose__Type ;
    RadioLinkMonitoringRS__detectionResource : RadioLinkMonitoringRS__detectionResource__Type ;
}.
Definition RadioLinkMonitoringRS__root_list : list seq_elem := (
 Nor RadioLinkMonitoringRS_Id__Type RadioLinkMonitoringRS_Id__cond ::
 Nor RadioLinkMonitoringRS__purpose__Type RadioLinkMonitoringRS__purpose__cond ::
 Nor RadioLinkMonitoringRS__detectionResource__Type RadioLinkMonitoringRS__detectionResource__cond ::
 nil).
Definition RadioLinkMonitoringRS__ext_list : list typ := (
  nil).
Definition RadioLinkMonitoringRS__cond (z : RadioLinkMonitoringRS__Type) := 
(  RadioLinkMonitoringRS_Id__cond (RadioLinkMonitoringRS__radioLinkMonitoringRS_Id z) /\
  RadioLinkMonitoringRS__purpose__cond (RadioLinkMonitoringRS__purpose z) /\
  RadioLinkMonitoringRS__detectionResource__cond (RadioLinkMonitoringRS__detectionResource z) /\
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
Definition RadioLinkMonitoringRS__purpose__Format : T_Format RadioLinkMonitoringRS__purpose__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RadioLinkMonitoringRS__purpose__nat__Format RadioLinkMonitoringRS__purpose__F1 RadioLinkMonitoringRS__purpose__F2 RadioLinkMonitoringRS__purpose__F1F2 RadioLinkMonitoringRS__purpose__F2F1.

Opaque RadioLinkMonitoringRS__purpose__cond RadioLinkMonitoringRS__purpose__Format.


Definition RadioLinkMonitoringRS__detectionResource__Format_Type := Eval cbn in get_formats RadioLinkMonitoringRS__detectionResource__list.
Definition RadioLinkMonitoringRS__detectionResource__Format_list : RadioLinkMonitoringRS__detectionResource__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, unit__Format)).
Definition RadioLinkMonitoringRS__detectionResource__list__Format := Eval compute in choice_format RadioLinkMonitoringRS__detectionResource__list RadioLinkMonitoringRS__detectionResource__len_helper1 RadioLinkMonitoringRS__detectionResource__len_helper2  RadioLinkMonitoringRS__detectionResource__Format_list.
Definition RadioLinkMonitoringRS__detectionResource__F1 (z : RadioLinkMonitoringRS__detectionResource__Type) : (choice RadioLinkMonitoringRS__detectionResource__list) :=
  match z with
   | RadioLinkMonitoringRS__detectionResource__ssb_Index t => existT _ 0 t
  | RadioLinkMonitoringRS__detectionResource__csi_RS_Index t => existT _ 1 t
  end.
Definition RadioLinkMonitoringRS__detectionResource__g := (fun n => typ_set (get_nth_typ RadioLinkMonitoringRS__detectionResource__list n)).
Definition RadioLinkMonitoringRS__detectionResource__F2 (y : choice RadioLinkMonitoringRS__detectionResource__list) : RadioLinkMonitoringRS__detectionResource__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RadioLinkMonitoringRS__detectionResource__g n -> RadioLinkMonitoringRS__detectionResource__Type) with
    | 0 => fun (t : SSB_Index__Type) => RadioLinkMonitoringRS__detectionResource__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => RadioLinkMonitoringRS__detectionResource__csi_RS_Index t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RadioLinkMonitoringRS__detectionResource__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RadioLinkMonitoringRS__detectionResource__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RadioLinkMonitoringRS__detectionResource__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RadioLinkMonitoringRS__detectionResource__Type with end) n0
           end t0).

Lemma RadioLinkMonitoringRS__detectionResource__helper2 :  forall (y : RadioLinkMonitoringRS__detectionResource__Type), RadioLinkMonitoringRS__detectionResource__cond y -> choice_cond RadioLinkMonitoringRS__detectionResource__list (RadioLinkMonitoringRS__detectionResource__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RadioLinkMonitoringRS__detectionResource__helper3 :  forall (y : RadioLinkMonitoringRS__detectionResource__Type), RadioLinkMonitoringRS__detectionResource__F2 (RadioLinkMonitoringRS__detectionResource__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RadioLinkMonitoringRS__detectionResource__helper4 : (forall b : choice RadioLinkMonitoringRS__detectionResource__list, choice_cond RadioLinkMonitoringRS__detectionResource__list b -> RadioLinkMonitoringRS__detectionResource__cond (RadioLinkMonitoringRS__detectionResource__F2 b) /\ RadioLinkMonitoringRS__detectionResource__F1 (RadioLinkMonitoringRS__detectionResource__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RadioLinkMonitoringRS__detectionResource__F1 RadioLinkMonitoringRS__detectionResource__F2.
Definition RadioLinkMonitoringRS__detectionResource__Format : T_Format RadioLinkMonitoringRS__detectionResource__Type RadioLinkMonitoringRS__detectionResource__cond :=
  (* Eval compute in *) proj2_format RadioLinkMonitoringRS__detectionResource__cond RadioLinkMonitoringRS__detectionResource__list__Format RadioLinkMonitoringRS__detectionResource__F1 RadioLinkMonitoringRS__detectionResource__F2 RadioLinkMonitoringRS__detectionResource__helper2 RadioLinkMonitoringRS__detectionResource__helper3 RadioLinkMonitoringRS__detectionResource__helper4.
Opaque RadioLinkMonitoringRS__detectionResource__cond RadioLinkMonitoringRS__detectionResource__Format.


Definition RadioLinkMonitoringRS__root_Format_Type := Eval cbn in seq_format_prod RadioLinkMonitoringRS__root_list.
Definition RadioLinkMonitoringRS__root_Format_list : RadioLinkMonitoringRS__root_Format_Type :=
  (RadioLinkMonitoringRS_Id__Format, (RadioLinkMonitoringRS__purpose__Format, (RadioLinkMonitoringRS__detectionResource__Format, unit_format))).

Definition RadioLinkMonitoringRS__ext_Format_Type := Eval cbn in get_formats RadioLinkMonitoringRS__ext_list.
Definition RadioLinkMonitoringRS__ext_Format_list : RadioLinkMonitoringRS__ext_Format_Type :=
  unit__Format.

Definition RadioLinkMonitoringRS__list_type : Set := (seq_type RadioLinkMonitoringRS__root_list) * (seq_ext_type RadioLinkMonitoringRS__ext_list).
Definition RadioLinkMonitoringRS__list_cond (z : RadioLinkMonitoringRS__list_type) : Prop :=
        (seq_cond RadioLinkMonitoringRS__root_list (fst z)) /\ (seq_ext_cond RadioLinkMonitoringRS__ext_list (snd z)).
Definition RadioLinkMonitoringRS__list_format : T_Format RadioLinkMonitoringRS__list_type RadioLinkMonitoringRS__list_cond :=
 (* Eval compute in *) seq_ext_format RadioLinkMonitoringRS__root_list RadioLinkMonitoringRS__root_Format_list RadioLinkMonitoringRS__ext_list RadioLinkMonitoringRS__ext_Format_list.

Opaque RadioLinkMonitoringRS__list_format.
Definition RadioLinkMonitoringRS__F1 (z : RadioLinkMonitoringRS__Type) : RadioLinkMonitoringRS__list_type :=
  (((RadioLinkMonitoringRS__radioLinkMonitoringRS_Id z, (RadioLinkMonitoringRS__purpose z, (RadioLinkMonitoringRS__detectionResource z, tt)))), (
tt)).
Definition RadioLinkMonitoringRS__F2 (y : RadioLinkMonitoringRS__list_type) : RadioLinkMonitoringRS__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__RadioLinkMonitoringRS__Type j0 j1 j2
  end.
Definition RadioLinkMonitoringRS__helper1 : (forall a : RadioLinkMonitoringRS__Type, RadioLinkMonitoringRS__cond a -> RadioLinkMonitoringRS__list_cond (RadioLinkMonitoringRS__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RadioLinkMonitoringRS__helper2 : (forall a : RadioLinkMonitoringRS__Type, RadioLinkMonitoringRS__F2 (RadioLinkMonitoringRS__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RadioLinkMonitoringRS__helper3 : (forall b : RadioLinkMonitoringRS__list_type, RadioLinkMonitoringRS__list_cond b -> RadioLinkMonitoringRS__cond (RadioLinkMonitoringRS__F2 b) /\ RadioLinkMonitoringRS__F1 (RadioLinkMonitoringRS__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RadioLinkMonitoringRS__cond, RadioLinkMonitoringRS__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RadioLinkMonitoringRS__Format : T_Format RadioLinkMonitoringRS__Type RadioLinkMonitoringRS__cond :=
 proj2_format RadioLinkMonitoringRS__cond RadioLinkMonitoringRS__list_format  RadioLinkMonitoringRS__F1 RadioLinkMonitoringRS__F2 RadioLinkMonitoringRS__helper1 RadioLinkMonitoringRS__helper2 RadioLinkMonitoringRS__helper3.

Opaque RadioLinkMonitoringRS__cond RadioLinkMonitoringRS__Format.

