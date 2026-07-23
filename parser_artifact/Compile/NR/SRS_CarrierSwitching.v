Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SRS_CarrierSwitching__srs_SwitchFromServCellIndex__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SRS_CarrierSwitching__srs_SwitchFromServCellIndex__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_CarrierSwitching__srs_SwitchFromServCellIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_CarrierSwitching__srs_SwitchFromServCellIndex__Type := Z.
Definition SRS_CarrierSwitching__srs_SwitchFromServCellIndex__cond := (fun z => (0 <= z <= 31)%Z).
Inductive SRS_CarrierSwitching__srs_SwitchFromCarrier__Type : Set :=
 | SRS_CarrierSwitching__srs_SwitchFromCarrier__sUL
 | SRS_CarrierSwitching__srs_SwitchFromCarrier__nUL
.
Definition SRS_CarrierSwitching__srs_SwitchFromCarrier__cond := (fun (_ : SRS_CarrierSwitching__srs_SwitchFromCarrier__Type) => True).
Lemma SRS_CarrierSwitching__srs_SwitchFromCarrier__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_CarrierSwitching__srs_SwitchFromCarrier__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SRS_CarrierSwitching__srs_SwitchFromCarrier__nat__helper.

Definition SRS_CarrierSwitching__srs_SwitchFromCarrier__F1 t :=
  match t with
  | SRS_CarrierSwitching__srs_SwitchFromCarrier__sUL => 0
  | SRS_CarrierSwitching__srs_SwitchFromCarrier__nUL => 1
  end.
Definition SRS_CarrierSwitching__srs_SwitchFromCarrier__F2 n :=
  match n with
  | 0 => SRS_CarrierSwitching__srs_SwitchFromCarrier__sUL
  | 1 => SRS_CarrierSwitching__srs_SwitchFromCarrier__nUL
  | _ => SRS_CarrierSwitching__srs_SwitchFromCarrier__sUL
  end.
Lemma SRS_CarrierSwitching__srs_SwitchFromCarrier__F1F2 : forall x : SRS_CarrierSwitching__srs_SwitchFromCarrier__Type, (SRS_CarrierSwitching__srs_SwitchFromCarrier__F1 x <= 1) /\ SRS_CarrierSwitching__srs_SwitchFromCarrier__F2 (SRS_CarrierSwitching__srs_SwitchFromCarrier__F1 x) = x. imp_solve. Qed.
Lemma SRS_CarrierSwitching__srs_SwitchFromCarrier__F2F1 : forall (y : nat) (H : y <= 1), SRS_CarrierSwitching__srs_SwitchFromCarrier__F1 (SRS_CarrierSwitching__srs_SwitchFromCarrier__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SRS_TPC_PDCCH_Config.

Opaque SRS_TPC_PDCCH_Config__cond SRS_TPC_PDCCH_Config__Format.

Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Type := list SRS_TPC_PDCCH_Config__Type.

Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__helper1 : (0 <= 1 <= 32)%Z.  lia. Qed.
Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__cond (z : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Type) :=  (1 <= Z.of_nat (length z) <= 32)%Z /\ (list_and SRS_TPC_PDCCH_Config__cond z) .

Require Import NR.SRS_TPC_PDCCH_Config.

Opaque SRS_TPC_PDCCH_Config__cond SRS_TPC_PDCCH_Config__Format.


Inductive SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type : Set :=
  | SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Type -> SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type
  | SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeB : SRS_TPC_PDCCH_Config__Type -> SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type
.
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list : list typ := (
typ_cons SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Type SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__cond ::
typ_cons SRS_TPC_PDCCH_Config__Type SRS_TPC_PDCCH_Config__cond ::
 nil).
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond (c : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type) := 
  match c with
  | SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA t => SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__cond t 
  | SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeB t => SRS_TPC_PDCCH_Config__cond t 
  end.

Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__len_helper1 : to_bit_sz (length SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__len_helper2 : 2 <= length2 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list.
 simpl. lia. Qed.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition SRS_CarrierSwitching__monitoringCells__Type := list ServCellIndex__Type.

Lemma SRS_CarrierSwitching__monitoringCells__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma SRS_CarrierSwitching__monitoringCells__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_CarrierSwitching__monitoringCells__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_CarrierSwitching__monitoringCells__cond (z : SRS_CarrierSwitching__monitoringCells__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and ServCellIndex__cond z) .

Record SRS_CarrierSwitching__Type : Set :=
  make__SRS_CarrierSwitching__Type {
    SRS_CarrierSwitching__srs_SwitchFromServCellIndex : option Z ;
    SRS_CarrierSwitching__srs_SwitchFromCarrier : SRS_CarrierSwitching__srs_SwitchFromCarrier__Type ;
    SRS_CarrierSwitching__srs_TPC_PDCCH_Group : option SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type ;
    SRS_CarrierSwitching__monitoringCells : option SRS_CarrierSwitching__monitoringCells__Type ;
}.
Definition SRS_CarrierSwitching__root_list : list seq_elem := (
 Opt Z SRS_CarrierSwitching__srs_SwitchFromServCellIndex__cond ::
 Nor SRS_CarrierSwitching__srs_SwitchFromCarrier__Type SRS_CarrierSwitching__srs_SwitchFromCarrier__cond ::
 Opt SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond ::
 Opt SRS_CarrierSwitching__monitoringCells__Type SRS_CarrierSwitching__monitoringCells__cond ::
 nil).
Definition SRS_CarrierSwitching__ext_list : list typ := (
  nil).
Definition SRS_CarrierSwitching__cond (z : SRS_CarrierSwitching__Type) := 
(  opt_cond SRS_CarrierSwitching__srs_SwitchFromServCellIndex__cond (SRS_CarrierSwitching__srs_SwitchFromServCellIndex z) /\
  SRS_CarrierSwitching__srs_SwitchFromCarrier__cond (SRS_CarrierSwitching__srs_SwitchFromCarrier z) /\
  opt_cond SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond (SRS_CarrierSwitching__srs_TPC_PDCCH_Group z) /\
  opt_cond SRS_CarrierSwitching__monitoringCells__cond (SRS_CarrierSwitching__monitoringCells z) /\
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
Definition SRS_CarrierSwitching__srs_SwitchFromServCellIndex__Format : T_Format Z SRS_CarrierSwitching__srs_SwitchFromServCellIndex__cond :=
 ranged_int_format (0) (31) SRS_CarrierSwitching__srs_SwitchFromServCellIndex__helper1 SRS_CarrierSwitching__srs_SwitchFromServCellIndex__helper2.

Opaque SRS_CarrierSwitching__srs_SwitchFromServCellIndex__cond SRS_CarrierSwitching__srs_SwitchFromServCellIndex__Format.

Definition SRS_CarrierSwitching__srs_SwitchFromCarrier__Format : T_Format SRS_CarrierSwitching__srs_SwitchFromCarrier__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_CarrierSwitching__srs_SwitchFromCarrier__nat__Format SRS_CarrierSwitching__srs_SwitchFromCarrier__F1 SRS_CarrierSwitching__srs_SwitchFromCarrier__F2 SRS_CarrierSwitching__srs_SwitchFromCarrier__F1F2 SRS_CarrierSwitching__srs_SwitchFromCarrier__F2F1.

Opaque SRS_CarrierSwitching__srs_SwitchFromCarrier__cond SRS_CarrierSwitching__srs_SwitchFromCarrier__Format.

Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Format : T_Format SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Type SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__cond := seq_of_format SRS_TPC_PDCCH_Config__Format 1 32 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__helper1 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__helper2.

Opaque SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__cond SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Format.


Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format_Type := Eval cbn in get_formats SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list.
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format_list : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format_Type :=
  (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Format, (SRS_TPC_PDCCH_Config__Format, unit__Format)).
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list__Format := Eval compute in choice_format SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list SRS_CarrierSwitching__srs_TPC_PDCCH_Group__len_helper1 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__len_helper2  SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format_list.
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F1 (z : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type) : (choice SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list) :=
  match z with
   | SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA t => existT _ 0 t
  | SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeB t => existT _ 1 t
  end.
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__g := (fun n => typ_set (get_nth_typ SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list n)).
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F2 (y : choice SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list) : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__g n -> SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type) with
    | 0 => fun (t : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA__Type) => SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeA t 
    | 1 => fun (t : SRS_TPC_PDCCH_Config__Type) => SRS_CarrierSwitching__srs_TPC_PDCCH_Group__typeB t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type with end) n0
           end t0).

Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__helper2 :  forall (y : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type), SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond y -> choice_cond SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__helper3 :  forall (y : SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type), SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F2 (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_CarrierSwitching__srs_TPC_PDCCH_Group__helper4 : (forall b : choice SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list, choice_cond SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list b -> SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F2 b) /\ SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F1 (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F1 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F2.
Definition SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format : T_Format SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Type SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond :=
  (* Eval compute in *) proj2_format SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond SRS_CarrierSwitching__srs_TPC_PDCCH_Group__list__Format SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F1 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__F2 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__helper2 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__helper3 SRS_CarrierSwitching__srs_TPC_PDCCH_Group__helper4.
Opaque SRS_CarrierSwitching__srs_TPC_PDCCH_Group__cond SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format.

Definition SRS_CarrierSwitching__monitoringCells__Format : T_Format SRS_CarrierSwitching__monitoringCells__Type SRS_CarrierSwitching__monitoringCells__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCells SRS_CarrierSwitching__monitoringCells__helper1 SRS_CarrierSwitching__monitoringCells__helper2.

Opaque SRS_CarrierSwitching__monitoringCells__cond SRS_CarrierSwitching__monitoringCells__Format.


Definition SRS_CarrierSwitching__root_Format_Type := Eval cbn in seq_format_prod SRS_CarrierSwitching__root_list.
Definition SRS_CarrierSwitching__root_Format_list : SRS_CarrierSwitching__root_Format_Type :=
  (SRS_CarrierSwitching__srs_SwitchFromServCellIndex__Format, (SRS_CarrierSwitching__srs_SwitchFromCarrier__Format, (SRS_CarrierSwitching__srs_TPC_PDCCH_Group__Format, (SRS_CarrierSwitching__monitoringCells__Format, unit_format)))).

Definition SRS_CarrierSwitching__ext_Format_Type := Eval cbn in get_formats SRS_CarrierSwitching__ext_list.
Definition SRS_CarrierSwitching__ext_Format_list : SRS_CarrierSwitching__ext_Format_Type :=
  unit__Format.

Definition SRS_CarrierSwitching__list_type : Set := (seq_type SRS_CarrierSwitching__root_list) * (seq_ext_type SRS_CarrierSwitching__ext_list).
Definition SRS_CarrierSwitching__list_cond (z : SRS_CarrierSwitching__list_type) : Prop :=
        (seq_cond SRS_CarrierSwitching__root_list (fst z)) /\ (seq_ext_cond SRS_CarrierSwitching__ext_list (snd z)).
Definition SRS_CarrierSwitching__list_format : T_Format SRS_CarrierSwitching__list_type SRS_CarrierSwitching__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_CarrierSwitching__root_list SRS_CarrierSwitching__root_Format_list SRS_CarrierSwitching__ext_list SRS_CarrierSwitching__ext_Format_list.

Opaque SRS_CarrierSwitching__list_format.
Definition SRS_CarrierSwitching__F1 (z : SRS_CarrierSwitching__Type) : SRS_CarrierSwitching__list_type :=
  (((SRS_CarrierSwitching__srs_SwitchFromServCellIndex z, (SRS_CarrierSwitching__srs_SwitchFromCarrier z, (SRS_CarrierSwitching__srs_TPC_PDCCH_Group z, (SRS_CarrierSwitching__monitoringCells z, tt))))), (
tt)).
Definition SRS_CarrierSwitching__F2 (y : SRS_CarrierSwitching__list_type) : SRS_CarrierSwitching__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SRS_CarrierSwitching__Type j0 j1 j2 j3
  end.
Definition SRS_CarrierSwitching__helper1 : (forall a : SRS_CarrierSwitching__Type, SRS_CarrierSwitching__cond a -> SRS_CarrierSwitching__list_cond (SRS_CarrierSwitching__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_CarrierSwitching__helper2 : (forall a : SRS_CarrierSwitching__Type, SRS_CarrierSwitching__F2 (SRS_CarrierSwitching__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_CarrierSwitching__helper3 : (forall b : SRS_CarrierSwitching__list_type, SRS_CarrierSwitching__list_cond b -> SRS_CarrierSwitching__cond (SRS_CarrierSwitching__F2 b) /\ SRS_CarrierSwitching__F1 (SRS_CarrierSwitching__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_CarrierSwitching__cond, SRS_CarrierSwitching__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_CarrierSwitching__Format : T_Format SRS_CarrierSwitching__Type SRS_CarrierSwitching__cond :=
 proj2_format SRS_CarrierSwitching__cond SRS_CarrierSwitching__list_format  SRS_CarrierSwitching__F1 SRS_CarrierSwitching__F2 SRS_CarrierSwitching__helper1 SRS_CarrierSwitching__helper2 SRS_CarrierSwitching__helper3.

Opaque SRS_CarrierSwitching__cond SRS_CarrierSwitching__Format.

