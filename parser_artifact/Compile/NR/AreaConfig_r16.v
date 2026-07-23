Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CellGlobalIdList_r16.

Opaque CellGlobalIdList_r16__cond CellGlobalIdList_r16__Format.

Require Import NR.TrackingAreaCodeList_r16.

Opaque TrackingAreaCodeList_r16__cond TrackingAreaCodeList_r16__Format.

Require Import NR.TrackingAreaIdentityList_r16.

Opaque TrackingAreaIdentityList_r16__cond TrackingAreaIdentityList_r16__Format.


Inductive AreaConfig_r16__Type : Set :=
  | AreaConfig_r16__cellGlobalIdList_r16 : CellGlobalIdList_r16__Type -> AreaConfig_r16__Type
  | AreaConfig_r16__trackingAreaCodeList_r16 : TrackingAreaCodeList_r16__Type -> AreaConfig_r16__Type
  | AreaConfig_r16__trackingAreaIdentityList_r16 : TrackingAreaIdentityList_r16__Type -> AreaConfig_r16__Type
.
Definition AreaConfig_r16__list : list typ := (
typ_cons CellGlobalIdList_r16__Type CellGlobalIdList_r16__cond ::
typ_cons TrackingAreaCodeList_r16__Type TrackingAreaCodeList_r16__cond ::
typ_cons TrackingAreaIdentityList_r16__Type TrackingAreaIdentityList_r16__cond ::
 nil).
Definition AreaConfig_r16__cond (c : AreaConfig_r16__Type) := 
  match c with
  | AreaConfig_r16__cellGlobalIdList_r16 t => CellGlobalIdList_r16__cond t 
  | AreaConfig_r16__trackingAreaCodeList_r16 t => TrackingAreaCodeList_r16__cond t 
  | AreaConfig_r16__trackingAreaIdentityList_r16 t => TrackingAreaIdentityList_r16__cond t 
  end.

Lemma AreaConfig_r16__len_helper1 : to_bit_sz (length AreaConfig_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma AreaConfig_r16__len_helper2 : 2 <= length2 AreaConfig_r16__list.
 simpl. lia. Qed.

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

Definition AreaConfig_r16__Format_Type := Eval cbn in get_formats AreaConfig_r16__list.
Definition AreaConfig_r16__Format_list : AreaConfig_r16__Format_Type :=
  (CellGlobalIdList_r16__Format, (TrackingAreaCodeList_r16__Format, (TrackingAreaIdentityList_r16__Format, unit__Format))).
Definition AreaConfig_r16__list__Format := Eval compute in choice_format AreaConfig_r16__list AreaConfig_r16__len_helper1 AreaConfig_r16__len_helper2  AreaConfig_r16__Format_list.
Definition AreaConfig_r16__F1 (z : AreaConfig_r16__Type) : (choice AreaConfig_r16__list) :=
  match z with
   | AreaConfig_r16__cellGlobalIdList_r16 t => existT _ 0 t
  | AreaConfig_r16__trackingAreaCodeList_r16 t => existT _ 1 t
  | AreaConfig_r16__trackingAreaIdentityList_r16 t => existT _ 2 t
  end.
Definition AreaConfig_r16__g := (fun n => typ_set (get_nth_typ AreaConfig_r16__list n)).
Definition AreaConfig_r16__F2 (y : choice AreaConfig_r16__list) : AreaConfig_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (AreaConfig_r16__g n -> AreaConfig_r16__Type) with
    | 0 => fun (t : CellGlobalIdList_r16__Type) => AreaConfig_r16__cellGlobalIdList_r16 t 
    | 1 => fun (t : TrackingAreaCodeList_r16__Type) => AreaConfig_r16__trackingAreaCodeList_r16 t 
    | 2 => fun (t : TrackingAreaIdentityList_r16__Type) => AreaConfig_r16__trackingAreaIdentityList_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : AreaConfig_r16__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ AreaConfig_r16__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len AreaConfig_r16__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return AreaConfig_r16__Type with end) n0
           end t0).

Lemma AreaConfig_r16__helper2 :  forall (y : AreaConfig_r16__Type), AreaConfig_r16__cond y -> choice_cond AreaConfig_r16__list (AreaConfig_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma AreaConfig_r16__helper3 :  forall (y : AreaConfig_r16__Type), AreaConfig_r16__F2 (AreaConfig_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma AreaConfig_r16__helper4 : (forall b : choice AreaConfig_r16__list, choice_cond AreaConfig_r16__list b -> AreaConfig_r16__cond (AreaConfig_r16__F2 b) /\ AreaConfig_r16__F1 (AreaConfig_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length AreaConfig_r16__F1 AreaConfig_r16__F2.
Definition AreaConfig_r16__Format : T_Format AreaConfig_r16__Type AreaConfig_r16__cond :=
  (* Eval compute in *) proj2_format AreaConfig_r16__cond AreaConfig_r16__list__Format AreaConfig_r16__F1 AreaConfig_r16__F2 AreaConfig_r16__helper2 AreaConfig_r16__helper3 AreaConfig_r16__helper4.
Opaque AreaConfig_r16__cond AreaConfig_r16__Format.

