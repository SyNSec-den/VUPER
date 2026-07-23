Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type : Set :=
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms160
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms320
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms1280
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms2560
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms61440
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms81920
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms368640
 | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms737280
.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__cond := (fun (_ : UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type) => True).
Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__nat__helper.

Definition UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1 t :=
  match t with
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms160 => 0
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms320 => 1
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms1280 => 2
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms2560 => 3
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms61440 => 4
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms81920 => 5
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms368640 => 6
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms737280 => 7
  end.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F2 n :=
  match n with
  | 0 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms160
  | 1 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms320
  | 2 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms1280
  | 3 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms2560
  | 4 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms61440
  | 5 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms81920
  | 6 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms368640
  | 7 => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms737280
  | _ => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__ms160
  end.
Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1F2 : forall x : UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type, (UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1 x <= 7) /\ UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F2 (UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F2F1 : forall (y : nat) (H : y <= 7), UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1 (UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F2 y) = y. enum_solve H y. Qed.


Inductive UE_TxTEG_RequestUL_TDOA_Config_r17__Type : Set :=
  | UE_TxTEG_RequestUL_TDOA_Config_r17__oneShot_r17 : unit -> UE_TxTEG_RequestUL_TDOA_Config_r17__Type
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17 : UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type -> UE_TxTEG_RequestUL_TDOA_Config_r17__Type
.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__cond ::
 nil).
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__cond (c : UE_TxTEG_RequestUL_TDOA_Config_r17__Type) := 
  match c with
  | UE_TxTEG_RequestUL_TDOA_Config_r17__oneShot_r17 t => (fun _ => True) t 
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17 t => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__cond t 
  end.

Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__len_helper1 : to_bit_sz (length UE_TxTEG_RequestUL_TDOA_Config_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__len_helper2 : 2 <= length2 UE_TxTEG_RequestUL_TDOA_Config_r17__list.
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
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Format : T_Format UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__nat__Format UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1 UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F2 UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F1F2 UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__F2F1.

Opaque UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__cond UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Format.


Definition UE_TxTEG_RequestUL_TDOA_Config_r17__Format_Type := Eval cbn in get_formats UE_TxTEG_RequestUL_TDOA_Config_r17__list.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__Format_list : UE_TxTEG_RequestUL_TDOA_Config_r17__Format_Type :=
  (unit__Format, (UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Format, unit__Format)).
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__list__Format := Eval compute in choice_format UE_TxTEG_RequestUL_TDOA_Config_r17__list UE_TxTEG_RequestUL_TDOA_Config_r17__len_helper1 UE_TxTEG_RequestUL_TDOA_Config_r17__len_helper2  UE_TxTEG_RequestUL_TDOA_Config_r17__Format_list.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__F1 (z : UE_TxTEG_RequestUL_TDOA_Config_r17__Type) : (choice UE_TxTEG_RequestUL_TDOA_Config_r17__list) :=
  match z with
   | UE_TxTEG_RequestUL_TDOA_Config_r17__oneShot_r17 t => existT _ 0 t
  | UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17 t => existT _ 1 t
  end.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__g := (fun n => typ_set (get_nth_typ UE_TxTEG_RequestUL_TDOA_Config_r17__list n)).
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__F2 (y : choice UE_TxTEG_RequestUL_TDOA_Config_r17__list) : UE_TxTEG_RequestUL_TDOA_Config_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UE_TxTEG_RequestUL_TDOA_Config_r17__g n -> UE_TxTEG_RequestUL_TDOA_Config_r17__Type) with
    | 0 => fun (t : unit) => UE_TxTEG_RequestUL_TDOA_Config_r17__oneShot_r17 t 
    | 1 => fun (t : UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17__Type) => UE_TxTEG_RequestUL_TDOA_Config_r17__periodicReporting_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UE_TxTEG_RequestUL_TDOA_Config_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UE_TxTEG_RequestUL_TDOA_Config_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UE_TxTEG_RequestUL_TDOA_Config_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UE_TxTEG_RequestUL_TDOA_Config_r17__Type with end) n0
           end t0).

Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__helper2 :  forall (y : UE_TxTEG_RequestUL_TDOA_Config_r17__Type), UE_TxTEG_RequestUL_TDOA_Config_r17__cond y -> choice_cond UE_TxTEG_RequestUL_TDOA_Config_r17__list (UE_TxTEG_RequestUL_TDOA_Config_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__helper3 :  forall (y : UE_TxTEG_RequestUL_TDOA_Config_r17__Type), UE_TxTEG_RequestUL_TDOA_Config_r17__F2 (UE_TxTEG_RequestUL_TDOA_Config_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UE_TxTEG_RequestUL_TDOA_Config_r17__helper4 : (forall b : choice UE_TxTEG_RequestUL_TDOA_Config_r17__list, choice_cond UE_TxTEG_RequestUL_TDOA_Config_r17__list b -> UE_TxTEG_RequestUL_TDOA_Config_r17__cond (UE_TxTEG_RequestUL_TDOA_Config_r17__F2 b) /\ UE_TxTEG_RequestUL_TDOA_Config_r17__F1 (UE_TxTEG_RequestUL_TDOA_Config_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UE_TxTEG_RequestUL_TDOA_Config_r17__F1 UE_TxTEG_RequestUL_TDOA_Config_r17__F2.
Definition UE_TxTEG_RequestUL_TDOA_Config_r17__Format : T_Format UE_TxTEG_RequestUL_TDOA_Config_r17__Type UE_TxTEG_RequestUL_TDOA_Config_r17__cond :=
  (* Eval compute in *) proj2_format UE_TxTEG_RequestUL_TDOA_Config_r17__cond UE_TxTEG_RequestUL_TDOA_Config_r17__list__Format UE_TxTEG_RequestUL_TDOA_Config_r17__F1 UE_TxTEG_RequestUL_TDOA_Config_r17__F2 UE_TxTEG_RequestUL_TDOA_Config_r17__helper2 UE_TxTEG_RequestUL_TDOA_Config_r17__helper3 UE_TxTEG_RequestUL_TDOA_Config_r17__helper4.
Opaque UE_TxTEG_RequestUL_TDOA_Config_r17__cond UE_TxTEG_RequestUL_TDOA_Config_r17__Format.

