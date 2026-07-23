Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.FDM_TDM_r16.
Definition RepetitionSchemeConfig_r16__fdm_TDM_r16__Type := SetupRelease__Type FDM_TDM_r16__Type.
Definition RepetitionSchemeConfig_r16__fdm_TDM_r16__cond := SetupRelease__cond _ FDM_TDM_r16__cond.
Definition RepetitionSchemeConfig_r16__fdm_TDM_r16__Format : T_Format RepetitionSchemeConfig_r16__fdm_TDM_r16__Type RepetitionSchemeConfig_r16__fdm_TDM_r16__cond := SetupRelease__Format _ _ FDM_TDM_r16__Format.
Opaque RepetitionSchemeConfig_r16__fdm_TDM_r16__cond RepetitionSchemeConfig_r16__fdm_TDM_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SlotBased_r16.
Definition RepetitionSchemeConfig_r16__slotBased_r16__Type := SetupRelease__Type SlotBased_r16__Type.
Definition RepetitionSchemeConfig_r16__slotBased_r16__cond := SetupRelease__cond _ SlotBased_r16__cond.
Definition RepetitionSchemeConfig_r16__slotBased_r16__Format : T_Format RepetitionSchemeConfig_r16__slotBased_r16__Type RepetitionSchemeConfig_r16__slotBased_r16__cond := SetupRelease__Format _ _ SlotBased_r16__Format.
Opaque RepetitionSchemeConfig_r16__slotBased_r16__cond RepetitionSchemeConfig_r16__slotBased_r16__Format.


Inductive RepetitionSchemeConfig_r16__Type : Set :=
  | RepetitionSchemeConfig_r16__fdm_TDM_r16 : RepetitionSchemeConfig_r16__fdm_TDM_r16__Type -> RepetitionSchemeConfig_r16__Type
  | RepetitionSchemeConfig_r16__slotBased_r16 : RepetitionSchemeConfig_r16__slotBased_r16__Type -> RepetitionSchemeConfig_r16__Type
.
Definition RepetitionSchemeConfig_r16__list : list typ := (
typ_cons RepetitionSchemeConfig_r16__fdm_TDM_r16__Type RepetitionSchemeConfig_r16__fdm_TDM_r16__cond ::
typ_cons RepetitionSchemeConfig_r16__slotBased_r16__Type RepetitionSchemeConfig_r16__slotBased_r16__cond ::
 nil).
Definition RepetitionSchemeConfig_r16__cond (c : RepetitionSchemeConfig_r16__Type) := 
  match c with
  | RepetitionSchemeConfig_r16__fdm_TDM_r16 t => RepetitionSchemeConfig_r16__fdm_TDM_r16__cond t 
  | RepetitionSchemeConfig_r16__slotBased_r16 t => RepetitionSchemeConfig_r16__slotBased_r16__cond t 
  end.

Lemma RepetitionSchemeConfig_r16__len_helper1 : to_bit_sz (length RepetitionSchemeConfig_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RepetitionSchemeConfig_r16__len_helper2 : 2 <= length2 RepetitionSchemeConfig_r16__list.
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
Opaque RepetitionSchemeConfig_r16__fdm_TDM_r16__cond RepetitionSchemeConfig_r16__fdm_TDM_r16__Format.

Opaque RepetitionSchemeConfig_r16__slotBased_r16__cond RepetitionSchemeConfig_r16__slotBased_r16__Format.


Definition RepetitionSchemeConfig_r16__Format_Type := Eval cbn in get_formats RepetitionSchemeConfig_r16__list.
Definition RepetitionSchemeConfig_r16__Format_list : RepetitionSchemeConfig_r16__Format_Type :=
  (RepetitionSchemeConfig_r16__fdm_TDM_r16__Format, (RepetitionSchemeConfig_r16__slotBased_r16__Format, unit__Format)).
Definition RepetitionSchemeConfig_r16__list__Format := Eval compute in choice_format RepetitionSchemeConfig_r16__list RepetitionSchemeConfig_r16__len_helper1 RepetitionSchemeConfig_r16__len_helper2  RepetitionSchemeConfig_r16__Format_list.
Definition RepetitionSchemeConfig_r16__F1 (z : RepetitionSchemeConfig_r16__Type) : (choice RepetitionSchemeConfig_r16__list) :=
  match z with
   | RepetitionSchemeConfig_r16__fdm_TDM_r16 t => existT _ 0 t
  | RepetitionSchemeConfig_r16__slotBased_r16 t => existT _ 1 t
  end.
Definition RepetitionSchemeConfig_r16__g := (fun n => typ_set (get_nth_typ RepetitionSchemeConfig_r16__list n)).
Definition RepetitionSchemeConfig_r16__F2 (y : choice RepetitionSchemeConfig_r16__list) : RepetitionSchemeConfig_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RepetitionSchemeConfig_r16__g n -> RepetitionSchemeConfig_r16__Type) with
    | 0 => fun (t : RepetitionSchemeConfig_r16__fdm_TDM_r16__Type) => RepetitionSchemeConfig_r16__fdm_TDM_r16 t 
    | 1 => fun (t : RepetitionSchemeConfig_r16__slotBased_r16__Type) => RepetitionSchemeConfig_r16__slotBased_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RepetitionSchemeConfig_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RepetitionSchemeConfig_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RepetitionSchemeConfig_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RepetitionSchemeConfig_r16__Type with end) n0
           end t0).

Lemma RepetitionSchemeConfig_r16__helper2 :  forall (y : RepetitionSchemeConfig_r16__Type), RepetitionSchemeConfig_r16__cond y -> choice_cond RepetitionSchemeConfig_r16__list (RepetitionSchemeConfig_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RepetitionSchemeConfig_r16__helper3 :  forall (y : RepetitionSchemeConfig_r16__Type), RepetitionSchemeConfig_r16__F2 (RepetitionSchemeConfig_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RepetitionSchemeConfig_r16__helper4 : (forall b : choice RepetitionSchemeConfig_r16__list, choice_cond RepetitionSchemeConfig_r16__list b -> RepetitionSchemeConfig_r16__cond (RepetitionSchemeConfig_r16__F2 b) /\ RepetitionSchemeConfig_r16__F1 (RepetitionSchemeConfig_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RepetitionSchemeConfig_r16__F1 RepetitionSchemeConfig_r16__F2.
Definition RepetitionSchemeConfig_r16__Format : T_Format RepetitionSchemeConfig_r16__Type RepetitionSchemeConfig_r16__cond :=
  (* Eval compute in *) proj2_format RepetitionSchemeConfig_r16__cond RepetitionSchemeConfig_r16__list__Format RepetitionSchemeConfig_r16__F1 RepetitionSchemeConfig_r16__F2 RepetitionSchemeConfig_r16__helper2 RepetitionSchemeConfig_r16__helper3 RepetitionSchemeConfig_r16__helper4.
Opaque RepetitionSchemeConfig_r16__cond RepetitionSchemeConfig_r16__Format.

