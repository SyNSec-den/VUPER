Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type : Set :=
 | MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__idle
 | MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__inactive
 | MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__outOfConnected
.
Definition MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__cond := (fun (_ : MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type) => True).
Lemma MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__nat__helper.

Definition MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1 t :=
  match t with
  | MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__idle => 0
  | MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__inactive => 1
  | MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__outOfConnected => 2
  end.
Definition MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2 n :=
  match n with
  | 0 => MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__idle
  | 1 => MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__inactive
  | 2 => MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__outOfConnected
  | _ => MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__idle
  end.
Lemma MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1F2 : forall x : MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type, (MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1 x <= 2) /\ MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2 (MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1 x) = x. imp_solve. Qed.
Lemma MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2F1 : forall (y : nat) (H : y <= 2), MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1 (MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MUSIM_GapPreferenceList_r17.

Opaque MUSIM_GapPreferenceList_r17__cond MUSIM_GapPreferenceList_r17__Format.

Record MUSIM_Assistance_r17__Type : Set :=
  make__MUSIM_Assistance_r17__Type {
    MUSIM_Assistance_r17__musim_PreferredRRC_State_r17 : option MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type ;
    MUSIM_Assistance_r17__musim_GapPreferenceList_r17 : option MUSIM_GapPreferenceList_r17__Type ;
}.
Definition MUSIM_Assistance_r17__list := (
 Opt MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__cond ::
 Opt MUSIM_GapPreferenceList_r17__Type MUSIM_GapPreferenceList_r17__cond ::
 nil).
Definition MUSIM_Assistance_r17__cond z := 
  opt_cond MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__cond (MUSIM_Assistance_r17__musim_PreferredRRC_State_r17 z) /\
  opt_cond MUSIM_GapPreferenceList_r17__cond (MUSIM_Assistance_r17__musim_GapPreferenceList_r17 z) /\
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
Definition MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Format : T_Format MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__nat__Format MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1 MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2 MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1F2 MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2F1.

Opaque MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__cond MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Format.


Definition MUSIM_Assistance_r17__Format_Type := Eval cbn in seq_format_prod MUSIM_Assistance_r17__list.
Definition MUSIM_Assistance_r17__Format_list : MUSIM_Assistance_r17__Format_Type :=
  (MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Format, (MUSIM_GapPreferenceList_r17__Format, unit_format)).
Definition MUSIM_Assistance_r17__list__Format := (*Eval compute in *) seq_format MUSIM_Assistance_r17__list MUSIM_Assistance_r17__Format_list.
Definition MUSIM_Assistance_r17__F1 z :=
  (MUSIM_Assistance_r17__musim_PreferredRRC_State_r17 z, (MUSIM_Assistance_r17__musim_GapPreferenceList_r17 z, tt)).
Definition MUSIM_Assistance_r17__F2 (y : seq_type MUSIM_Assistance_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MUSIM_Assistance_r17__Type i0 i1
  end.
Lemma MUSIM_Assistance_r17__F1F2_cond (z : MUSIM_Assistance_r17__Type)
  : MUSIM_Assistance_r17__cond z ->
  (seq_cond MUSIM_Assistance_r17__list (MUSIM_Assistance_r17__F1 z)).
intro H. unfold MUSIM_Assistance_r17__cond in H. simpl. auto. Qed.
Lemma MUSIM_Assistance_r17__F1F2_cond2 (z : MUSIM_Assistance_r17__Type)
 : MUSIM_Assistance_r17__F2 (MUSIM_Assistance_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MUSIM_Assistance_r17__F2F1_cond (y : seq_type MUSIM_Assistance_r17__list)
  : seq_cond MUSIM_Assistance_r17__list y ->
 (MUSIM_Assistance_r17__cond (MUSIM_Assistance_r17__F2 y)) /\  MUSIM_Assistance_r17__F1 (MUSIM_Assistance_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MUSIM_Assistance_r17__cond. simpl in *. auto.
 - simpl. unfold MUSIM_Assistance_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MUSIM_Assistance_r17__Format : T_Format MUSIM_Assistance_r17__Type MUSIM_Assistance_r17__cond :=
        proj2_format  MUSIM_Assistance_r17__cond MUSIM_Assistance_r17__list__Format
    MUSIM_Assistance_r17__F1 MUSIM_Assistance_r17__F2 MUSIM_Assistance_r17__F1F2_cond  MUSIM_Assistance_r17__F1F2_cond2 MUSIM_Assistance_r17__F2F1_cond.
Opaque MUSIM_Assistance_r17__cond MUSIM_Assistance_r17__Format.

