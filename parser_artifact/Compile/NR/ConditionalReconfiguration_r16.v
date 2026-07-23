Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ConditionalReconfiguration_r16__attemptCondReconfig_r16__Type : Set :=
 | ConditionalReconfiguration_r16__attemptCondReconfig_r16__true
.
Definition ConditionalReconfiguration_r16__attemptCondReconfig_r16__cond := (fun (_ : ConditionalReconfiguration_r16__attemptCondReconfig_r16__Type) => True).
Lemma ConditionalReconfiguration_r16__attemptCondReconfig_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConditionalReconfiguration_r16__attemptCondReconfig_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ConditionalReconfiguration_r16__attemptCondReconfig_r16__nat__helper.

Definition ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1 t :=
  match t with
  | ConditionalReconfiguration_r16__attemptCondReconfig_r16__true => 0
  end.
Definition ConditionalReconfiguration_r16__attemptCondReconfig_r16__F2 n :=
  match n with
  | 0 => ConditionalReconfiguration_r16__attemptCondReconfig_r16__true
  | _ => ConditionalReconfiguration_r16__attemptCondReconfig_r16__true
  end.
Lemma ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1F2 : forall x : ConditionalReconfiguration_r16__attemptCondReconfig_r16__Type, (ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1 x <= 0) /\ ConditionalReconfiguration_r16__attemptCondReconfig_r16__F2 (ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1 x) = x. imp_solve. Qed.
Lemma ConditionalReconfiguration_r16__attemptCondReconfig_r16__F2F1 : forall (y : nat) (H : y <= 0), ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1 (ConditionalReconfiguration_r16__attemptCondReconfig_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CondReconfigToRemoveList_r16.

Opaque CondReconfigToRemoveList_r16__cond CondReconfigToRemoveList_r16__Format.

Require Import NR.CondReconfigToAddModList_r16.

Opaque CondReconfigToAddModList_r16__cond CondReconfigToAddModList_r16__Format.

Record ConditionalReconfiguration_r16__Type : Set :=
  make__ConditionalReconfiguration_r16__Type {
    ConditionalReconfiguration_r16__attemptCondReconfig_r16 : option ConditionalReconfiguration_r16__attemptCondReconfig_r16__Type ;
    ConditionalReconfiguration_r16__condReconfigToRemoveList_r16 : option CondReconfigToRemoveList_r16__Type ;
    ConditionalReconfiguration_r16__condReconfigToAddModList_r16 : option CondReconfigToAddModList_r16__Type ;
}.
Definition ConditionalReconfiguration_r16__root_list : list seq_elem := (
 Opt ConditionalReconfiguration_r16__attemptCondReconfig_r16__Type ConditionalReconfiguration_r16__attemptCondReconfig_r16__cond ::
 Opt CondReconfigToRemoveList_r16__Type CondReconfigToRemoveList_r16__cond ::
 Opt CondReconfigToAddModList_r16__Type CondReconfigToAddModList_r16__cond ::
 nil).
Definition ConditionalReconfiguration_r16__ext_list : list typ := (
  nil).
Definition ConditionalReconfiguration_r16__cond (z : ConditionalReconfiguration_r16__Type) := 
(  opt_cond ConditionalReconfiguration_r16__attemptCondReconfig_r16__cond (ConditionalReconfiguration_r16__attemptCondReconfig_r16 z) /\
  opt_cond CondReconfigToRemoveList_r16__cond (ConditionalReconfiguration_r16__condReconfigToRemoveList_r16 z) /\
  opt_cond CondReconfigToAddModList_r16__cond (ConditionalReconfiguration_r16__condReconfigToAddModList_r16 z) /\
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
Definition ConditionalReconfiguration_r16__attemptCondReconfig_r16__Format : T_Format ConditionalReconfiguration_r16__attemptCondReconfig_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConditionalReconfiguration_r16__attemptCondReconfig_r16__nat__Format ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1 ConditionalReconfiguration_r16__attemptCondReconfig_r16__F2 ConditionalReconfiguration_r16__attemptCondReconfig_r16__F1F2 ConditionalReconfiguration_r16__attemptCondReconfig_r16__F2F1.

Opaque ConditionalReconfiguration_r16__attemptCondReconfig_r16__cond ConditionalReconfiguration_r16__attemptCondReconfig_r16__Format.


Definition ConditionalReconfiguration_r16__root_Format_Type := Eval cbn in seq_format_prod ConditionalReconfiguration_r16__root_list.
Definition ConditionalReconfiguration_r16__root_Format_list : ConditionalReconfiguration_r16__root_Format_Type :=
  (ConditionalReconfiguration_r16__attemptCondReconfig_r16__Format, (CondReconfigToRemoveList_r16__Format, (CondReconfigToAddModList_r16__Format, unit_format))).

Definition ConditionalReconfiguration_r16__ext_Format_Type := Eval cbn in get_formats ConditionalReconfiguration_r16__ext_list.
Definition ConditionalReconfiguration_r16__ext_Format_list : ConditionalReconfiguration_r16__ext_Format_Type :=
  unit__Format.

Definition ConditionalReconfiguration_r16__list_type : Set := (seq_type ConditionalReconfiguration_r16__root_list) * (seq_ext_type ConditionalReconfiguration_r16__ext_list).
Definition ConditionalReconfiguration_r16__list_cond (z : ConditionalReconfiguration_r16__list_type) : Prop :=
        (seq_cond ConditionalReconfiguration_r16__root_list (fst z)) /\ (seq_ext_cond ConditionalReconfiguration_r16__ext_list (snd z)).
Definition ConditionalReconfiguration_r16__list_format : T_Format ConditionalReconfiguration_r16__list_type ConditionalReconfiguration_r16__list_cond :=
 (* Eval compute in *) seq_ext_format ConditionalReconfiguration_r16__root_list ConditionalReconfiguration_r16__root_Format_list ConditionalReconfiguration_r16__ext_list ConditionalReconfiguration_r16__ext_Format_list.

Opaque ConditionalReconfiguration_r16__list_format.
Definition ConditionalReconfiguration_r16__F1 (z : ConditionalReconfiguration_r16__Type) : ConditionalReconfiguration_r16__list_type :=
  (((ConditionalReconfiguration_r16__attemptCondReconfig_r16 z, (ConditionalReconfiguration_r16__condReconfigToRemoveList_r16 z, (ConditionalReconfiguration_r16__condReconfigToAddModList_r16 z, tt)))), (
tt)).
Definition ConditionalReconfiguration_r16__F2 (y : ConditionalReconfiguration_r16__list_type) : ConditionalReconfiguration_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__ConditionalReconfiguration_r16__Type j0 j1 j2
  end.
Definition ConditionalReconfiguration_r16__helper1 : (forall a : ConditionalReconfiguration_r16__Type, ConditionalReconfiguration_r16__cond a -> ConditionalReconfiguration_r16__list_cond (ConditionalReconfiguration_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ConditionalReconfiguration_r16__helper2 : (forall a : ConditionalReconfiguration_r16__Type, ConditionalReconfiguration_r16__F2 (ConditionalReconfiguration_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ConditionalReconfiguration_r16__helper3 : (forall b : ConditionalReconfiguration_r16__list_type, ConditionalReconfiguration_r16__list_cond b -> ConditionalReconfiguration_r16__cond (ConditionalReconfiguration_r16__F2 b) /\ ConditionalReconfiguration_r16__F1 (ConditionalReconfiguration_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ConditionalReconfiguration_r16__cond, ConditionalReconfiguration_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ConditionalReconfiguration_r16__Format : T_Format ConditionalReconfiguration_r16__Type ConditionalReconfiguration_r16__cond :=
 proj2_format ConditionalReconfiguration_r16__cond ConditionalReconfiguration_r16__list_format  ConditionalReconfiguration_r16__F1 ConditionalReconfiguration_r16__F2 ConditionalReconfiguration_r16__helper1 ConditionalReconfiguration_r16__helper2 ConditionalReconfiguration_r16__helper3.

Opaque ConditionalReconfiguration_r16__cond ConditionalReconfiguration_r16__Format.

