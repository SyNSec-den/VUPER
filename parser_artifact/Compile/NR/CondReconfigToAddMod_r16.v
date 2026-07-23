Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CondReconfigId_r16.

Opaque CondReconfigId_r16__cond CondReconfigId_r16__Format.

Require Import NR.MeasId.

Opaque MeasId__cond MeasId__Format.

Definition CondReconfigToAddMod_r16__condExecutionCond_r16__Type := list MeasId__Type.

Lemma CondReconfigToAddMod_r16__condExecutionCond_r16__helper1 : (0 <= 1 <= 2)%Z.  lia. Qed.
Lemma CondReconfigToAddMod_r16__condExecutionCond_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CondReconfigToAddMod_r16__condExecutionCond_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CondReconfigToAddMod_r16__condExecutionCond_r16__cond (z : CondReconfigToAddMod_r16__condExecutionCond_r16__Type) :=  (1 <= Z.of_nat (length z) <= 2)%Z /\ (list_and MeasId__cond z) .

Record CondReconfigToAddMod_r16__ext0O__Type : Set :=
  make__CondReconfigToAddMod_r16__ext0O__Type {
    CondReconfigToAddMod_r16__ext0O__condExecutionCondSCG_r17 : option octet_string ;
}.
Definition CondReconfigToAddMod_r16__ext0O__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CondReconfigToAddMod_r16__ext0O__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CondReconfigToAddMod_r16__ext0O__condExecutionCondSCG_r17 z) /\
  True.

Definition CondReconfigToAddMod_r16__ext0__Type := CondReconfigToAddMod_r16__ext0O__Type.
Definition CondReconfigToAddMod_r16__ext0__cond := CondReconfigToAddMod_r16__ext0O__cond.

Record CondReconfigToAddMod_r16__Type : Set :=
  make__CondReconfigToAddMod_r16__Type {
    CondReconfigToAddMod_r16__condReconfigId_r16 : CondReconfigId_r16__Type ;
    CondReconfigToAddMod_r16__condExecutionCond_r16 : option CondReconfigToAddMod_r16__condExecutionCond_r16__Type ;
    CondReconfigToAddMod_r16__condRRCReconfig_r16 : option octet_string ;
    CondReconfigToAddMod_r16__ext0 : option CondReconfigToAddMod_r16__ext0__Type ;
}.
Definition CondReconfigToAddMod_r16__root_list : list seq_elem := (
 Nor CondReconfigId_r16__Type CondReconfigId_r16__cond ::
 Opt CondReconfigToAddMod_r16__condExecutionCond_r16__Type CondReconfigToAddMod_r16__condExecutionCond_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CondReconfigToAddMod_r16__ext_list : list typ := (
  typ_cons CondReconfigToAddMod_r16__ext0__Type CondReconfigToAddMod_r16__ext0__cond ::
  nil).
Definition CondReconfigToAddMod_r16__cond (z : CondReconfigToAddMod_r16__Type) := 
(  CondReconfigId_r16__cond (CondReconfigToAddMod_r16__condReconfigId_r16 z) /\
  opt_cond CondReconfigToAddMod_r16__condExecutionCond_r16__cond (CondReconfigToAddMod_r16__condExecutionCond_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CondReconfigToAddMod_r16__condRRCReconfig_r16 z) /\
  True) /\ 
(  opt_cond CondReconfigToAddMod_r16__ext0__cond (CondReconfigToAddMod_r16__ext0 z) /\
  True).


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
Definition CondReconfigToAddMod_r16__condExecutionCond_r16__Format : T_Format CondReconfigToAddMod_r16__condExecutionCond_r16__Type CondReconfigToAddMod_r16__condExecutionCond_r16__cond := seq_of_format MeasId__Format 1 2 CondReconfigToAddMod_r16__condExecutionCond_r16__helper1 CondReconfigToAddMod_r16__condExecutionCond_r16__helper2.

Opaque CondReconfigToAddMod_r16__condExecutionCond_r16__cond CondReconfigToAddMod_r16__condExecutionCond_r16__Format.


Definition CondReconfigToAddMod_r16__ext0O__Format_Type := Eval cbn in seq_format_prod CondReconfigToAddMod_r16__ext0O__list.
Definition CondReconfigToAddMod_r16__ext0O__Format_list : CondReconfigToAddMod_r16__ext0O__Format_Type :=
  (octet_string_nc__Format, unit_format).
Definition CondReconfigToAddMod_r16__ext0O__list__Format := (*Eval compute in *) seq_format CondReconfigToAddMod_r16__ext0O__list CondReconfigToAddMod_r16__ext0O__Format_list.
Definition CondReconfigToAddMod_r16__ext0O__F1 z :=
  (CondReconfigToAddMod_r16__ext0O__condExecutionCondSCG_r17 z, tt).
Definition CondReconfigToAddMod_r16__ext0O__F2 (y : seq_type CondReconfigToAddMod_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CondReconfigToAddMod_r16__ext0O__Type i0
  end.
Lemma CondReconfigToAddMod_r16__ext0O__F1F2_cond (z : CondReconfigToAddMod_r16__ext0O__Type)
  : CondReconfigToAddMod_r16__ext0O__cond z ->
  (seq_cond CondReconfigToAddMod_r16__ext0O__list (CondReconfigToAddMod_r16__ext0O__F1 z)).
intro H. unfold CondReconfigToAddMod_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma CondReconfigToAddMod_r16__ext0O__F1F2_cond2 (z : CondReconfigToAddMod_r16__ext0O__Type)
 : CondReconfigToAddMod_r16__ext0O__F2 (CondReconfigToAddMod_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CondReconfigToAddMod_r16__ext0O__F2F1_cond (y : seq_type CondReconfigToAddMod_r16__ext0O__list)
  : seq_cond CondReconfigToAddMod_r16__ext0O__list y ->
 (CondReconfigToAddMod_r16__ext0O__cond (CondReconfigToAddMod_r16__ext0O__F2 y)) /\  CondReconfigToAddMod_r16__ext0O__F1 (CondReconfigToAddMod_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CondReconfigToAddMod_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold CondReconfigToAddMod_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CondReconfigToAddMod_r16__ext0O__Format : T_Format CondReconfigToAddMod_r16__ext0O__Type CondReconfigToAddMod_r16__ext0O__cond :=
        proj2_format  CondReconfigToAddMod_r16__ext0O__cond CondReconfigToAddMod_r16__ext0O__list__Format
    CondReconfigToAddMod_r16__ext0O__F1 CondReconfigToAddMod_r16__ext0O__F2 CondReconfigToAddMod_r16__ext0O__F1F2_cond  CondReconfigToAddMod_r16__ext0O__F1F2_cond2 CondReconfigToAddMod_r16__ext0O__F2F1_cond.
Opaque CondReconfigToAddMod_r16__ext0O__cond CondReconfigToAddMod_r16__ext0O__Format.

Definition CondReconfigToAddMod_r16__ext0__check_all_none (b : CondReconfigToAddMod_r16__ext0O__Type) : bool :=
match b with 
  | make__CondReconfigToAddMod_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CondReconfigToAddMod_r16__ext0__Format : T_Format CondReconfigToAddMod_r16__ext0__Type CondReconfigToAddMod_r16__ext0__cond :=
  restrict_add_format CondReconfigToAddMod_r16__ext0__check_all_none CondReconfigToAddMod_r16__ext0O__Format.

Opaque CondReconfigToAddMod_r16__ext0__cond CondReconfigToAddMod_r16__ext0__Format.


Definition CondReconfigToAddMod_r16__root_Format_Type := Eval cbn in seq_format_prod CondReconfigToAddMod_r16__root_list.
Definition CondReconfigToAddMod_r16__root_Format_list : CondReconfigToAddMod_r16__root_Format_Type :=
  (CondReconfigId_r16__Format, (CondReconfigToAddMod_r16__condExecutionCond_r16__Format, (octet_string_nc__Format, unit_format))).

Definition CondReconfigToAddMod_r16__ext_Format_Type := Eval cbn in get_formats CondReconfigToAddMod_r16__ext_list.
Definition CondReconfigToAddMod_r16__ext_Format_list : CondReconfigToAddMod_r16__ext_Format_Type :=
  (CondReconfigToAddMod_r16__ext0__Format, unit__Format).

Definition CondReconfigToAddMod_r16__list_type : Set := (seq_type CondReconfigToAddMod_r16__root_list) * (seq_ext_type CondReconfigToAddMod_r16__ext_list).
Definition CondReconfigToAddMod_r16__list_cond (z : CondReconfigToAddMod_r16__list_type) : Prop :=
        (seq_cond CondReconfigToAddMod_r16__root_list (fst z)) /\ (seq_ext_cond CondReconfigToAddMod_r16__ext_list (snd z)).
Definition CondReconfigToAddMod_r16__list_format : T_Format CondReconfigToAddMod_r16__list_type CondReconfigToAddMod_r16__list_cond :=
 (* Eval compute in *) seq_ext_format CondReconfigToAddMod_r16__root_list CondReconfigToAddMod_r16__root_Format_list CondReconfigToAddMod_r16__ext_list CondReconfigToAddMod_r16__ext_Format_list.

Opaque CondReconfigToAddMod_r16__list_format.
Definition CondReconfigToAddMod_r16__F1 (z : CondReconfigToAddMod_r16__Type) : CondReconfigToAddMod_r16__list_type :=
  (((CondReconfigToAddMod_r16__condReconfigId_r16 z, (CondReconfigToAddMod_r16__condExecutionCond_r16 z, (CondReconfigToAddMod_r16__condRRCReconfig_r16 z, tt)))), (
(CondReconfigToAddMod_r16__ext0 z, tt))).
Definition CondReconfigToAddMod_r16__F2 (y : CondReconfigToAddMod_r16__list_type) : CondReconfigToAddMod_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__CondReconfigToAddMod_r16__Type j0 j1 j2 i0
  end.
Definition CondReconfigToAddMod_r16__helper1 : (forall a : CondReconfigToAddMod_r16__Type, CondReconfigToAddMod_r16__cond a -> CondReconfigToAddMod_r16__list_cond (CondReconfigToAddMod_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CondReconfigToAddMod_r16__helper2 : (forall a : CondReconfigToAddMod_r16__Type, CondReconfigToAddMod_r16__F2 (CondReconfigToAddMod_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CondReconfigToAddMod_r16__helper3 : (forall b : CondReconfigToAddMod_r16__list_type, CondReconfigToAddMod_r16__list_cond b -> CondReconfigToAddMod_r16__cond (CondReconfigToAddMod_r16__F2 b) /\ CondReconfigToAddMod_r16__F1 (CondReconfigToAddMod_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CondReconfigToAddMod_r16__cond, CondReconfigToAddMod_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CondReconfigToAddMod_r16__Format : T_Format CondReconfigToAddMod_r16__Type CondReconfigToAddMod_r16__cond :=
 proj2_format CondReconfigToAddMod_r16__cond CondReconfigToAddMod_r16__list_format  CondReconfigToAddMod_r16__F1 CondReconfigToAddMod_r16__F2 CondReconfigToAddMod_r16__helper1 CondReconfigToAddMod_r16__helper2 CondReconfigToAddMod_r16__helper3.

Opaque CondReconfigToAddMod_r16__cond CondReconfigToAddMod_r16__Format.

