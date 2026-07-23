Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_Parameters.

Opaque EUTRA_Parameters__cond EUTRA_Parameters__Format.

Require Import NR.UTRA_FDD_Parameters_r16.

Opaque UTRA_FDD_Parameters_r16__cond UTRA_FDD_Parameters_r16__Format.

Record InterRAT_Parameters__ext0O__Type : Set :=
  make__InterRAT_Parameters__ext0O__Type {
    InterRAT_Parameters__ext0O__utra_FDD_r16 : option UTRA_FDD_Parameters_r16__Type ;
}.
Definition InterRAT_Parameters__ext0O__list := (
 Opt UTRA_FDD_Parameters_r16__Type UTRA_FDD_Parameters_r16__cond ::
 nil).
Definition InterRAT_Parameters__ext0O__cond z := 
  opt_cond UTRA_FDD_Parameters_r16__cond (InterRAT_Parameters__ext0O__utra_FDD_r16 z) /\
  True.

Definition InterRAT_Parameters__ext0__Type := InterRAT_Parameters__ext0O__Type.
Definition InterRAT_Parameters__ext0__cond := InterRAT_Parameters__ext0O__cond.

Record InterRAT_Parameters__Type : Set :=
  make__InterRAT_Parameters__Type {
    InterRAT_Parameters__eutra : option EUTRA_Parameters__Type ;
    InterRAT_Parameters__ext0 : option InterRAT_Parameters__ext0__Type ;
}.
Definition InterRAT_Parameters__root_list : list seq_elem := (
 Opt EUTRA_Parameters__Type EUTRA_Parameters__cond ::
 nil).
Definition InterRAT_Parameters__ext_list : list typ := (
  typ_cons InterRAT_Parameters__ext0__Type InterRAT_Parameters__ext0__cond ::
  nil).
Definition InterRAT_Parameters__cond (z : InterRAT_Parameters__Type) := 
(  opt_cond EUTRA_Parameters__cond (InterRAT_Parameters__eutra z) /\
  True) /\ 
(  opt_cond InterRAT_Parameters__ext0__cond (InterRAT_Parameters__ext0 z) /\
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

Definition InterRAT_Parameters__ext0O__Format_Type := Eval cbn in seq_format_prod InterRAT_Parameters__ext0O__list.
Definition InterRAT_Parameters__ext0O__Format_list : InterRAT_Parameters__ext0O__Format_Type :=
  (UTRA_FDD_Parameters_r16__Format, unit_format).
Definition InterRAT_Parameters__ext0O__list__Format := (*Eval compute in *) seq_format InterRAT_Parameters__ext0O__list InterRAT_Parameters__ext0O__Format_list.
Definition InterRAT_Parameters__ext0O__F1 z :=
  (InterRAT_Parameters__ext0O__utra_FDD_r16 z, tt).
Definition InterRAT_Parameters__ext0O__F2 (y : seq_type InterRAT_Parameters__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__InterRAT_Parameters__ext0O__Type i0
  end.
Lemma InterRAT_Parameters__ext0O__F1F2_cond (z : InterRAT_Parameters__ext0O__Type)
  : InterRAT_Parameters__ext0O__cond z ->
  (seq_cond InterRAT_Parameters__ext0O__list (InterRAT_Parameters__ext0O__F1 z)).
intro H. unfold InterRAT_Parameters__ext0O__cond in H. simpl. auto. Qed.
Lemma InterRAT_Parameters__ext0O__F1F2_cond2 (z : InterRAT_Parameters__ext0O__Type)
 : InterRAT_Parameters__ext0O__F2 (InterRAT_Parameters__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma InterRAT_Parameters__ext0O__F2F1_cond (y : seq_type InterRAT_Parameters__ext0O__list)
  : seq_cond InterRAT_Parameters__ext0O__list y ->
 (InterRAT_Parameters__ext0O__cond (InterRAT_Parameters__ext0O__F2 y)) /\  InterRAT_Parameters__ext0O__F1 (InterRAT_Parameters__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold InterRAT_Parameters__ext0O__cond. simpl in *. auto.
 - simpl. unfold InterRAT_Parameters__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition InterRAT_Parameters__ext0O__Format : T_Format InterRAT_Parameters__ext0O__Type InterRAT_Parameters__ext0O__cond :=
        proj2_format  InterRAT_Parameters__ext0O__cond InterRAT_Parameters__ext0O__list__Format
    InterRAT_Parameters__ext0O__F1 InterRAT_Parameters__ext0O__F2 InterRAT_Parameters__ext0O__F1F2_cond  InterRAT_Parameters__ext0O__F1F2_cond2 InterRAT_Parameters__ext0O__F2F1_cond.
Opaque InterRAT_Parameters__ext0O__cond InterRAT_Parameters__ext0O__Format.

Definition InterRAT_Parameters__ext0__check_all_none (b : InterRAT_Parameters__ext0O__Type) : bool :=
match b with 
  | make__InterRAT_Parameters__ext0O__Type None  => false 
  | _ => true 
 end.
Definition InterRAT_Parameters__ext0__Format : T_Format InterRAT_Parameters__ext0__Type InterRAT_Parameters__ext0__cond :=
  restrict_add_format InterRAT_Parameters__ext0__check_all_none InterRAT_Parameters__ext0O__Format.

Opaque InterRAT_Parameters__ext0__cond InterRAT_Parameters__ext0__Format.


Definition InterRAT_Parameters__root_Format_Type := Eval cbn in seq_format_prod InterRAT_Parameters__root_list.
Definition InterRAT_Parameters__root_Format_list : InterRAT_Parameters__root_Format_Type :=
  (EUTRA_Parameters__Format, unit_format).

Definition InterRAT_Parameters__ext_Format_Type := Eval cbn in get_formats InterRAT_Parameters__ext_list.
Definition InterRAT_Parameters__ext_Format_list : InterRAT_Parameters__ext_Format_Type :=
  (InterRAT_Parameters__ext0__Format, unit__Format).

Definition InterRAT_Parameters__list_type : Set := (seq_type InterRAT_Parameters__root_list) * (seq_ext_type InterRAT_Parameters__ext_list).
Definition InterRAT_Parameters__list_cond (z : InterRAT_Parameters__list_type) : Prop :=
        (seq_cond InterRAT_Parameters__root_list (fst z)) /\ (seq_ext_cond InterRAT_Parameters__ext_list (snd z)).
Definition InterRAT_Parameters__list_format : T_Format InterRAT_Parameters__list_type InterRAT_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format InterRAT_Parameters__root_list InterRAT_Parameters__root_Format_list InterRAT_Parameters__ext_list InterRAT_Parameters__ext_Format_list.

Opaque InterRAT_Parameters__list_format.
Definition InterRAT_Parameters__F1 (z : InterRAT_Parameters__Type) : InterRAT_Parameters__list_type :=
  (((InterRAT_Parameters__eutra z, tt)), (
(InterRAT_Parameters__ext0 z, tt))).
Definition InterRAT_Parameters__F2 (y : InterRAT_Parameters__list_type) : InterRAT_Parameters__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__InterRAT_Parameters__Type j0 i0
  end.
Definition InterRAT_Parameters__helper1 : (forall a : InterRAT_Parameters__Type, InterRAT_Parameters__cond a -> InterRAT_Parameters__list_cond (InterRAT_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition InterRAT_Parameters__helper2 : (forall a : InterRAT_Parameters__Type, InterRAT_Parameters__F2 (InterRAT_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition InterRAT_Parameters__helper3 : (forall b : InterRAT_Parameters__list_type, InterRAT_Parameters__list_cond b -> InterRAT_Parameters__cond (InterRAT_Parameters__F2 b) /\ InterRAT_Parameters__F1 (InterRAT_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold InterRAT_Parameters__cond, InterRAT_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition InterRAT_Parameters__Format : T_Format InterRAT_Parameters__Type InterRAT_Parameters__cond :=
 proj2_format InterRAT_Parameters__cond InterRAT_Parameters__list_format  InterRAT_Parameters__F1 InterRAT_Parameters__F2 InterRAT_Parameters__helper1 InterRAT_Parameters__helper2 InterRAT_Parameters__helper3.

Opaque InterRAT_Parameters__cond InterRAT_Parameters__Format.

