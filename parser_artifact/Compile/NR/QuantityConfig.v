Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.QuantityConfigNR.

Opaque QuantityConfigNR__cond QuantityConfigNR__Format.

Definition QuantityConfig__quantityConfigNR_List__Type := list QuantityConfigNR__Type.

Lemma QuantityConfig__quantityConfigNR_List__helper1 : (0 <= 1 <= maxNrofQuantityConfig)%Z. unfold maxNrofQuantityConfig.
 lia. Qed.
Lemma QuantityConfig__quantityConfigNR_List__helper2 : to_bit_sz (Z.to_nat (maxNrofQuantityConfig - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofQuantityConfig - 1))%Z). { apply Zorder.Zle_minus_le_0. apply QuantityConfig__quantityConfigNR_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition QuantityConfig__quantityConfigNR_List__cond (z : QuantityConfig__quantityConfigNR_List__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofQuantityConfig)%Z /\ (list_and QuantityConfigNR__cond z) .

Require Import NR.FilterConfig.

Opaque FilterConfig__cond FilterConfig__Format.

Record QuantityConfig__ext0O__Type : Set :=
  make__QuantityConfig__ext0O__Type {
    QuantityConfig__ext0O__quantityConfigEUTRA : option FilterConfig__Type ;
}.
Definition QuantityConfig__ext0O__list := (
 Opt FilterConfig__Type FilterConfig__cond ::
 nil).
Definition QuantityConfig__ext0O__cond z := 
  opt_cond FilterConfig__cond (QuantityConfig__ext0O__quantityConfigEUTRA z) /\
  True.

Definition QuantityConfig__ext0__Type := QuantityConfig__ext0O__Type.
Definition QuantityConfig__ext0__cond := QuantityConfig__ext0O__cond.

Require Import NR.QuantityConfigUTRA_FDD_r16.

Opaque QuantityConfigUTRA_FDD_r16__cond QuantityConfigUTRA_FDD_r16__Format.

Require Import NR.FilterConfigCLI_r16.

Opaque FilterConfigCLI_r16__cond FilterConfigCLI_r16__Format.

Record QuantityConfig__ext1O__Type : Set :=
  make__QuantityConfig__ext1O__Type {
    QuantityConfig__ext1O__quantityConfigUTRA_FDD_r16 : option QuantityConfigUTRA_FDD_r16__Type ;
    QuantityConfig__ext1O__quantityConfigCLI_r16 : option FilterConfigCLI_r16__Type ;
}.
Definition QuantityConfig__ext1O__list := (
 Opt QuantityConfigUTRA_FDD_r16__Type QuantityConfigUTRA_FDD_r16__cond ::
 Opt FilterConfigCLI_r16__Type FilterConfigCLI_r16__cond ::
 nil).
Definition QuantityConfig__ext1O__cond z := 
  opt_cond QuantityConfigUTRA_FDD_r16__cond (QuantityConfig__ext1O__quantityConfigUTRA_FDD_r16 z) /\
  opt_cond FilterConfigCLI_r16__cond (QuantityConfig__ext1O__quantityConfigCLI_r16 z) /\
  True.

Definition QuantityConfig__ext1__Type := QuantityConfig__ext1O__Type.
Definition QuantityConfig__ext1__cond := QuantityConfig__ext1O__cond.

Record QuantityConfig__Type : Set :=
  make__QuantityConfig__Type {
    QuantityConfig__quantityConfigNR_List : option QuantityConfig__quantityConfigNR_List__Type ;
    QuantityConfig__ext0 : option QuantityConfig__ext0__Type ;
    QuantityConfig__ext1 : option QuantityConfig__ext1__Type ;
}.
Definition QuantityConfig__root_list : list seq_elem := (
 Opt QuantityConfig__quantityConfigNR_List__Type QuantityConfig__quantityConfigNR_List__cond ::
 nil).
Definition QuantityConfig__ext_list : list typ := (
  typ_cons QuantityConfig__ext0__Type QuantityConfig__ext0__cond ::
  typ_cons QuantityConfig__ext1__Type QuantityConfig__ext1__cond ::
  nil).
Definition QuantityConfig__cond (z : QuantityConfig__Type) := 
(  opt_cond QuantityConfig__quantityConfigNR_List__cond (QuantityConfig__quantityConfigNR_List z) /\
  True) /\ 
(  opt_cond QuantityConfig__ext0__cond (QuantityConfig__ext0 z) /\
  opt_cond QuantityConfig__ext1__cond (QuantityConfig__ext1 z) /\
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
Definition QuantityConfig__quantityConfigNR_List__Format : T_Format QuantityConfig__quantityConfigNR_List__Type QuantityConfig__quantityConfigNR_List__cond := seq_of_format QuantityConfigNR__Format 1 maxNrofQuantityConfig QuantityConfig__quantityConfigNR_List__helper1 QuantityConfig__quantityConfigNR_List__helper2.

Opaque QuantityConfig__quantityConfigNR_List__cond QuantityConfig__quantityConfigNR_List__Format.


Definition QuantityConfig__ext0O__Format_Type := Eval cbn in seq_format_prod QuantityConfig__ext0O__list.
Definition QuantityConfig__ext0O__Format_list : QuantityConfig__ext0O__Format_Type :=
  (FilterConfig__Format, unit_format).
Definition QuantityConfig__ext0O__list__Format := (*Eval compute in *) seq_format QuantityConfig__ext0O__list QuantityConfig__ext0O__Format_list.
Definition QuantityConfig__ext0O__F1 z :=
  (QuantityConfig__ext0O__quantityConfigEUTRA z, tt).
Definition QuantityConfig__ext0O__F2 (y : seq_type QuantityConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__QuantityConfig__ext0O__Type i0
  end.
Lemma QuantityConfig__ext0O__F1F2_cond (z : QuantityConfig__ext0O__Type)
  : QuantityConfig__ext0O__cond z ->
  (seq_cond QuantityConfig__ext0O__list (QuantityConfig__ext0O__F1 z)).
intro H. unfold QuantityConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma QuantityConfig__ext0O__F1F2_cond2 (z : QuantityConfig__ext0O__Type)
 : QuantityConfig__ext0O__F2 (QuantityConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma QuantityConfig__ext0O__F2F1_cond (y : seq_type QuantityConfig__ext0O__list)
  : seq_cond QuantityConfig__ext0O__list y ->
 (QuantityConfig__ext0O__cond (QuantityConfig__ext0O__F2 y)) /\  QuantityConfig__ext0O__F1 (QuantityConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold QuantityConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold QuantityConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition QuantityConfig__ext0O__Format : T_Format QuantityConfig__ext0O__Type QuantityConfig__ext0O__cond :=
        proj2_format  QuantityConfig__ext0O__cond QuantityConfig__ext0O__list__Format
    QuantityConfig__ext0O__F1 QuantityConfig__ext0O__F2 QuantityConfig__ext0O__F1F2_cond  QuantityConfig__ext0O__F1F2_cond2 QuantityConfig__ext0O__F2F1_cond.
Opaque QuantityConfig__ext0O__cond QuantityConfig__ext0O__Format.

Definition QuantityConfig__ext0__check_all_none (b : QuantityConfig__ext0O__Type) : bool :=
match b with 
  | make__QuantityConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition QuantityConfig__ext0__Format : T_Format QuantityConfig__ext0__Type QuantityConfig__ext0__cond :=
  restrict_add_format QuantityConfig__ext0__check_all_none QuantityConfig__ext0O__Format.

Opaque QuantityConfig__ext0__cond QuantityConfig__ext0__Format.


Definition QuantityConfig__ext1O__Format_Type := Eval cbn in seq_format_prod QuantityConfig__ext1O__list.
Definition QuantityConfig__ext1O__Format_list : QuantityConfig__ext1O__Format_Type :=
  (QuantityConfigUTRA_FDD_r16__Format, (FilterConfigCLI_r16__Format, unit_format)).
Definition QuantityConfig__ext1O__list__Format := (*Eval compute in *) seq_format QuantityConfig__ext1O__list QuantityConfig__ext1O__Format_list.
Definition QuantityConfig__ext1O__F1 z :=
  (QuantityConfig__ext1O__quantityConfigUTRA_FDD_r16 z, (QuantityConfig__ext1O__quantityConfigCLI_r16 z, tt)).
Definition QuantityConfig__ext1O__F2 (y : seq_type QuantityConfig__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__QuantityConfig__ext1O__Type i0 i1
  end.
Lemma QuantityConfig__ext1O__F1F2_cond (z : QuantityConfig__ext1O__Type)
  : QuantityConfig__ext1O__cond z ->
  (seq_cond QuantityConfig__ext1O__list (QuantityConfig__ext1O__F1 z)).
intro H. unfold QuantityConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma QuantityConfig__ext1O__F1F2_cond2 (z : QuantityConfig__ext1O__Type)
 : QuantityConfig__ext1O__F2 (QuantityConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma QuantityConfig__ext1O__F2F1_cond (y : seq_type QuantityConfig__ext1O__list)
  : seq_cond QuantityConfig__ext1O__list y ->
 (QuantityConfig__ext1O__cond (QuantityConfig__ext1O__F2 y)) /\  QuantityConfig__ext1O__F1 (QuantityConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold QuantityConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold QuantityConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition QuantityConfig__ext1O__Format : T_Format QuantityConfig__ext1O__Type QuantityConfig__ext1O__cond :=
        proj2_format  QuantityConfig__ext1O__cond QuantityConfig__ext1O__list__Format
    QuantityConfig__ext1O__F1 QuantityConfig__ext1O__F2 QuantityConfig__ext1O__F1F2_cond  QuantityConfig__ext1O__F1F2_cond2 QuantityConfig__ext1O__F2F1_cond.
Opaque QuantityConfig__ext1O__cond QuantityConfig__ext1O__Format.

Definition QuantityConfig__ext1__check_all_none (b : QuantityConfig__ext1O__Type) : bool :=
match b with 
  | make__QuantityConfig__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition QuantityConfig__ext1__Format : T_Format QuantityConfig__ext1__Type QuantityConfig__ext1__cond :=
  restrict_add_format QuantityConfig__ext1__check_all_none QuantityConfig__ext1O__Format.

Opaque QuantityConfig__ext1__cond QuantityConfig__ext1__Format.


Definition QuantityConfig__root_Format_Type := Eval cbn in seq_format_prod QuantityConfig__root_list.
Definition QuantityConfig__root_Format_list : QuantityConfig__root_Format_Type :=
  (QuantityConfig__quantityConfigNR_List__Format, unit_format).

Definition QuantityConfig__ext_Format_Type := Eval cbn in get_formats QuantityConfig__ext_list.
Definition QuantityConfig__ext_Format_list : QuantityConfig__ext_Format_Type :=
  (QuantityConfig__ext0__Format, (QuantityConfig__ext1__Format, unit__Format)).

Definition QuantityConfig__list_type : Set := (seq_type QuantityConfig__root_list) * (seq_ext_type QuantityConfig__ext_list).
Definition QuantityConfig__list_cond (z : QuantityConfig__list_type) : Prop :=
        (seq_cond QuantityConfig__root_list (fst z)) /\ (seq_ext_cond QuantityConfig__ext_list (snd z)).
Definition QuantityConfig__list_format : T_Format QuantityConfig__list_type QuantityConfig__list_cond :=
 (* Eval compute in *) seq_ext_format QuantityConfig__root_list QuantityConfig__root_Format_list QuantityConfig__ext_list QuantityConfig__ext_Format_list.

Opaque QuantityConfig__list_format.
Definition QuantityConfig__F1 (z : QuantityConfig__Type) : QuantityConfig__list_type :=
  (((QuantityConfig__quantityConfigNR_List z, tt)), (
(QuantityConfig__ext0 z, (QuantityConfig__ext1 z, tt)))).
Definition QuantityConfig__F2 (y : QuantityConfig__list_type) : QuantityConfig__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__QuantityConfig__Type j0 i0 i1
  end.
Definition QuantityConfig__helper1 : (forall a : QuantityConfig__Type, QuantityConfig__cond a -> QuantityConfig__list_cond (QuantityConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition QuantityConfig__helper2 : (forall a : QuantityConfig__Type, QuantityConfig__F2 (QuantityConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition QuantityConfig__helper3 : (forall b : QuantityConfig__list_type, QuantityConfig__list_cond b -> QuantityConfig__cond (QuantityConfig__F2 b) /\ QuantityConfig__F1 (QuantityConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold QuantityConfig__cond, QuantityConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition QuantityConfig__Format : T_Format QuantityConfig__Type QuantityConfig__cond :=
 proj2_format QuantityConfig__cond QuantityConfig__list_format  QuantityConfig__F1 QuantityConfig__F2 QuantityConfig__helper1 QuantityConfig__helper2 QuantityConfig__helper3.

Opaque QuantityConfig__cond QuantityConfig__Format.

