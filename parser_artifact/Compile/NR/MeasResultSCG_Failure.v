Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasResultList2NR.

Opaque MeasResultList2NR__cond MeasResultList2NR__Format.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Record MeasResultSCG_Failure__ext0O__Type : Set :=
  make__MeasResultSCG_Failure__ext0O__Type {
    MeasResultSCG_Failure__ext0O__locationInfo_r16 : option LocationInfo_r16__Type ;
}.
Definition MeasResultSCG_Failure__ext0O__list := (
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 nil).
Definition MeasResultSCG_Failure__ext0O__cond z := 
  opt_cond LocationInfo_r16__cond (MeasResultSCG_Failure__ext0O__locationInfo_r16 z) /\
  True.

Definition MeasResultSCG_Failure__ext0__Type := MeasResultSCG_Failure__ext0O__Type.
Definition MeasResultSCG_Failure__ext0__cond := MeasResultSCG_Failure__ext0O__cond.

Record MeasResultSCG_Failure__Type : Set :=
  make__MeasResultSCG_Failure__Type {
    MeasResultSCG_Failure__measResultPerMOList : MeasResultList2NR__Type ;
    MeasResultSCG_Failure__ext0 : option MeasResultSCG_Failure__ext0__Type ;
}.
Definition MeasResultSCG_Failure__root_list : list seq_elem := (
 Nor MeasResultList2NR__Type MeasResultList2NR__cond ::
 nil).
Definition MeasResultSCG_Failure__ext_list : list typ := (
  typ_cons MeasResultSCG_Failure__ext0__Type MeasResultSCG_Failure__ext0__cond ::
  nil).
Definition MeasResultSCG_Failure__cond (z : MeasResultSCG_Failure__Type) := 
(  MeasResultList2NR__cond (MeasResultSCG_Failure__measResultPerMOList z) /\
  True) /\ 
(  opt_cond MeasResultSCG_Failure__ext0__cond (MeasResultSCG_Failure__ext0 z) /\
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

Definition MeasResultSCG_Failure__ext0O__Format_Type := Eval cbn in seq_format_prod MeasResultSCG_Failure__ext0O__list.
Definition MeasResultSCG_Failure__ext0O__Format_list : MeasResultSCG_Failure__ext0O__Format_Type :=
  (LocationInfo_r16__Format, unit_format).
Definition MeasResultSCG_Failure__ext0O__list__Format := (*Eval compute in *) seq_format MeasResultSCG_Failure__ext0O__list MeasResultSCG_Failure__ext0O__Format_list.
Definition MeasResultSCG_Failure__ext0O__F1 z :=
  (MeasResultSCG_Failure__ext0O__locationInfo_r16 z, tt).
Definition MeasResultSCG_Failure__ext0O__F2 (y : seq_type MeasResultSCG_Failure__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MeasResultSCG_Failure__ext0O__Type i0
  end.
Lemma MeasResultSCG_Failure__ext0O__F1F2_cond (z : MeasResultSCG_Failure__ext0O__Type)
  : MeasResultSCG_Failure__ext0O__cond z ->
  (seq_cond MeasResultSCG_Failure__ext0O__list (MeasResultSCG_Failure__ext0O__F1 z)).
intro H. unfold MeasResultSCG_Failure__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasResultSCG_Failure__ext0O__F1F2_cond2 (z : MeasResultSCG_Failure__ext0O__Type)
 : MeasResultSCG_Failure__ext0O__F2 (MeasResultSCG_Failure__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultSCG_Failure__ext0O__F2F1_cond (y : seq_type MeasResultSCG_Failure__ext0O__list)
  : seq_cond MeasResultSCG_Failure__ext0O__list y ->
 (MeasResultSCG_Failure__ext0O__cond (MeasResultSCG_Failure__ext0O__F2 y)) /\  MeasResultSCG_Failure__ext0O__F1 (MeasResultSCG_Failure__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultSCG_Failure__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasResultSCG_Failure__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultSCG_Failure__ext0O__Format : T_Format MeasResultSCG_Failure__ext0O__Type MeasResultSCG_Failure__ext0O__cond :=
        proj2_format  MeasResultSCG_Failure__ext0O__cond MeasResultSCG_Failure__ext0O__list__Format
    MeasResultSCG_Failure__ext0O__F1 MeasResultSCG_Failure__ext0O__F2 MeasResultSCG_Failure__ext0O__F1F2_cond  MeasResultSCG_Failure__ext0O__F1F2_cond2 MeasResultSCG_Failure__ext0O__F2F1_cond.
Opaque MeasResultSCG_Failure__ext0O__cond MeasResultSCG_Failure__ext0O__Format.

Definition MeasResultSCG_Failure__ext0__check_all_none (b : MeasResultSCG_Failure__ext0O__Type) : bool :=
match b with 
  | make__MeasResultSCG_Failure__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MeasResultSCG_Failure__ext0__Format : T_Format MeasResultSCG_Failure__ext0__Type MeasResultSCG_Failure__ext0__cond :=
  restrict_add_format MeasResultSCG_Failure__ext0__check_all_none MeasResultSCG_Failure__ext0O__Format.

Opaque MeasResultSCG_Failure__ext0__cond MeasResultSCG_Failure__ext0__Format.


Definition MeasResultSCG_Failure__root_Format_Type := Eval cbn in seq_format_prod MeasResultSCG_Failure__root_list.
Definition MeasResultSCG_Failure__root_Format_list : MeasResultSCG_Failure__root_Format_Type :=
  (MeasResultList2NR__Format, unit_format).

Definition MeasResultSCG_Failure__ext_Format_Type := Eval cbn in get_formats MeasResultSCG_Failure__ext_list.
Definition MeasResultSCG_Failure__ext_Format_list : MeasResultSCG_Failure__ext_Format_Type :=
  (MeasResultSCG_Failure__ext0__Format, unit__Format).

Definition MeasResultSCG_Failure__list_type : Set := (seq_type MeasResultSCG_Failure__root_list) * (seq_ext_type MeasResultSCG_Failure__ext_list).
Definition MeasResultSCG_Failure__list_cond (z : MeasResultSCG_Failure__list_type) : Prop :=
        (seq_cond MeasResultSCG_Failure__root_list (fst z)) /\ (seq_ext_cond MeasResultSCG_Failure__ext_list (snd z)).
Definition MeasResultSCG_Failure__list_format : T_Format MeasResultSCG_Failure__list_type MeasResultSCG_Failure__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultSCG_Failure__root_list MeasResultSCG_Failure__root_Format_list MeasResultSCG_Failure__ext_list MeasResultSCG_Failure__ext_Format_list.

Opaque MeasResultSCG_Failure__list_format.
Definition MeasResultSCG_Failure__F1 (z : MeasResultSCG_Failure__Type) : MeasResultSCG_Failure__list_type :=
  (((MeasResultSCG_Failure__measResultPerMOList z, tt)), (
(MeasResultSCG_Failure__ext0 z, tt))).
Definition MeasResultSCG_Failure__F2 (y : MeasResultSCG_Failure__list_type) : MeasResultSCG_Failure__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__MeasResultSCG_Failure__Type j0 i0
  end.
Definition MeasResultSCG_Failure__helper1 : (forall a : MeasResultSCG_Failure__Type, MeasResultSCG_Failure__cond a -> MeasResultSCG_Failure__list_cond (MeasResultSCG_Failure__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultSCG_Failure__helper2 : (forall a : MeasResultSCG_Failure__Type, MeasResultSCG_Failure__F2 (MeasResultSCG_Failure__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultSCG_Failure__helper3 : (forall b : MeasResultSCG_Failure__list_type, MeasResultSCG_Failure__list_cond b -> MeasResultSCG_Failure__cond (MeasResultSCG_Failure__F2 b) /\ MeasResultSCG_Failure__F1 (MeasResultSCG_Failure__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultSCG_Failure__cond, MeasResultSCG_Failure__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultSCG_Failure__Format : T_Format MeasResultSCG_Failure__Type MeasResultSCG_Failure__cond :=
 proj2_format MeasResultSCG_Failure__cond MeasResultSCG_Failure__list_format  MeasResultSCG_Failure__F1 MeasResultSCG_Failure__F2 MeasResultSCG_Failure__helper1 MeasResultSCG_Failure__helper2 MeasResultSCG_Failure__helper3.

Opaque MeasResultSCG_Failure__cond MeasResultSCG_Failure__Format.

