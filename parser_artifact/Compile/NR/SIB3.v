Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.IntraFreqNeighCellList.

Opaque IntraFreqNeighCellList__cond IntraFreqNeighCellList__Format.

Require Import NR.IntraFreqExcludedCellList.

Opaque IntraFreqExcludedCellList__cond IntraFreqExcludedCellList__Format.

Require Import NR.IntraFreqNeighCellList_v1610.

Opaque IntraFreqNeighCellList_v1610__cond IntraFreqNeighCellList_v1610__Format.

Require Import NR.IntraFreqAllowedCellList_r16.

Opaque IntraFreqAllowedCellList_r16__cond IntraFreqAllowedCellList_r16__Format.

Require Import NR.IntraFreqCAG_CellListPerPLMN_r16.

Opaque IntraFreqCAG_CellListPerPLMN_r16__cond IntraFreqCAG_CellListPerPLMN_r16__Format.

Definition SIB3__ext0O__intraFreqCAG_CellList_r16__Type := list IntraFreqCAG_CellListPerPLMN_r16__Type.

Lemma SIB3__ext0O__intraFreqCAG_CellList_r16__helper1 : (0 <= 1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma SIB3__ext0O__intraFreqCAG_CellList_r16__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SIB3__ext0O__intraFreqCAG_CellList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB3__ext0O__intraFreqCAG_CellList_r16__cond (z : SIB3__ext0O__intraFreqCAG_CellList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and IntraFreqCAG_CellListPerPLMN_r16__cond z) .

Record SIB3__ext0O__Type : Set :=
  make__SIB3__ext0O__Type {
    SIB3__ext0O__intraFreqNeighCellList_v1610 : option IntraFreqNeighCellList_v1610__Type ;
    SIB3__ext0O__intraFreqAllowedCellList_r16 : option IntraFreqAllowedCellList_r16__Type ;
    SIB3__ext0O__intraFreqCAG_CellList_r16 : option SIB3__ext0O__intraFreqCAG_CellList_r16__Type ;
}.
Definition SIB3__ext0O__list := (
 Opt IntraFreqNeighCellList_v1610__Type IntraFreqNeighCellList_v1610__cond ::
 Opt IntraFreqAllowedCellList_r16__Type IntraFreqAllowedCellList_r16__cond ::
 Opt SIB3__ext0O__intraFreqCAG_CellList_r16__Type SIB3__ext0O__intraFreqCAG_CellList_r16__cond ::
 nil).
Definition SIB3__ext0O__cond z := 
  opt_cond IntraFreqNeighCellList_v1610__cond (SIB3__ext0O__intraFreqNeighCellList_v1610 z) /\
  opt_cond IntraFreqAllowedCellList_r16__cond (SIB3__ext0O__intraFreqAllowedCellList_r16 z) /\
  opt_cond SIB3__ext0O__intraFreqCAG_CellList_r16__cond (SIB3__ext0O__intraFreqCAG_CellList_r16 z) /\
  True.

Definition SIB3__ext0__Type := SIB3__ext0O__Type.
Definition SIB3__ext0__cond := SIB3__ext0O__cond.

Require Import NR.IntraFreqNeighHSDN_CellList_r17.

Opaque IntraFreqNeighHSDN_CellList_r17__cond IntraFreqNeighHSDN_CellList_r17__Format.

Require Import NR.IntraFreqNeighCellList_v1710.

Opaque IntraFreqNeighCellList_v1710__cond IntraFreqNeighCellList_v1710__Format.

Record SIB3__ext1O__Type : Set :=
  make__SIB3__ext1O__Type {
    SIB3__ext1O__intraFreqNeighHSDN_CellList_r17 : option IntraFreqNeighHSDN_CellList_r17__Type ;
    SIB3__ext1O__intraFreqNeighCellList_v1710 : option IntraFreqNeighCellList_v1710__Type ;
}.
Definition SIB3__ext1O__list := (
 Opt IntraFreqNeighHSDN_CellList_r17__Type IntraFreqNeighHSDN_CellList_r17__cond ::
 Opt IntraFreqNeighCellList_v1710__Type IntraFreqNeighCellList_v1710__cond ::
 nil).
Definition SIB3__ext1O__cond z := 
  opt_cond IntraFreqNeighHSDN_CellList_r17__cond (SIB3__ext1O__intraFreqNeighHSDN_CellList_r17 z) /\
  opt_cond IntraFreqNeighCellList_v1710__cond (SIB3__ext1O__intraFreqNeighCellList_v1710 z) /\
  True.

Definition SIB3__ext1__Type := SIB3__ext1O__Type.
Definition SIB3__ext1__cond := SIB3__ext1O__cond.

Inductive SIB3__ext2O__channelAccessMode2_r17__Type : Set :=
 | SIB3__ext2O__channelAccessMode2_r17__enabled
.
Definition SIB3__ext2O__channelAccessMode2_r17__cond := (fun (_ : SIB3__ext2O__channelAccessMode2_r17__Type) => True).
Lemma SIB3__ext2O__channelAccessMode2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB3__ext2O__channelAccessMode2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB3__ext2O__channelAccessMode2_r17__nat__helper.

Definition SIB3__ext2O__channelAccessMode2_r17__F1 t :=
  match t with
  | SIB3__ext2O__channelAccessMode2_r17__enabled => 0
  end.
Definition SIB3__ext2O__channelAccessMode2_r17__F2 n :=
  match n with
  | 0 => SIB3__ext2O__channelAccessMode2_r17__enabled
  | _ => SIB3__ext2O__channelAccessMode2_r17__enabled
  end.
Lemma SIB3__ext2O__channelAccessMode2_r17__F1F2 : forall x : SIB3__ext2O__channelAccessMode2_r17__Type, (SIB3__ext2O__channelAccessMode2_r17__F1 x <= 0) /\ SIB3__ext2O__channelAccessMode2_r17__F2 (SIB3__ext2O__channelAccessMode2_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB3__ext2O__channelAccessMode2_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB3__ext2O__channelAccessMode2_r17__F1 (SIB3__ext2O__channelAccessMode2_r17__F2 y) = y. enum_solve H y. Qed.

Record SIB3__ext2O__Type : Set :=
  make__SIB3__ext2O__Type {
    SIB3__ext2O__channelAccessMode2_r17 : option SIB3__ext2O__channelAccessMode2_r17__Type ;
}.
Definition SIB3__ext2O__list := (
 Opt SIB3__ext2O__channelAccessMode2_r17__Type SIB3__ext2O__channelAccessMode2_r17__cond ::
 nil).
Definition SIB3__ext2O__cond z := 
  opt_cond SIB3__ext2O__channelAccessMode2_r17__cond (SIB3__ext2O__channelAccessMode2_r17 z) /\
  True.

Definition SIB3__ext2__Type := SIB3__ext2O__Type.
Definition SIB3__ext2__cond := SIB3__ext2O__cond.

Record SIB3__Type : Set :=
  make__SIB3__Type {
    SIB3__intraFreqNeighCellList : option IntraFreqNeighCellList__Type ;
    SIB3__intraFreqExcludedCellList : option IntraFreqExcludedCellList__Type ;
    SIB3__lateNonCriticalExtension : option octet_string ;
    SIB3__ext0 : option SIB3__ext0__Type ;
    SIB3__ext1 : option SIB3__ext1__Type ;
    SIB3__ext2 : option SIB3__ext2__Type ;
}.
Definition SIB3__root_list : list seq_elem := (
 Opt IntraFreqNeighCellList__Type IntraFreqNeighCellList__cond ::
 Opt IntraFreqExcludedCellList__Type IntraFreqExcludedCellList__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB3__ext_list : list typ := (
  typ_cons SIB3__ext0__Type SIB3__ext0__cond ::
  typ_cons SIB3__ext1__Type SIB3__ext1__cond ::
  typ_cons SIB3__ext2__Type SIB3__ext2__cond ::
  nil).
Definition SIB3__cond (z : SIB3__Type) := 
(  opt_cond IntraFreqNeighCellList__cond (SIB3__intraFreqNeighCellList z) /\
  opt_cond IntraFreqExcludedCellList__cond (SIB3__intraFreqExcludedCellList z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB3__lateNonCriticalExtension z) /\
  True) /\ 
(  opt_cond SIB3__ext0__cond (SIB3__ext0 z) /\
  opt_cond SIB3__ext1__cond (SIB3__ext1 z) /\
  opt_cond SIB3__ext2__cond (SIB3__ext2 z) /\
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
Definition SIB3__ext0O__intraFreqCAG_CellList_r16__Format : T_Format SIB3__ext0O__intraFreqCAG_CellList_r16__Type SIB3__ext0O__intraFreqCAG_CellList_r16__cond := seq_of_format IntraFreqCAG_CellListPerPLMN_r16__Format 1 maxPLMN SIB3__ext0O__intraFreqCAG_CellList_r16__helper1 SIB3__ext0O__intraFreqCAG_CellList_r16__helper2.

Opaque SIB3__ext0O__intraFreqCAG_CellList_r16__cond SIB3__ext0O__intraFreqCAG_CellList_r16__Format.


Definition SIB3__ext0O__Format_Type := Eval cbn in seq_format_prod SIB3__ext0O__list.
Definition SIB3__ext0O__Format_list : SIB3__ext0O__Format_Type :=
  (IntraFreqNeighCellList_v1610__Format, (IntraFreqAllowedCellList_r16__Format, (SIB3__ext0O__intraFreqCAG_CellList_r16__Format, unit_format))).
Definition SIB3__ext0O__list__Format := (*Eval compute in *) seq_format SIB3__ext0O__list SIB3__ext0O__Format_list.
Definition SIB3__ext0O__F1 z :=
  (SIB3__ext0O__intraFreqNeighCellList_v1610 z, (SIB3__ext0O__intraFreqAllowedCellList_r16 z, (SIB3__ext0O__intraFreqCAG_CellList_r16 z, tt))).
Definition SIB3__ext0O__F2 (y : seq_type SIB3__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SIB3__ext0O__Type i0 i1 i2
  end.
Lemma SIB3__ext0O__F1F2_cond (z : SIB3__ext0O__Type)
  : SIB3__ext0O__cond z ->
  (seq_cond SIB3__ext0O__list (SIB3__ext0O__F1 z)).
intro H. unfold SIB3__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB3__ext0O__F1F2_cond2 (z : SIB3__ext0O__Type)
 : SIB3__ext0O__F2 (SIB3__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB3__ext0O__F2F1_cond (y : seq_type SIB3__ext0O__list)
  : seq_cond SIB3__ext0O__list y ->
 (SIB3__ext0O__cond (SIB3__ext0O__F2 y)) /\  SIB3__ext0O__F1 (SIB3__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB3__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB3__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB3__ext0O__Format : T_Format SIB3__ext0O__Type SIB3__ext0O__cond :=
        proj2_format  SIB3__ext0O__cond SIB3__ext0O__list__Format
    SIB3__ext0O__F1 SIB3__ext0O__F2 SIB3__ext0O__F1F2_cond  SIB3__ext0O__F1F2_cond2 SIB3__ext0O__F2F1_cond.
Opaque SIB3__ext0O__cond SIB3__ext0O__Format.

Definition SIB3__ext0__check_all_none (b : SIB3__ext0O__Type) : bool :=
match b with 
  | make__SIB3__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition SIB3__ext0__Format : T_Format SIB3__ext0__Type SIB3__ext0__cond :=
  restrict_add_format SIB3__ext0__check_all_none SIB3__ext0O__Format.

Opaque SIB3__ext0__cond SIB3__ext0__Format.


Definition SIB3__ext1O__Format_Type := Eval cbn in seq_format_prod SIB3__ext1O__list.
Definition SIB3__ext1O__Format_list : SIB3__ext1O__Format_Type :=
  (IntraFreqNeighHSDN_CellList_r17__Format, (IntraFreqNeighCellList_v1710__Format, unit_format)).
Definition SIB3__ext1O__list__Format := (*Eval compute in *) seq_format SIB3__ext1O__list SIB3__ext1O__Format_list.
Definition SIB3__ext1O__F1 z :=
  (SIB3__ext1O__intraFreqNeighHSDN_CellList_r17 z, (SIB3__ext1O__intraFreqNeighCellList_v1710 z, tt)).
Definition SIB3__ext1O__F2 (y : seq_type SIB3__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB3__ext1O__Type i0 i1
  end.
Lemma SIB3__ext1O__F1F2_cond (z : SIB3__ext1O__Type)
  : SIB3__ext1O__cond z ->
  (seq_cond SIB3__ext1O__list (SIB3__ext1O__F1 z)).
intro H. unfold SIB3__ext1O__cond in H. simpl. auto. Qed.
Lemma SIB3__ext1O__F1F2_cond2 (z : SIB3__ext1O__Type)
 : SIB3__ext1O__F2 (SIB3__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB3__ext1O__F2F1_cond (y : seq_type SIB3__ext1O__list)
  : seq_cond SIB3__ext1O__list y ->
 (SIB3__ext1O__cond (SIB3__ext1O__F2 y)) /\  SIB3__ext1O__F1 (SIB3__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB3__ext1O__cond. simpl in *. auto.
 - simpl. unfold SIB3__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB3__ext1O__Format : T_Format SIB3__ext1O__Type SIB3__ext1O__cond :=
        proj2_format  SIB3__ext1O__cond SIB3__ext1O__list__Format
    SIB3__ext1O__F1 SIB3__ext1O__F2 SIB3__ext1O__F1F2_cond  SIB3__ext1O__F1F2_cond2 SIB3__ext1O__F2F1_cond.
Opaque SIB3__ext1O__cond SIB3__ext1O__Format.

Definition SIB3__ext1__check_all_none (b : SIB3__ext1O__Type) : bool :=
match b with 
  | make__SIB3__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition SIB3__ext1__Format : T_Format SIB3__ext1__Type SIB3__ext1__cond :=
  restrict_add_format SIB3__ext1__check_all_none SIB3__ext1O__Format.

Opaque SIB3__ext1__cond SIB3__ext1__Format.

Definition SIB3__ext2O__channelAccessMode2_r17__Format : T_Format SIB3__ext2O__channelAccessMode2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB3__ext2O__channelAccessMode2_r17__nat__Format SIB3__ext2O__channelAccessMode2_r17__F1 SIB3__ext2O__channelAccessMode2_r17__F2 SIB3__ext2O__channelAccessMode2_r17__F1F2 SIB3__ext2O__channelAccessMode2_r17__F2F1.

Opaque SIB3__ext2O__channelAccessMode2_r17__cond SIB3__ext2O__channelAccessMode2_r17__Format.


Definition SIB3__ext2O__Format_Type := Eval cbn in seq_format_prod SIB3__ext2O__list.
Definition SIB3__ext2O__Format_list : SIB3__ext2O__Format_Type :=
  (SIB3__ext2O__channelAccessMode2_r17__Format, unit_format).
Definition SIB3__ext2O__list__Format := (*Eval compute in *) seq_format SIB3__ext2O__list SIB3__ext2O__Format_list.
Definition SIB3__ext2O__F1 z :=
  (SIB3__ext2O__channelAccessMode2_r17 z, tt).
Definition SIB3__ext2O__F2 (y : seq_type SIB3__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__SIB3__ext2O__Type i0
  end.
Lemma SIB3__ext2O__F1F2_cond (z : SIB3__ext2O__Type)
  : SIB3__ext2O__cond z ->
  (seq_cond SIB3__ext2O__list (SIB3__ext2O__F1 z)).
intro H. unfold SIB3__ext2O__cond in H. simpl. auto. Qed.
Lemma SIB3__ext2O__F1F2_cond2 (z : SIB3__ext2O__Type)
 : SIB3__ext2O__F2 (SIB3__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB3__ext2O__F2F1_cond (y : seq_type SIB3__ext2O__list)
  : seq_cond SIB3__ext2O__list y ->
 (SIB3__ext2O__cond (SIB3__ext2O__F2 y)) /\  SIB3__ext2O__F1 (SIB3__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB3__ext2O__cond. simpl in *. auto.
 - simpl. unfold SIB3__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB3__ext2O__Format : T_Format SIB3__ext2O__Type SIB3__ext2O__cond :=
        proj2_format  SIB3__ext2O__cond SIB3__ext2O__list__Format
    SIB3__ext2O__F1 SIB3__ext2O__F2 SIB3__ext2O__F1F2_cond  SIB3__ext2O__F1F2_cond2 SIB3__ext2O__F2F1_cond.
Opaque SIB3__ext2O__cond SIB3__ext2O__Format.

Definition SIB3__ext2__check_all_none (b : SIB3__ext2O__Type) : bool :=
match b with 
  | make__SIB3__ext2O__Type None  => false 
  | _ => true 
 end.
Definition SIB3__ext2__Format : T_Format SIB3__ext2__Type SIB3__ext2__cond :=
  restrict_add_format SIB3__ext2__check_all_none SIB3__ext2O__Format.

Opaque SIB3__ext2__cond SIB3__ext2__Format.


Definition SIB3__root_Format_Type := Eval cbn in seq_format_prod SIB3__root_list.
Definition SIB3__root_Format_list : SIB3__root_Format_Type :=
  (IntraFreqNeighCellList__Format, (IntraFreqExcludedCellList__Format, (octet_string_nc__Format, unit_format))).

Definition SIB3__ext_Format_Type := Eval cbn in get_formats SIB3__ext_list.
Definition SIB3__ext_Format_list : SIB3__ext_Format_Type :=
  (SIB3__ext0__Format, (SIB3__ext1__Format, (SIB3__ext2__Format, unit__Format))).

Definition SIB3__list_type : Set := (seq_type SIB3__root_list) * (seq_ext_type SIB3__ext_list).
Definition SIB3__list_cond (z : SIB3__list_type) : Prop :=
        (seq_cond SIB3__root_list (fst z)) /\ (seq_ext_cond SIB3__ext_list (snd z)).
Definition SIB3__list_format : T_Format SIB3__list_type SIB3__list_cond :=
 (* Eval compute in *) seq_ext_format SIB3__root_list SIB3__root_Format_list SIB3__ext_list SIB3__ext_Format_list.

Opaque SIB3__list_format.
Definition SIB3__F1 (z : SIB3__Type) : SIB3__list_type :=
  (((SIB3__intraFreqNeighCellList z, (SIB3__intraFreqExcludedCellList z, (SIB3__lateNonCriticalExtension z, tt)))), (
(SIB3__ext0 z, (SIB3__ext1 z, (SIB3__ext2 z, tt))))).
Definition SIB3__F2 (y : SIB3__list_type) : SIB3__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, _))))=>
    make__SIB3__Type j0 j1 j2 i0 i1 i2
  end.
Definition SIB3__helper1 : (forall a : SIB3__Type, SIB3__cond a -> SIB3__list_cond (SIB3__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB3__helper2 : (forall a : SIB3__Type, SIB3__F2 (SIB3__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB3__helper3 : (forall b : SIB3__list_type, SIB3__list_cond b -> SIB3__cond (SIB3__F2 b) /\ SIB3__F1 (SIB3__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB3__cond, SIB3__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB3__Format : T_Format SIB3__Type SIB3__cond :=
 proj2_format SIB3__cond SIB3__list_format  SIB3__F1 SIB3__F2 SIB3__helper1 SIB3__helper2 SIB3__helper3.

Opaque SIB3__cond SIB3__Format.

