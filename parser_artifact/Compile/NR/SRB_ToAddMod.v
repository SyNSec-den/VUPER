Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRB_Identity.

Opaque SRB_Identity__cond SRB_Identity__Format.

Inductive SRB_ToAddMod__reestablishPDCP__Type : Set :=
 | SRB_ToAddMod__reestablishPDCP__true
.
Definition SRB_ToAddMod__reestablishPDCP__cond := (fun (_ : SRB_ToAddMod__reestablishPDCP__Type) => True).
Lemma SRB_ToAddMod__reestablishPDCP__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRB_ToAddMod__reestablishPDCP__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRB_ToAddMod__reestablishPDCP__nat__helper.

Definition SRB_ToAddMod__reestablishPDCP__F1 t :=
  match t with
  | SRB_ToAddMod__reestablishPDCP__true => 0
  end.
Definition SRB_ToAddMod__reestablishPDCP__F2 n :=
  match n with
  | 0 => SRB_ToAddMod__reestablishPDCP__true
  | _ => SRB_ToAddMod__reestablishPDCP__true
  end.
Lemma SRB_ToAddMod__reestablishPDCP__F1F2 : forall x : SRB_ToAddMod__reestablishPDCP__Type, (SRB_ToAddMod__reestablishPDCP__F1 x <= 0) /\ SRB_ToAddMod__reestablishPDCP__F2 (SRB_ToAddMod__reestablishPDCP__F1 x) = x. imp_solve. Qed.
Lemma SRB_ToAddMod__reestablishPDCP__F2F1 : forall (y : nat) (H : y <= 0), SRB_ToAddMod__reestablishPDCP__F1 (SRB_ToAddMod__reestablishPDCP__F2 y) = y. enum_solve H y. Qed.

Inductive SRB_ToAddMod__discardOnPDCP__Type : Set :=
 | SRB_ToAddMod__discardOnPDCP__true
.
Definition SRB_ToAddMod__discardOnPDCP__cond := (fun (_ : SRB_ToAddMod__discardOnPDCP__Type) => True).
Lemma SRB_ToAddMod__discardOnPDCP__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRB_ToAddMod__discardOnPDCP__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRB_ToAddMod__discardOnPDCP__nat__helper.

Definition SRB_ToAddMod__discardOnPDCP__F1 t :=
  match t with
  | SRB_ToAddMod__discardOnPDCP__true => 0
  end.
Definition SRB_ToAddMod__discardOnPDCP__F2 n :=
  match n with
  | 0 => SRB_ToAddMod__discardOnPDCP__true
  | _ => SRB_ToAddMod__discardOnPDCP__true
  end.
Lemma SRB_ToAddMod__discardOnPDCP__F1F2 : forall x : SRB_ToAddMod__discardOnPDCP__Type, (SRB_ToAddMod__discardOnPDCP__F1 x <= 0) /\ SRB_ToAddMod__discardOnPDCP__F2 (SRB_ToAddMod__discardOnPDCP__F1 x) = x. imp_solve. Qed.
Lemma SRB_ToAddMod__discardOnPDCP__F2F1 : forall (y : nat) (H : y <= 0), SRB_ToAddMod__discardOnPDCP__F1 (SRB_ToAddMod__discardOnPDCP__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PDCP_Config.

Opaque PDCP_Config__cond PDCP_Config__Format.

Require Import NR.SRB_Identity_v1700.

Opaque SRB_Identity_v1700__cond SRB_Identity_v1700__Format.

Record SRB_ToAddMod__ext0O__Type : Set :=
  make__SRB_ToAddMod__ext0O__Type {
    SRB_ToAddMod__ext0O__srb_Identity_v1700 : option SRB_Identity_v1700__Type ;
}.
Definition SRB_ToAddMod__ext0O__list := (
 Opt SRB_Identity_v1700__Type SRB_Identity_v1700__cond ::
 nil).
Definition SRB_ToAddMod__ext0O__cond z := 
  opt_cond SRB_Identity_v1700__cond (SRB_ToAddMod__ext0O__srb_Identity_v1700 z) /\
  True.

Definition SRB_ToAddMod__ext0__Type := SRB_ToAddMod__ext0O__Type.
Definition SRB_ToAddMod__ext0__cond := SRB_ToAddMod__ext0O__cond.

Record SRB_ToAddMod__Type : Set :=
  make__SRB_ToAddMod__Type {
    SRB_ToAddMod__srb_Identity : SRB_Identity__Type ;
    SRB_ToAddMod__reestablishPDCP : option SRB_ToAddMod__reestablishPDCP__Type ;
    SRB_ToAddMod__discardOnPDCP : option SRB_ToAddMod__discardOnPDCP__Type ;
    SRB_ToAddMod__pdcp_Config : option PDCP_Config__Type ;
    SRB_ToAddMod__ext0 : option SRB_ToAddMod__ext0__Type ;
}.
Definition SRB_ToAddMod__root_list : list seq_elem := (
 Nor SRB_Identity__Type SRB_Identity__cond ::
 Opt SRB_ToAddMod__reestablishPDCP__Type SRB_ToAddMod__reestablishPDCP__cond ::
 Opt SRB_ToAddMod__discardOnPDCP__Type SRB_ToAddMod__discardOnPDCP__cond ::
 Opt PDCP_Config__Type PDCP_Config__cond ::
 nil).
Definition SRB_ToAddMod__ext_list : list typ := (
  typ_cons SRB_ToAddMod__ext0__Type SRB_ToAddMod__ext0__cond ::
  nil).
Definition SRB_ToAddMod__cond (z : SRB_ToAddMod__Type) := 
(  SRB_Identity__cond (SRB_ToAddMod__srb_Identity z) /\
  opt_cond SRB_ToAddMod__reestablishPDCP__cond (SRB_ToAddMod__reestablishPDCP z) /\
  opt_cond SRB_ToAddMod__discardOnPDCP__cond (SRB_ToAddMod__discardOnPDCP z) /\
  opt_cond PDCP_Config__cond (SRB_ToAddMod__pdcp_Config z) /\
  True) /\ 
(  opt_cond SRB_ToAddMod__ext0__cond (SRB_ToAddMod__ext0 z) /\
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
Definition SRB_ToAddMod__reestablishPDCP__Format : T_Format SRB_ToAddMod__reestablishPDCP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRB_ToAddMod__reestablishPDCP__nat__Format SRB_ToAddMod__reestablishPDCP__F1 SRB_ToAddMod__reestablishPDCP__F2 SRB_ToAddMod__reestablishPDCP__F1F2 SRB_ToAddMod__reestablishPDCP__F2F1.

Opaque SRB_ToAddMod__reestablishPDCP__cond SRB_ToAddMod__reestablishPDCP__Format.

Definition SRB_ToAddMod__discardOnPDCP__Format : T_Format SRB_ToAddMod__discardOnPDCP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRB_ToAddMod__discardOnPDCP__nat__Format SRB_ToAddMod__discardOnPDCP__F1 SRB_ToAddMod__discardOnPDCP__F2 SRB_ToAddMod__discardOnPDCP__F1F2 SRB_ToAddMod__discardOnPDCP__F2F1.

Opaque SRB_ToAddMod__discardOnPDCP__cond SRB_ToAddMod__discardOnPDCP__Format.


Definition SRB_ToAddMod__ext0O__Format_Type := Eval cbn in seq_format_prod SRB_ToAddMod__ext0O__list.
Definition SRB_ToAddMod__ext0O__Format_list : SRB_ToAddMod__ext0O__Format_Type :=
  (SRB_Identity_v1700__Format, unit_format).
Definition SRB_ToAddMod__ext0O__list__Format := (*Eval compute in *) seq_format SRB_ToAddMod__ext0O__list SRB_ToAddMod__ext0O__Format_list.
Definition SRB_ToAddMod__ext0O__F1 z :=
  (SRB_ToAddMod__ext0O__srb_Identity_v1700 z, tt).
Definition SRB_ToAddMod__ext0O__F2 (y : seq_type SRB_ToAddMod__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRB_ToAddMod__ext0O__Type i0
  end.
Lemma SRB_ToAddMod__ext0O__F1F2_cond (z : SRB_ToAddMod__ext0O__Type)
  : SRB_ToAddMod__ext0O__cond z ->
  (seq_cond SRB_ToAddMod__ext0O__list (SRB_ToAddMod__ext0O__F1 z)).
intro H. unfold SRB_ToAddMod__ext0O__cond in H. simpl. auto. Qed.
Lemma SRB_ToAddMod__ext0O__F1F2_cond2 (z : SRB_ToAddMod__ext0O__Type)
 : SRB_ToAddMod__ext0O__F2 (SRB_ToAddMod__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRB_ToAddMod__ext0O__F2F1_cond (y : seq_type SRB_ToAddMod__ext0O__list)
  : seq_cond SRB_ToAddMod__ext0O__list y ->
 (SRB_ToAddMod__ext0O__cond (SRB_ToAddMod__ext0O__F2 y)) /\  SRB_ToAddMod__ext0O__F1 (SRB_ToAddMod__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRB_ToAddMod__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRB_ToAddMod__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRB_ToAddMod__ext0O__Format : T_Format SRB_ToAddMod__ext0O__Type SRB_ToAddMod__ext0O__cond :=
        proj2_format  SRB_ToAddMod__ext0O__cond SRB_ToAddMod__ext0O__list__Format
    SRB_ToAddMod__ext0O__F1 SRB_ToAddMod__ext0O__F2 SRB_ToAddMod__ext0O__F1F2_cond  SRB_ToAddMod__ext0O__F1F2_cond2 SRB_ToAddMod__ext0O__F2F1_cond.
Opaque SRB_ToAddMod__ext0O__cond SRB_ToAddMod__ext0O__Format.

Definition SRB_ToAddMod__ext0__check_all_none (b : SRB_ToAddMod__ext0O__Type) : bool :=
match b with 
  | make__SRB_ToAddMod__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRB_ToAddMod__ext0__Format : T_Format SRB_ToAddMod__ext0__Type SRB_ToAddMod__ext0__cond :=
  restrict_add_format SRB_ToAddMod__ext0__check_all_none SRB_ToAddMod__ext0O__Format.

Opaque SRB_ToAddMod__ext0__cond SRB_ToAddMod__ext0__Format.


Definition SRB_ToAddMod__root_Format_Type := Eval cbn in seq_format_prod SRB_ToAddMod__root_list.
Definition SRB_ToAddMod__root_Format_list : SRB_ToAddMod__root_Format_Type :=
  (SRB_Identity__Format, (SRB_ToAddMod__reestablishPDCP__Format, (SRB_ToAddMod__discardOnPDCP__Format, (PDCP_Config__Format, unit_format)))).

Definition SRB_ToAddMod__ext_Format_Type := Eval cbn in get_formats SRB_ToAddMod__ext_list.
Definition SRB_ToAddMod__ext_Format_list : SRB_ToAddMod__ext_Format_Type :=
  (SRB_ToAddMod__ext0__Format, unit__Format).

Definition SRB_ToAddMod__list_type : Set := (seq_type SRB_ToAddMod__root_list) * (seq_ext_type SRB_ToAddMod__ext_list).
Definition SRB_ToAddMod__list_cond (z : SRB_ToAddMod__list_type) : Prop :=
        (seq_cond SRB_ToAddMod__root_list (fst z)) /\ (seq_ext_cond SRB_ToAddMod__ext_list (snd z)).
Definition SRB_ToAddMod__list_format : T_Format SRB_ToAddMod__list_type SRB_ToAddMod__list_cond :=
 (* Eval compute in *) seq_ext_format SRB_ToAddMod__root_list SRB_ToAddMod__root_Format_list SRB_ToAddMod__ext_list SRB_ToAddMod__ext_Format_list.

Opaque SRB_ToAddMod__list_format.
Definition SRB_ToAddMod__F1 (z : SRB_ToAddMod__Type) : SRB_ToAddMod__list_type :=
  (((SRB_ToAddMod__srb_Identity z, (SRB_ToAddMod__reestablishPDCP z, (SRB_ToAddMod__discardOnPDCP z, (SRB_ToAddMod__pdcp_Config z, tt))))), (
(SRB_ToAddMod__ext0 z, tt))).
Definition SRB_ToAddMod__F2 (y : SRB_ToAddMod__list_type) : SRB_ToAddMod__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__SRB_ToAddMod__Type j0 j1 j2 j3 i0
  end.
Definition SRB_ToAddMod__helper1 : (forall a : SRB_ToAddMod__Type, SRB_ToAddMod__cond a -> SRB_ToAddMod__list_cond (SRB_ToAddMod__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRB_ToAddMod__helper2 : (forall a : SRB_ToAddMod__Type, SRB_ToAddMod__F2 (SRB_ToAddMod__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRB_ToAddMod__helper3 : (forall b : SRB_ToAddMod__list_type, SRB_ToAddMod__list_cond b -> SRB_ToAddMod__cond (SRB_ToAddMod__F2 b) /\ SRB_ToAddMod__F1 (SRB_ToAddMod__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRB_ToAddMod__cond, SRB_ToAddMod__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRB_ToAddMod__Format : T_Format SRB_ToAddMod__Type SRB_ToAddMod__cond :=
 proj2_format SRB_ToAddMod__cond SRB_ToAddMod__list_format  SRB_ToAddMod__F1 SRB_ToAddMod__F2 SRB_ToAddMod__helper1 SRB_ToAddMod__helper2 SRB_ToAddMod__helper3.

Opaque SRB_ToAddMod__cond SRB_ToAddMod__Format.

