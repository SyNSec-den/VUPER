Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Record AS_Config__ext0O__Type : Set :=
  make__AS_Config__ext0O__Type {
    AS_Config__ext0O__sourceRB_SN_Config : option octet_string ;
    AS_Config__ext0O__sourceSCG_NR_Config : option octet_string ;
    AS_Config__ext0O__sourceSCG_EUTRA_Config : option octet_string ;
}.
Definition AS_Config__ext0O__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition AS_Config__ext0O__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Config__ext0O__sourceRB_SN_Config z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Config__ext0O__sourceSCG_NR_Config z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Config__ext0O__sourceSCG_EUTRA_Config z) /\
  True.

Definition AS_Config__ext0__Type := AS_Config__ext0O__Type.
Definition AS_Config__ext0__cond := AS_Config__ext0O__cond.

Inductive AS_Config__ext1O__sourceSCG_Configured__Type : Set :=
 | AS_Config__ext1O__sourceSCG_Configured__true
.
Definition AS_Config__ext1O__sourceSCG_Configured__cond := (fun (_ : AS_Config__ext1O__sourceSCG_Configured__Type) => True).
Lemma AS_Config__ext1O__sourceSCG_Configured__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition AS_Config__ext1O__sourceSCG_Configured__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 AS_Config__ext1O__sourceSCG_Configured__nat__helper.

Definition AS_Config__ext1O__sourceSCG_Configured__F1 t :=
  match t with
  | AS_Config__ext1O__sourceSCG_Configured__true => 0
  end.
Definition AS_Config__ext1O__sourceSCG_Configured__F2 n :=
  match n with
  | 0 => AS_Config__ext1O__sourceSCG_Configured__true
  | _ => AS_Config__ext1O__sourceSCG_Configured__true
  end.
Lemma AS_Config__ext1O__sourceSCG_Configured__F1F2 : forall x : AS_Config__ext1O__sourceSCG_Configured__Type, (AS_Config__ext1O__sourceSCG_Configured__F1 x <= 0) /\ AS_Config__ext1O__sourceSCG_Configured__F2 (AS_Config__ext1O__sourceSCG_Configured__F1 x) = x. imp_solve. Qed.
Lemma AS_Config__ext1O__sourceSCG_Configured__F2F1 : forall (y : nat) (H : y <= 0), AS_Config__ext1O__sourceSCG_Configured__F1 (AS_Config__ext1O__sourceSCG_Configured__F2 y) = y. enum_solve H y. Qed.

Record AS_Config__ext1O__Type : Set :=
  make__AS_Config__ext1O__Type {
    AS_Config__ext1O__sourceSCG_Configured : option AS_Config__ext1O__sourceSCG_Configured__Type ;
}.
Definition AS_Config__ext1O__list := (
 Opt AS_Config__ext1O__sourceSCG_Configured__Type AS_Config__ext1O__sourceSCG_Configured__cond ::
 nil).
Definition AS_Config__ext1O__cond z := 
  opt_cond AS_Config__ext1O__sourceSCG_Configured__cond (AS_Config__ext1O__sourceSCG_Configured z) /\
  True.

Definition AS_Config__ext1__Type := AS_Config__ext1O__Type.
Definition AS_Config__ext1__cond := AS_Config__ext1O__cond.

Require Import NR.SDT_Config_r17.

Opaque SDT_Config_r17__cond SDT_Config_r17__Format.

Record AS_Config__ext2O__Type : Set :=
  make__AS_Config__ext2O__Type {
    AS_Config__ext2O__sdt_Config_r17 : option SDT_Config_r17__Type ;
}.
Definition AS_Config__ext2O__list := (
 Opt SDT_Config_r17__Type SDT_Config_r17__cond ::
 nil).
Definition AS_Config__ext2O__cond z := 
  opt_cond SDT_Config_r17__cond (AS_Config__ext2O__sdt_Config_r17 z) /\
  True.

Definition AS_Config__ext2__Type := AS_Config__ext2O__Type.
Definition AS_Config__ext2__cond := AS_Config__ext2O__cond.

Record AS_Config__Type : Set :=
  make__AS_Config__Type {
    AS_Config__rrcReconfiguration : octet_string ;
    AS_Config__ext0 : option AS_Config__ext0__Type ;
    AS_Config__ext1 : option AS_Config__ext1__Type ;
    AS_Config__ext2 : option AS_Config__ext2__Type ;
}.
Definition AS_Config__root_list : list seq_elem := (
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition AS_Config__ext_list : list typ := (
  typ_cons AS_Config__ext0__Type AS_Config__ext0__cond ::
  typ_cons AS_Config__ext1__Type AS_Config__ext1__cond ::
  typ_cons AS_Config__ext2__Type AS_Config__ext2__cond ::
  nil).
Definition AS_Config__cond (z : AS_Config__Type) := 
(  (fun (b : octet_string) => length b < Nat.pow 2 14) (AS_Config__rrcReconfiguration z) /\
  True) /\ 
(  opt_cond AS_Config__ext0__cond (AS_Config__ext0 z) /\
  opt_cond AS_Config__ext1__cond (AS_Config__ext1 z) /\
  opt_cond AS_Config__ext2__cond (AS_Config__ext2 z) /\
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

Definition AS_Config__ext0O__Format_Type := Eval cbn in seq_format_prod AS_Config__ext0O__list.
Definition AS_Config__ext0O__Format_list : AS_Config__ext0O__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, unit_format))).
Definition AS_Config__ext0O__list__Format := (*Eval compute in *) seq_format AS_Config__ext0O__list AS_Config__ext0O__Format_list.
Definition AS_Config__ext0O__F1 z :=
  (AS_Config__ext0O__sourceRB_SN_Config z, (AS_Config__ext0O__sourceSCG_NR_Config z, (AS_Config__ext0O__sourceSCG_EUTRA_Config z, tt))).
Definition AS_Config__ext0O__F2 (y : seq_type AS_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__AS_Config__ext0O__Type i0 i1 i2
  end.
Lemma AS_Config__ext0O__F1F2_cond (z : AS_Config__ext0O__Type)
  : AS_Config__ext0O__cond z ->
  (seq_cond AS_Config__ext0O__list (AS_Config__ext0O__F1 z)).
intro H. unfold AS_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma AS_Config__ext0O__F1F2_cond2 (z : AS_Config__ext0O__Type)
 : AS_Config__ext0O__F2 (AS_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Config__ext0O__F2F1_cond (y : seq_type AS_Config__ext0O__list)
  : seq_cond AS_Config__ext0O__list y ->
 (AS_Config__ext0O__cond (AS_Config__ext0O__F2 y)) /\  AS_Config__ext0O__F1 (AS_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold AS_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Config__ext0O__Format : T_Format AS_Config__ext0O__Type AS_Config__ext0O__cond :=
        proj2_format  AS_Config__ext0O__cond AS_Config__ext0O__list__Format
    AS_Config__ext0O__F1 AS_Config__ext0O__F2 AS_Config__ext0O__F1F2_cond  AS_Config__ext0O__F1F2_cond2 AS_Config__ext0O__F2F1_cond.
Opaque AS_Config__ext0O__cond AS_Config__ext0O__Format.

Definition AS_Config__ext0__check_all_none (b : AS_Config__ext0O__Type) : bool :=
match b with 
  | make__AS_Config__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition AS_Config__ext0__Format : T_Format AS_Config__ext0__Type AS_Config__ext0__cond :=
  restrict_add_format AS_Config__ext0__check_all_none AS_Config__ext0O__Format.

Opaque AS_Config__ext0__cond AS_Config__ext0__Format.

Definition AS_Config__ext1O__sourceSCG_Configured__Format : T_Format AS_Config__ext1O__sourceSCG_Configured__Type (fun _ => True) :=
(* Eval compute in *) proj3_format AS_Config__ext1O__sourceSCG_Configured__nat__Format AS_Config__ext1O__sourceSCG_Configured__F1 AS_Config__ext1O__sourceSCG_Configured__F2 AS_Config__ext1O__sourceSCG_Configured__F1F2 AS_Config__ext1O__sourceSCG_Configured__F2F1.

Opaque AS_Config__ext1O__sourceSCG_Configured__cond AS_Config__ext1O__sourceSCG_Configured__Format.


Definition AS_Config__ext1O__Format_Type := Eval cbn in seq_format_prod AS_Config__ext1O__list.
Definition AS_Config__ext1O__Format_list : AS_Config__ext1O__Format_Type :=
  (AS_Config__ext1O__sourceSCG_Configured__Format, unit_format).
Definition AS_Config__ext1O__list__Format := (*Eval compute in *) seq_format AS_Config__ext1O__list AS_Config__ext1O__Format_list.
Definition AS_Config__ext1O__F1 z :=
  (AS_Config__ext1O__sourceSCG_Configured z, tt).
Definition AS_Config__ext1O__F2 (y : seq_type AS_Config__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__AS_Config__ext1O__Type i0
  end.
Lemma AS_Config__ext1O__F1F2_cond (z : AS_Config__ext1O__Type)
  : AS_Config__ext1O__cond z ->
  (seq_cond AS_Config__ext1O__list (AS_Config__ext1O__F1 z)).
intro H. unfold AS_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma AS_Config__ext1O__F1F2_cond2 (z : AS_Config__ext1O__Type)
 : AS_Config__ext1O__F2 (AS_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Config__ext1O__F2F1_cond (y : seq_type AS_Config__ext1O__list)
  : seq_cond AS_Config__ext1O__list y ->
 (AS_Config__ext1O__cond (AS_Config__ext1O__F2 y)) /\  AS_Config__ext1O__F1 (AS_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold AS_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Config__ext1O__Format : T_Format AS_Config__ext1O__Type AS_Config__ext1O__cond :=
        proj2_format  AS_Config__ext1O__cond AS_Config__ext1O__list__Format
    AS_Config__ext1O__F1 AS_Config__ext1O__F2 AS_Config__ext1O__F1F2_cond  AS_Config__ext1O__F1F2_cond2 AS_Config__ext1O__F2F1_cond.
Opaque AS_Config__ext1O__cond AS_Config__ext1O__Format.

Definition AS_Config__ext1__check_all_none (b : AS_Config__ext1O__Type) : bool :=
match b with 
  | make__AS_Config__ext1O__Type None  => false 
  | _ => true 
 end.
Definition AS_Config__ext1__Format : T_Format AS_Config__ext1__Type AS_Config__ext1__cond :=
  restrict_add_format AS_Config__ext1__check_all_none AS_Config__ext1O__Format.

Opaque AS_Config__ext1__cond AS_Config__ext1__Format.


Definition AS_Config__ext2O__Format_Type := Eval cbn in seq_format_prod AS_Config__ext2O__list.
Definition AS_Config__ext2O__Format_list : AS_Config__ext2O__Format_Type :=
  (SDT_Config_r17__Format, unit_format).
Definition AS_Config__ext2O__list__Format := (*Eval compute in *) seq_format AS_Config__ext2O__list AS_Config__ext2O__Format_list.
Definition AS_Config__ext2O__F1 z :=
  (AS_Config__ext2O__sdt_Config_r17 z, tt).
Definition AS_Config__ext2O__F2 (y : seq_type AS_Config__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__AS_Config__ext2O__Type i0
  end.
Lemma AS_Config__ext2O__F1F2_cond (z : AS_Config__ext2O__Type)
  : AS_Config__ext2O__cond z ->
  (seq_cond AS_Config__ext2O__list (AS_Config__ext2O__F1 z)).
intro H. unfold AS_Config__ext2O__cond in H. simpl. auto. Qed.
Lemma AS_Config__ext2O__F1F2_cond2 (z : AS_Config__ext2O__Type)
 : AS_Config__ext2O__F2 (AS_Config__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AS_Config__ext2O__F2F1_cond (y : seq_type AS_Config__ext2O__list)
  : seq_cond AS_Config__ext2O__list y ->
 (AS_Config__ext2O__cond (AS_Config__ext2O__F2 y)) /\  AS_Config__ext2O__F1 (AS_Config__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AS_Config__ext2O__cond. simpl in *. auto.
 - simpl. unfold AS_Config__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AS_Config__ext2O__Format : T_Format AS_Config__ext2O__Type AS_Config__ext2O__cond :=
        proj2_format  AS_Config__ext2O__cond AS_Config__ext2O__list__Format
    AS_Config__ext2O__F1 AS_Config__ext2O__F2 AS_Config__ext2O__F1F2_cond  AS_Config__ext2O__F1F2_cond2 AS_Config__ext2O__F2F1_cond.
Opaque AS_Config__ext2O__cond AS_Config__ext2O__Format.

Definition AS_Config__ext2__check_all_none (b : AS_Config__ext2O__Type) : bool :=
match b with 
  | make__AS_Config__ext2O__Type None  => false 
  | _ => true 
 end.
Definition AS_Config__ext2__Format : T_Format AS_Config__ext2__Type AS_Config__ext2__cond :=
  restrict_add_format AS_Config__ext2__check_all_none AS_Config__ext2O__Format.

Opaque AS_Config__ext2__cond AS_Config__ext2__Format.


Definition AS_Config__root_Format_Type := Eval cbn in seq_format_prod AS_Config__root_list.
Definition AS_Config__root_Format_list : AS_Config__root_Format_Type :=
  (octet_string_nc__Format, unit_format).

Definition AS_Config__ext_Format_Type := Eval cbn in get_formats AS_Config__ext_list.
Definition AS_Config__ext_Format_list : AS_Config__ext_Format_Type :=
  (AS_Config__ext0__Format, (AS_Config__ext1__Format, (AS_Config__ext2__Format, unit__Format))).

Definition AS_Config__list_type : Set := (seq_type AS_Config__root_list) * (seq_ext_type AS_Config__ext_list).
Definition AS_Config__list_cond (z : AS_Config__list_type) : Prop :=
        (seq_cond AS_Config__root_list (fst z)) /\ (seq_ext_cond AS_Config__ext_list (snd z)).
Definition AS_Config__list_format : T_Format AS_Config__list_type AS_Config__list_cond :=
 (* Eval compute in *) seq_ext_format AS_Config__root_list AS_Config__root_Format_list AS_Config__ext_list AS_Config__ext_Format_list.

Opaque AS_Config__list_format.
Definition AS_Config__F1 (z : AS_Config__Type) : AS_Config__list_type :=
  (((AS_Config__rrcReconfiguration z, tt)), (
(AS_Config__ext0 z, (AS_Config__ext1 z, (AS_Config__ext2 z, tt))))).
Definition AS_Config__F2 (y : AS_Config__list_type) : AS_Config__Type :=
  match y with
  | ((j0, _), (i0, (i1, (i2, _))))=>
    make__AS_Config__Type j0 i0 i1 i2
  end.
Definition AS_Config__helper1 : (forall a : AS_Config__Type, AS_Config__cond a -> AS_Config__list_cond (AS_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition AS_Config__helper2 : (forall a : AS_Config__Type, AS_Config__F2 (AS_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition AS_Config__helper3 : (forall b : AS_Config__list_type, AS_Config__list_cond b -> AS_Config__cond (AS_Config__F2 b) /\ AS_Config__F1 (AS_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold AS_Config__cond, AS_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition AS_Config__Format : T_Format AS_Config__Type AS_Config__cond :=
 proj2_format AS_Config__cond AS_Config__list_format  AS_Config__F1 AS_Config__F2 AS_Config__helper1 AS_Config__helper2 AS_Config__helper3.

Opaque AS_Config__cond AS_Config__Format.

