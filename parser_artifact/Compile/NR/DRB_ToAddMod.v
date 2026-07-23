Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DRB_ToAddMod__cnAssociation__eps_BearerIdentity__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma DRB_ToAddMod__cnAssociation__eps_BearerIdentity__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRB_ToAddMod__cnAssociation__eps_BearerIdentity__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRB_ToAddMod__cnAssociation__eps_BearerIdentity__Type := Z.
Definition DRB_ToAddMod__cnAssociation__eps_BearerIdentity__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.SDAP_Config.

Opaque SDAP_Config__cond SDAP_Config__Format.


Inductive DRB_ToAddMod__cnAssociation__Type : Set :=
  | DRB_ToAddMod__cnAssociation__eps_BearerIdentity : Z -> DRB_ToAddMod__cnAssociation__Type
  | DRB_ToAddMod__cnAssociation__sdap_Config : SDAP_Config__Type -> DRB_ToAddMod__cnAssociation__Type
.
Definition DRB_ToAddMod__cnAssociation__list : list typ := (
typ_cons Z DRB_ToAddMod__cnAssociation__eps_BearerIdentity__cond ::
typ_cons SDAP_Config__Type SDAP_Config__cond ::
 nil).
Definition DRB_ToAddMod__cnAssociation__cond (c : DRB_ToAddMod__cnAssociation__Type) := 
  match c with
  | DRB_ToAddMod__cnAssociation__eps_BearerIdentity t => DRB_ToAddMod__cnAssociation__eps_BearerIdentity__cond t 
  | DRB_ToAddMod__cnAssociation__sdap_Config t => SDAP_Config__cond t 
  end.

Lemma DRB_ToAddMod__cnAssociation__len_helper1 : to_bit_sz (length DRB_ToAddMod__cnAssociation__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DRB_ToAddMod__cnAssociation__len_helper2 : 2 <= length2 DRB_ToAddMod__cnAssociation__list.
 simpl. lia. Qed.
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.

Inductive DRB_ToAddMod__reestablishPDCP__Type : Set :=
 | DRB_ToAddMod__reestablishPDCP__true
.
Definition DRB_ToAddMod__reestablishPDCP__cond := (fun (_ : DRB_ToAddMod__reestablishPDCP__Type) => True).
Lemma DRB_ToAddMod__reestablishPDCP__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRB_ToAddMod__reestablishPDCP__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DRB_ToAddMod__reestablishPDCP__nat__helper.

Definition DRB_ToAddMod__reestablishPDCP__F1 t :=
  match t with
  | DRB_ToAddMod__reestablishPDCP__true => 0
  end.
Definition DRB_ToAddMod__reestablishPDCP__F2 n :=
  match n with
  | 0 => DRB_ToAddMod__reestablishPDCP__true
  | _ => DRB_ToAddMod__reestablishPDCP__true
  end.
Lemma DRB_ToAddMod__reestablishPDCP__F1F2 : forall x : DRB_ToAddMod__reestablishPDCP__Type, (DRB_ToAddMod__reestablishPDCP__F1 x <= 0) /\ DRB_ToAddMod__reestablishPDCP__F2 (DRB_ToAddMod__reestablishPDCP__F1 x) = x. imp_solve. Qed.
Lemma DRB_ToAddMod__reestablishPDCP__F2F1 : forall (y : nat) (H : y <= 0), DRB_ToAddMod__reestablishPDCP__F1 (DRB_ToAddMod__reestablishPDCP__F2 y) = y. enum_solve H y. Qed.

Inductive DRB_ToAddMod__recoverPDCP__Type : Set :=
 | DRB_ToAddMod__recoverPDCP__true
.
Definition DRB_ToAddMod__recoverPDCP__cond := (fun (_ : DRB_ToAddMod__recoverPDCP__Type) => True).
Lemma DRB_ToAddMod__recoverPDCP__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRB_ToAddMod__recoverPDCP__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DRB_ToAddMod__recoverPDCP__nat__helper.

Definition DRB_ToAddMod__recoverPDCP__F1 t :=
  match t with
  | DRB_ToAddMod__recoverPDCP__true => 0
  end.
Definition DRB_ToAddMod__recoverPDCP__F2 n :=
  match n with
  | 0 => DRB_ToAddMod__recoverPDCP__true
  | _ => DRB_ToAddMod__recoverPDCP__true
  end.
Lemma DRB_ToAddMod__recoverPDCP__F1F2 : forall x : DRB_ToAddMod__recoverPDCP__Type, (DRB_ToAddMod__recoverPDCP__F1 x <= 0) /\ DRB_ToAddMod__recoverPDCP__F2 (DRB_ToAddMod__recoverPDCP__F1 x) = x. imp_solve. Qed.
Lemma DRB_ToAddMod__recoverPDCP__F2F1 : forall (y : nat) (H : y <= 0), DRB_ToAddMod__recoverPDCP__F1 (DRB_ToAddMod__recoverPDCP__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PDCP_Config.

Opaque PDCP_Config__cond PDCP_Config__Format.

Inductive DRB_ToAddMod__ext0O__daps_Config_r16__Type : Set :=
 | DRB_ToAddMod__ext0O__daps_Config_r16__true
.
Definition DRB_ToAddMod__ext0O__daps_Config_r16__cond := (fun (_ : DRB_ToAddMod__ext0O__daps_Config_r16__Type) => True).
Lemma DRB_ToAddMod__ext0O__daps_Config_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRB_ToAddMod__ext0O__daps_Config_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DRB_ToAddMod__ext0O__daps_Config_r16__nat__helper.

Definition DRB_ToAddMod__ext0O__daps_Config_r16__F1 t :=
  match t with
  | DRB_ToAddMod__ext0O__daps_Config_r16__true => 0
  end.
Definition DRB_ToAddMod__ext0O__daps_Config_r16__F2 n :=
  match n with
  | 0 => DRB_ToAddMod__ext0O__daps_Config_r16__true
  | _ => DRB_ToAddMod__ext0O__daps_Config_r16__true
  end.
Lemma DRB_ToAddMod__ext0O__daps_Config_r16__F1F2 : forall x : DRB_ToAddMod__ext0O__daps_Config_r16__Type, (DRB_ToAddMod__ext0O__daps_Config_r16__F1 x <= 0) /\ DRB_ToAddMod__ext0O__daps_Config_r16__F2 (DRB_ToAddMod__ext0O__daps_Config_r16__F1 x) = x. imp_solve. Qed.
Lemma DRB_ToAddMod__ext0O__daps_Config_r16__F2F1 : forall (y : nat) (H : y <= 0), DRB_ToAddMod__ext0O__daps_Config_r16__F1 (DRB_ToAddMod__ext0O__daps_Config_r16__F2 y) = y. enum_solve H y. Qed.

Record DRB_ToAddMod__ext0O__Type : Set :=
  make__DRB_ToAddMod__ext0O__Type {
    DRB_ToAddMod__ext0O__daps_Config_r16 : option DRB_ToAddMod__ext0O__daps_Config_r16__Type ;
}.
Definition DRB_ToAddMod__ext0O__list := (
 Opt DRB_ToAddMod__ext0O__daps_Config_r16__Type DRB_ToAddMod__ext0O__daps_Config_r16__cond ::
 nil).
Definition DRB_ToAddMod__ext0O__cond z := 
  opt_cond DRB_ToAddMod__ext0O__daps_Config_r16__cond (DRB_ToAddMod__ext0O__daps_Config_r16 z) /\
  True.

Definition DRB_ToAddMod__ext0__Type := DRB_ToAddMod__ext0O__Type.
Definition DRB_ToAddMod__ext0__cond := DRB_ToAddMod__ext0O__cond.

Record DRB_ToAddMod__Type : Set :=
  make__DRB_ToAddMod__Type {
    DRB_ToAddMod__cnAssociation : option DRB_ToAddMod__cnAssociation__Type ;
    DRB_ToAddMod__drb_Identity : DRB_Identity__Type ;
    DRB_ToAddMod__reestablishPDCP : option DRB_ToAddMod__reestablishPDCP__Type ;
    DRB_ToAddMod__recoverPDCP : option DRB_ToAddMod__recoverPDCP__Type ;
    DRB_ToAddMod__pdcp_Config : option PDCP_Config__Type ;
    DRB_ToAddMod__ext0 : option DRB_ToAddMod__ext0__Type ;
}.
Definition DRB_ToAddMod__root_list : list seq_elem := (
 Opt DRB_ToAddMod__cnAssociation__Type DRB_ToAddMod__cnAssociation__cond ::
 Nor DRB_Identity__Type DRB_Identity__cond ::
 Opt DRB_ToAddMod__reestablishPDCP__Type DRB_ToAddMod__reestablishPDCP__cond ::
 Opt DRB_ToAddMod__recoverPDCP__Type DRB_ToAddMod__recoverPDCP__cond ::
 Opt PDCP_Config__Type PDCP_Config__cond ::
 nil).
Definition DRB_ToAddMod__ext_list : list typ := (
  typ_cons DRB_ToAddMod__ext0__Type DRB_ToAddMod__ext0__cond ::
  nil).
Definition DRB_ToAddMod__cond (z : DRB_ToAddMod__Type) := 
(  opt_cond DRB_ToAddMod__cnAssociation__cond (DRB_ToAddMod__cnAssociation z) /\
  DRB_Identity__cond (DRB_ToAddMod__drb_Identity z) /\
  opt_cond DRB_ToAddMod__reestablishPDCP__cond (DRB_ToAddMod__reestablishPDCP z) /\
  opt_cond DRB_ToAddMod__recoverPDCP__cond (DRB_ToAddMod__recoverPDCP z) /\
  opt_cond PDCP_Config__cond (DRB_ToAddMod__pdcp_Config z) /\
  True) /\ 
(  opt_cond DRB_ToAddMod__ext0__cond (DRB_ToAddMod__ext0 z) /\
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
Definition DRB_ToAddMod__cnAssociation__eps_BearerIdentity__Format : T_Format Z DRB_ToAddMod__cnAssociation__eps_BearerIdentity__cond :=
 ranged_int_format (0) (15) DRB_ToAddMod__cnAssociation__eps_BearerIdentity__helper1 DRB_ToAddMod__cnAssociation__eps_BearerIdentity__helper2.

Opaque DRB_ToAddMod__cnAssociation__eps_BearerIdentity__cond DRB_ToAddMod__cnAssociation__eps_BearerIdentity__Format.


Definition DRB_ToAddMod__cnAssociation__Format_Type := Eval cbn in get_formats DRB_ToAddMod__cnAssociation__list.
Definition DRB_ToAddMod__cnAssociation__Format_list : DRB_ToAddMod__cnAssociation__Format_Type :=
  (DRB_ToAddMod__cnAssociation__eps_BearerIdentity__Format, (SDAP_Config__Format, unit__Format)).
Definition DRB_ToAddMod__cnAssociation__list__Format := Eval compute in choice_format DRB_ToAddMod__cnAssociation__list DRB_ToAddMod__cnAssociation__len_helper1 DRB_ToAddMod__cnAssociation__len_helper2  DRB_ToAddMod__cnAssociation__Format_list.
Definition DRB_ToAddMod__cnAssociation__F1 (z : DRB_ToAddMod__cnAssociation__Type) : (choice DRB_ToAddMod__cnAssociation__list) :=
  match z with
   | DRB_ToAddMod__cnAssociation__eps_BearerIdentity t => existT _ 0 t
  | DRB_ToAddMod__cnAssociation__sdap_Config t => existT _ 1 t
  end.
Definition DRB_ToAddMod__cnAssociation__g := (fun n => typ_set (get_nth_typ DRB_ToAddMod__cnAssociation__list n)).
Definition DRB_ToAddMod__cnAssociation__F2 (y : choice DRB_ToAddMod__cnAssociation__list) : DRB_ToAddMod__cnAssociation__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DRB_ToAddMod__cnAssociation__g n -> DRB_ToAddMod__cnAssociation__Type) with
    | 0 => fun (t : Z) => DRB_ToAddMod__cnAssociation__eps_BearerIdentity t 
    | 1 => fun (t : SDAP_Config__Type) => DRB_ToAddMod__cnAssociation__sdap_Config t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DRB_ToAddMod__cnAssociation__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DRB_ToAddMod__cnAssociation__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DRB_ToAddMod__cnAssociation__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DRB_ToAddMod__cnAssociation__Type with end) n0
           end t0).

Lemma DRB_ToAddMod__cnAssociation__helper2 :  forall (y : DRB_ToAddMod__cnAssociation__Type), DRB_ToAddMod__cnAssociation__cond y -> choice_cond DRB_ToAddMod__cnAssociation__list (DRB_ToAddMod__cnAssociation__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DRB_ToAddMod__cnAssociation__helper3 :  forall (y : DRB_ToAddMod__cnAssociation__Type), DRB_ToAddMod__cnAssociation__F2 (DRB_ToAddMod__cnAssociation__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DRB_ToAddMod__cnAssociation__helper4 : (forall b : choice DRB_ToAddMod__cnAssociation__list, choice_cond DRB_ToAddMod__cnAssociation__list b -> DRB_ToAddMod__cnAssociation__cond (DRB_ToAddMod__cnAssociation__F2 b) /\ DRB_ToAddMod__cnAssociation__F1 (DRB_ToAddMod__cnAssociation__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DRB_ToAddMod__cnAssociation__F1 DRB_ToAddMod__cnAssociation__F2.
Definition DRB_ToAddMod__cnAssociation__Format : T_Format DRB_ToAddMod__cnAssociation__Type DRB_ToAddMod__cnAssociation__cond :=
  (* Eval compute in *) proj2_format DRB_ToAddMod__cnAssociation__cond DRB_ToAddMod__cnAssociation__list__Format DRB_ToAddMod__cnAssociation__F1 DRB_ToAddMod__cnAssociation__F2 DRB_ToAddMod__cnAssociation__helper2 DRB_ToAddMod__cnAssociation__helper3 DRB_ToAddMod__cnAssociation__helper4.
Opaque DRB_ToAddMod__cnAssociation__cond DRB_ToAddMod__cnAssociation__Format.

Definition DRB_ToAddMod__reestablishPDCP__Format : T_Format DRB_ToAddMod__reestablishPDCP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRB_ToAddMod__reestablishPDCP__nat__Format DRB_ToAddMod__reestablishPDCP__F1 DRB_ToAddMod__reestablishPDCP__F2 DRB_ToAddMod__reestablishPDCP__F1F2 DRB_ToAddMod__reestablishPDCP__F2F1.

Opaque DRB_ToAddMod__reestablishPDCP__cond DRB_ToAddMod__reestablishPDCP__Format.

Definition DRB_ToAddMod__recoverPDCP__Format : T_Format DRB_ToAddMod__recoverPDCP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRB_ToAddMod__recoverPDCP__nat__Format DRB_ToAddMod__recoverPDCP__F1 DRB_ToAddMod__recoverPDCP__F2 DRB_ToAddMod__recoverPDCP__F1F2 DRB_ToAddMod__recoverPDCP__F2F1.

Opaque DRB_ToAddMod__recoverPDCP__cond DRB_ToAddMod__recoverPDCP__Format.

Definition DRB_ToAddMod__ext0O__daps_Config_r16__Format : T_Format DRB_ToAddMod__ext0O__daps_Config_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRB_ToAddMod__ext0O__daps_Config_r16__nat__Format DRB_ToAddMod__ext0O__daps_Config_r16__F1 DRB_ToAddMod__ext0O__daps_Config_r16__F2 DRB_ToAddMod__ext0O__daps_Config_r16__F1F2 DRB_ToAddMod__ext0O__daps_Config_r16__F2F1.

Opaque DRB_ToAddMod__ext0O__daps_Config_r16__cond DRB_ToAddMod__ext0O__daps_Config_r16__Format.


Definition DRB_ToAddMod__ext0O__Format_Type := Eval cbn in seq_format_prod DRB_ToAddMod__ext0O__list.
Definition DRB_ToAddMod__ext0O__Format_list : DRB_ToAddMod__ext0O__Format_Type :=
  (DRB_ToAddMod__ext0O__daps_Config_r16__Format, unit_format).
Definition DRB_ToAddMod__ext0O__list__Format := (*Eval compute in *) seq_format DRB_ToAddMod__ext0O__list DRB_ToAddMod__ext0O__Format_list.
Definition DRB_ToAddMod__ext0O__F1 z :=
  (DRB_ToAddMod__ext0O__daps_Config_r16 z, tt).
Definition DRB_ToAddMod__ext0O__F2 (y : seq_type DRB_ToAddMod__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__DRB_ToAddMod__ext0O__Type i0
  end.
Lemma DRB_ToAddMod__ext0O__F1F2_cond (z : DRB_ToAddMod__ext0O__Type)
  : DRB_ToAddMod__ext0O__cond z ->
  (seq_cond DRB_ToAddMod__ext0O__list (DRB_ToAddMod__ext0O__F1 z)).
intro H. unfold DRB_ToAddMod__ext0O__cond in H. simpl. auto. Qed.
Lemma DRB_ToAddMod__ext0O__F1F2_cond2 (z : DRB_ToAddMod__ext0O__Type)
 : DRB_ToAddMod__ext0O__F2 (DRB_ToAddMod__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRB_ToAddMod__ext0O__F2F1_cond (y : seq_type DRB_ToAddMod__ext0O__list)
  : seq_cond DRB_ToAddMod__ext0O__list y ->
 (DRB_ToAddMod__ext0O__cond (DRB_ToAddMod__ext0O__F2 y)) /\  DRB_ToAddMod__ext0O__F1 (DRB_ToAddMod__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRB_ToAddMod__ext0O__cond. simpl in *. auto.
 - simpl. unfold DRB_ToAddMod__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRB_ToAddMod__ext0O__Format : T_Format DRB_ToAddMod__ext0O__Type DRB_ToAddMod__ext0O__cond :=
        proj2_format  DRB_ToAddMod__ext0O__cond DRB_ToAddMod__ext0O__list__Format
    DRB_ToAddMod__ext0O__F1 DRB_ToAddMod__ext0O__F2 DRB_ToAddMod__ext0O__F1F2_cond  DRB_ToAddMod__ext0O__F1F2_cond2 DRB_ToAddMod__ext0O__F2F1_cond.
Opaque DRB_ToAddMod__ext0O__cond DRB_ToAddMod__ext0O__Format.

Definition DRB_ToAddMod__ext0__check_all_none (b : DRB_ToAddMod__ext0O__Type) : bool :=
match b with 
  | make__DRB_ToAddMod__ext0O__Type None  => false 
  | _ => true 
 end.
Definition DRB_ToAddMod__ext0__Format : T_Format DRB_ToAddMod__ext0__Type DRB_ToAddMod__ext0__cond :=
  restrict_add_format DRB_ToAddMod__ext0__check_all_none DRB_ToAddMod__ext0O__Format.

Opaque DRB_ToAddMod__ext0__cond DRB_ToAddMod__ext0__Format.


Definition DRB_ToAddMod__root_Format_Type := Eval cbn in seq_format_prod DRB_ToAddMod__root_list.
Definition DRB_ToAddMod__root_Format_list : DRB_ToAddMod__root_Format_Type :=
  (DRB_ToAddMod__cnAssociation__Format, (DRB_Identity__Format, (DRB_ToAddMod__reestablishPDCP__Format, (DRB_ToAddMod__recoverPDCP__Format, (PDCP_Config__Format, unit_format))))).

Definition DRB_ToAddMod__ext_Format_Type := Eval cbn in get_formats DRB_ToAddMod__ext_list.
Definition DRB_ToAddMod__ext_Format_list : DRB_ToAddMod__ext_Format_Type :=
  (DRB_ToAddMod__ext0__Format, unit__Format).

Definition DRB_ToAddMod__list_type : Set := (seq_type DRB_ToAddMod__root_list) * (seq_ext_type DRB_ToAddMod__ext_list).
Definition DRB_ToAddMod__list_cond (z : DRB_ToAddMod__list_type) : Prop :=
        (seq_cond DRB_ToAddMod__root_list (fst z)) /\ (seq_ext_cond DRB_ToAddMod__ext_list (snd z)).
Definition DRB_ToAddMod__list_format : T_Format DRB_ToAddMod__list_type DRB_ToAddMod__list_cond :=
 (* Eval compute in *) seq_ext_format DRB_ToAddMod__root_list DRB_ToAddMod__root_Format_list DRB_ToAddMod__ext_list DRB_ToAddMod__ext_Format_list.

Opaque DRB_ToAddMod__list_format.
Definition DRB_ToAddMod__F1 (z : DRB_ToAddMod__Type) : DRB_ToAddMod__list_type :=
  (((DRB_ToAddMod__cnAssociation z, (DRB_ToAddMod__drb_Identity z, (DRB_ToAddMod__reestablishPDCP z, (DRB_ToAddMod__recoverPDCP z, (DRB_ToAddMod__pdcp_Config z, tt)))))), (
(DRB_ToAddMod__ext0 z, tt))).
Definition DRB_ToAddMod__F2 (y : DRB_ToAddMod__list_type) : DRB_ToAddMod__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__DRB_ToAddMod__Type j0 j1 j2 j3 j4 i0
  end.
Definition DRB_ToAddMod__helper1 : (forall a : DRB_ToAddMod__Type, DRB_ToAddMod__cond a -> DRB_ToAddMod__list_cond (DRB_ToAddMod__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DRB_ToAddMod__helper2 : (forall a : DRB_ToAddMod__Type, DRB_ToAddMod__F2 (DRB_ToAddMod__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DRB_ToAddMod__helper3 : (forall b : DRB_ToAddMod__list_type, DRB_ToAddMod__list_cond b -> DRB_ToAddMod__cond (DRB_ToAddMod__F2 b) /\ DRB_ToAddMod__F1 (DRB_ToAddMod__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DRB_ToAddMod__cond, DRB_ToAddMod__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DRB_ToAddMod__Format : T_Format DRB_ToAddMod__Type DRB_ToAddMod__cond :=
 proj2_format DRB_ToAddMod__cond DRB_ToAddMod__list_format  DRB_ToAddMod__F1 DRB_ToAddMod__F2 DRB_ToAddMod__helper1 DRB_ToAddMod__helper2 DRB_ToAddMod__helper3.

Opaque DRB_ToAddMod__cond DRB_ToAddMod__Format.

