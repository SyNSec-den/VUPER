Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RRCSetupComplete_IEs__selectedPLMN_Identity__helper1 : (1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma RRCSetupComplete_IEs__selectedPLMN_Identity__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCSetupComplete_IEs__selectedPLMN_Identity__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCSetupComplete_IEs__selectedPLMN_Identity__Type := Z.
Definition RRCSetupComplete_IEs__selectedPLMN_Identity__cond := (fun z => (1 <= z <= maxPLMN)%Z).
Require Import NR.RegisteredAMF.

Opaque RegisteredAMF__cond RegisteredAMF__Format.

Inductive RRCSetupComplete_IEs__guami_Type__Type : Set :=
 | RRCSetupComplete_IEs__guami_Type__native
 | RRCSetupComplete_IEs__guami_Type__mapped
.
Definition RRCSetupComplete_IEs__guami_Type__cond := (fun (_ : RRCSetupComplete_IEs__guami_Type__Type) => True).
Lemma RRCSetupComplete_IEs__guami_Type__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCSetupComplete_IEs__guami_Type__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RRCSetupComplete_IEs__guami_Type__nat__helper.

Definition RRCSetupComplete_IEs__guami_Type__F1 t :=
  match t with
  | RRCSetupComplete_IEs__guami_Type__native => 0
  | RRCSetupComplete_IEs__guami_Type__mapped => 1
  end.
Definition RRCSetupComplete_IEs__guami_Type__F2 n :=
  match n with
  | 0 => RRCSetupComplete_IEs__guami_Type__native
  | 1 => RRCSetupComplete_IEs__guami_Type__mapped
  | _ => RRCSetupComplete_IEs__guami_Type__native
  end.
Lemma RRCSetupComplete_IEs__guami_Type__F1F2 : forall x : RRCSetupComplete_IEs__guami_Type__Type, (RRCSetupComplete_IEs__guami_Type__F1 x <= 1) /\ RRCSetupComplete_IEs__guami_Type__F2 (RRCSetupComplete_IEs__guami_Type__F1 x) = x. imp_solve. Qed.
Lemma RRCSetupComplete_IEs__guami_Type__F2F1 : forall (y : nat) (H : y <= 1), RRCSetupComplete_IEs__guami_Type__F1 (RRCSetupComplete_IEs__guami_Type__F2 y) = y. enum_solve H y. Qed.

Require Import NR.S_NSSAI.

Opaque S_NSSAI__cond S_NSSAI__Format.

Definition RRCSetupComplete_IEs__s_NSSAI_List__Type := list S_NSSAI__Type.

Lemma RRCSetupComplete_IEs__s_NSSAI_List__helper1 : (0 <= 1 <= maxNrofS_NSSAI)%Z. unfold maxNrofS_NSSAI.
 lia. Qed.
Lemma RRCSetupComplete_IEs__s_NSSAI_List__helper2 : to_bit_sz (Z.to_nat (maxNrofS_NSSAI - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofS_NSSAI - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCSetupComplete_IEs__s_NSSAI_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCSetupComplete_IEs__s_NSSAI_List__cond (z : RRCSetupComplete_IEs__s_NSSAI_List__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofS_NSSAI)%Z /\ (list_and S_NSSAI__cond z) .

Require Import NR.DedicatedNAS_Message.

Opaque DedicatedNAS_Message__cond DedicatedNAS_Message__Format.

Require Import NR.NG_5G_S_TMSI.

Opaque NG_5G_S_TMSI__cond NG_5G_S_TMSI__Format.

Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type := bit_string_fixed.
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 9 /\ bit_string_len_prop (fst z) (snd z)).

Inductive RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type : Set :=
  | RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI : NG_5G_S_TMSI__Type -> RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type
  | RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2 : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type -> RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type
.
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list : list typ := (
typ_cons NG_5G_S_TMSI__Type NG_5G_S_TMSI__cond ::
typ_cons RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__cond ::
 nil).
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond (c : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type) := 
  match c with
  | RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI t => NG_5G_S_TMSI__cond t 
  | RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2 t => RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__cond t 
  end.

Lemma RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__len_helper1 : to_bit_sz (length RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__len_helper2 : 2 <= length2 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list.
 simpl. lia. Qed.
Require Import NR.RRCSetupComplete_v1610_IEs.

Opaque RRCSetupComplete_v1610_IEs__cond RRCSetupComplete_v1610_IEs__Format.

Record RRCSetupComplete_IEs__Type : Set :=
  make__RRCSetupComplete_IEs__Type {
    RRCSetupComplete_IEs__selectedPLMN_Identity : Z ;
    RRCSetupComplete_IEs__registeredAMF : option RegisteredAMF__Type ;
    RRCSetupComplete_IEs__guami_Type : option RRCSetupComplete_IEs__guami_Type__Type ;
    RRCSetupComplete_IEs__s_NSSAI_List : option RRCSetupComplete_IEs__s_NSSAI_List__Type ;
    RRCSetupComplete_IEs__dedicatedNAS_Message : DedicatedNAS_Message__Type ;
    RRCSetupComplete_IEs__ng_5G_S_TMSI_Value : option RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type ;
    RRCSetupComplete_IEs__lateNonCriticalExtension : option octet_string ;
    RRCSetupComplete_IEs__nonCriticalExtension : option RRCSetupComplete_v1610_IEs__Type ;
}.
Definition RRCSetupComplete_IEs__list := (
 Nor Z RRCSetupComplete_IEs__selectedPLMN_Identity__cond ::
 Opt RegisteredAMF__Type RegisteredAMF__cond ::
 Opt RRCSetupComplete_IEs__guami_Type__Type RRCSetupComplete_IEs__guami_Type__cond ::
 Opt RRCSetupComplete_IEs__s_NSSAI_List__Type RRCSetupComplete_IEs__s_NSSAI_List__cond ::
 Nor DedicatedNAS_Message__Type DedicatedNAS_Message__cond ::
 Opt RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCSetupComplete_v1610_IEs__Type RRCSetupComplete_v1610_IEs__cond ::
 nil).
Definition RRCSetupComplete_IEs__cond z := 
  RRCSetupComplete_IEs__selectedPLMN_Identity__cond (RRCSetupComplete_IEs__selectedPLMN_Identity z) /\
  opt_cond RegisteredAMF__cond (RRCSetupComplete_IEs__registeredAMF z) /\
  opt_cond RRCSetupComplete_IEs__guami_Type__cond (RRCSetupComplete_IEs__guami_Type z) /\
  opt_cond RRCSetupComplete_IEs__s_NSSAI_List__cond (RRCSetupComplete_IEs__s_NSSAI_List z) /\
  DedicatedNAS_Message__cond (RRCSetupComplete_IEs__dedicatedNAS_Message z) /\
  opt_cond RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCSetupComplete_IEs__lateNonCriticalExtension z) /\
  opt_cond RRCSetupComplete_v1610_IEs__cond (RRCSetupComplete_IEs__nonCriticalExtension z) /\
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
Definition RRCSetupComplete_IEs__selectedPLMN_Identity__Format : T_Format Z RRCSetupComplete_IEs__selectedPLMN_Identity__cond :=
 ranged_int_format (1) (maxPLMN) RRCSetupComplete_IEs__selectedPLMN_Identity__helper1 RRCSetupComplete_IEs__selectedPLMN_Identity__helper2.

Opaque RRCSetupComplete_IEs__selectedPLMN_Identity__cond RRCSetupComplete_IEs__selectedPLMN_Identity__Format.

Definition RRCSetupComplete_IEs__guami_Type__Format : T_Format RRCSetupComplete_IEs__guami_Type__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCSetupComplete_IEs__guami_Type__nat__Format RRCSetupComplete_IEs__guami_Type__F1 RRCSetupComplete_IEs__guami_Type__F2 RRCSetupComplete_IEs__guami_Type__F1F2 RRCSetupComplete_IEs__guami_Type__F2F1.

Opaque RRCSetupComplete_IEs__guami_Type__cond RRCSetupComplete_IEs__guami_Type__Format.

Definition RRCSetupComplete_IEs__s_NSSAI_List__Format : T_Format RRCSetupComplete_IEs__s_NSSAI_List__Type RRCSetupComplete_IEs__s_NSSAI_List__cond := seq_of_format S_NSSAI__Format 1 maxNrofS_NSSAI RRCSetupComplete_IEs__s_NSSAI_List__helper1 RRCSetupComplete_IEs__s_NSSAI_List__helper2.

Opaque RRCSetupComplete_IEs__s_NSSAI_List__cond RRCSetupComplete_IEs__s_NSSAI_List__Format.

Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Format : T_Format RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__cond := (* Eval compute in *) bit_string_fixed_format 9.
Opaque RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__cond RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Format.


Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format_Type := Eval cbn in get_formats RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list.
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format_list : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format_Type :=
  (NG_5G_S_TMSI__Format, (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Format, unit__Format)).
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list__Format := Eval compute in choice_format RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__len_helper1 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__len_helper2  RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format_list.
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 (z : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type) : (choice RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list) :=
  match z with
   | RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI t => existT _ 0 t
  | RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2 t => existT _ 1 t
  end.
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__g := (fun n => typ_set (get_nth_typ RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list n)).
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2 (y : choice RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list) : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__g n -> RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type) with
    | 0 => fun (t : NG_5G_S_TMSI__Type) => RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI t 
    | 1 => fun (t : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type) => RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type with end) n0
           end t0).

Lemma RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__helper2 :  forall (y : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type), RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond y -> choice_cond RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__helper3 :  forall (y : RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type), RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2 (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__helper4 : (forall b : choice RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list, choice_cond RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list b -> RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2 b) /\ RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2.
Definition RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format : T_Format RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond :=
  (* Eval compute in *) proj2_format RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list__Format RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__helper2 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__helper3 RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__helper4.
Opaque RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__cond RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format.


Definition RRCSetupComplete_IEs__Format_Type := Eval cbn in seq_format_prod RRCSetupComplete_IEs__list.
Definition RRCSetupComplete_IEs__Format_list : RRCSetupComplete_IEs__Format_Type :=
  (RRCSetupComplete_IEs__selectedPLMN_Identity__Format, (RegisteredAMF__Format, (RRCSetupComplete_IEs__guami_Type__Format, (RRCSetupComplete_IEs__s_NSSAI_List__Format, (DedicatedNAS_Message__Format, (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format, (octet_string_nc__Format, (RRCSetupComplete_v1610_IEs__Format, unit_format)))))))).
Definition RRCSetupComplete_IEs__list__Format := (*Eval compute in *) seq_format RRCSetupComplete_IEs__list RRCSetupComplete_IEs__Format_list.
Definition RRCSetupComplete_IEs__F1 z :=
  (RRCSetupComplete_IEs__selectedPLMN_Identity z, (RRCSetupComplete_IEs__registeredAMF z, (RRCSetupComplete_IEs__guami_Type z, (RRCSetupComplete_IEs__s_NSSAI_List z, (RRCSetupComplete_IEs__dedicatedNAS_Message z, (RRCSetupComplete_IEs__ng_5G_S_TMSI_Value z, (RRCSetupComplete_IEs__lateNonCriticalExtension z, (RRCSetupComplete_IEs__nonCriticalExtension z, tt)))))))).
Definition RRCSetupComplete_IEs__F2 (y : seq_type RRCSetupComplete_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__RRCSetupComplete_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma RRCSetupComplete_IEs__F1F2_cond (z : RRCSetupComplete_IEs__Type)
  : RRCSetupComplete_IEs__cond z ->
  (seq_cond RRCSetupComplete_IEs__list (RRCSetupComplete_IEs__F1 z)).
intro H. unfold RRCSetupComplete_IEs__cond in H. simpl. auto. Qed.
Lemma RRCSetupComplete_IEs__F1F2_cond2 (z : RRCSetupComplete_IEs__Type)
 : RRCSetupComplete_IEs__F2 (RRCSetupComplete_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetupComplete_IEs__F2F1_cond (y : seq_type RRCSetupComplete_IEs__list)
  : seq_cond RRCSetupComplete_IEs__list y ->
 (RRCSetupComplete_IEs__cond (RRCSetupComplete_IEs__F2 y)) /\  RRCSetupComplete_IEs__F1 (RRCSetupComplete_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetupComplete_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCSetupComplete_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetupComplete_IEs__Format : T_Format RRCSetupComplete_IEs__Type RRCSetupComplete_IEs__cond :=
        proj2_format  RRCSetupComplete_IEs__cond RRCSetupComplete_IEs__list__Format
    RRCSetupComplete_IEs__F1 RRCSetupComplete_IEs__F2 RRCSetupComplete_IEs__F1F2_cond  RRCSetupComplete_IEs__F1F2_cond2 RRCSetupComplete_IEs__F2F1_cond.
Opaque RRCSetupComplete_IEs__cond RRCSetupComplete_IEs__Format.

