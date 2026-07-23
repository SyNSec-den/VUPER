Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.

Inductive SL_RLC_ModeIndication_r16__sl_Mode_r16__Type : Set :=
  | SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_AM_Mode_r16 : unit -> SL_RLC_ModeIndication_r16__sl_Mode_r16__Type
  | SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_UM_Mode_r16 : unit -> SL_RLC_ModeIndication_r16__sl_Mode_r16__Type
.
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__cond (c : SL_RLC_ModeIndication_r16__sl_Mode_r16__Type) := 
  match c with
  | SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_AM_Mode_r16 t => (fun _ => True) t 
  | SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_UM_Mode_r16 t => (fun _ => True) t 
  end.

Lemma SL_RLC_ModeIndication_r16__sl_Mode_r16__len_helper1 : to_bit_sz (length SL_RLC_ModeIndication_r16__sl_Mode_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_RLC_ModeIndication_r16__sl_Mode_r16__len_helper2 : 2 <= length2 SL_RLC_ModeIndication_r16__sl_Mode_r16__list.
 simpl. lia. Qed.
Require Import NR.SL_QoS_Info_r16.

Opaque SL_QoS_Info_r16__cond SL_QoS_Info_r16__Format.

Definition SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type := list SL_QoS_Info_r16__Type.

Lemma SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__helper1 : (0 <= 1 <= maxNrofSL_QFIsPerDest_r16)%Z. unfold maxNrofSL_QFIsPerDest_r16.
 lia. Qed.
Lemma SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_QFIsPerDest_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_QFIsPerDest_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__cond (z : SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_QFIsPerDest_r16)%Z /\ (list_and SL_QoS_Info_r16__cond z) .

Record SL_RLC_ModeIndication_r16__Type : Set :=
  make__SL_RLC_ModeIndication_r16__Type {
    SL_RLC_ModeIndication_r16__sl_Mode_r16 : SL_RLC_ModeIndication_r16__sl_Mode_r16__Type ;
    SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16 : SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type ;
}.
Definition SL_RLC_ModeIndication_r16__list := (
 Nor SL_RLC_ModeIndication_r16__sl_Mode_r16__Type SL_RLC_ModeIndication_r16__sl_Mode_r16__cond ::
 Nor SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__cond ::
 nil).
Definition SL_RLC_ModeIndication_r16__cond z := 
  SL_RLC_ModeIndication_r16__sl_Mode_r16__cond (SL_RLC_ModeIndication_r16__sl_Mode_r16 z) /\
  SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__cond (SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16 z) /\
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

Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__Format_Type := Eval cbn in get_formats SL_RLC_ModeIndication_r16__sl_Mode_r16__list.
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__Format_list : SL_RLC_ModeIndication_r16__sl_Mode_r16__Format_Type :=
  (unit__Format, (unit__Format, unit__Format)).
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__list__Format := Eval compute in choice_format SL_RLC_ModeIndication_r16__sl_Mode_r16__list SL_RLC_ModeIndication_r16__sl_Mode_r16__len_helper1 SL_RLC_ModeIndication_r16__sl_Mode_r16__len_helper2  SL_RLC_ModeIndication_r16__sl_Mode_r16__Format_list.
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__F1 (z : SL_RLC_ModeIndication_r16__sl_Mode_r16__Type) : (choice SL_RLC_ModeIndication_r16__sl_Mode_r16__list) :=
  match z with
   | SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_AM_Mode_r16 t => existT _ 0 t
  | SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_UM_Mode_r16 t => existT _ 1 t
  end.
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__g := (fun n => typ_set (get_nth_typ SL_RLC_ModeIndication_r16__sl_Mode_r16__list n)).
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__F2 (y : choice SL_RLC_ModeIndication_r16__sl_Mode_r16__list) : SL_RLC_ModeIndication_r16__sl_Mode_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_RLC_ModeIndication_r16__sl_Mode_r16__g n -> SL_RLC_ModeIndication_r16__sl_Mode_r16__Type) with
    | 0 => fun (t : unit) => SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_AM_Mode_r16 t 
    | 1 => fun (t : unit) => SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_UM_Mode_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_RLC_ModeIndication_r16__sl_Mode_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_RLC_ModeIndication_r16__sl_Mode_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_RLC_ModeIndication_r16__sl_Mode_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_RLC_ModeIndication_r16__sl_Mode_r16__Type with end) n0
           end t0).

Lemma SL_RLC_ModeIndication_r16__sl_Mode_r16__helper2 :  forall (y : SL_RLC_ModeIndication_r16__sl_Mode_r16__Type), SL_RLC_ModeIndication_r16__sl_Mode_r16__cond y -> choice_cond SL_RLC_ModeIndication_r16__sl_Mode_r16__list (SL_RLC_ModeIndication_r16__sl_Mode_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_RLC_ModeIndication_r16__sl_Mode_r16__helper3 :  forall (y : SL_RLC_ModeIndication_r16__sl_Mode_r16__Type), SL_RLC_ModeIndication_r16__sl_Mode_r16__F2 (SL_RLC_ModeIndication_r16__sl_Mode_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_RLC_ModeIndication_r16__sl_Mode_r16__helper4 : (forall b : choice SL_RLC_ModeIndication_r16__sl_Mode_r16__list, choice_cond SL_RLC_ModeIndication_r16__sl_Mode_r16__list b -> SL_RLC_ModeIndication_r16__sl_Mode_r16__cond (SL_RLC_ModeIndication_r16__sl_Mode_r16__F2 b) /\ SL_RLC_ModeIndication_r16__sl_Mode_r16__F1 (SL_RLC_ModeIndication_r16__sl_Mode_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_RLC_ModeIndication_r16__sl_Mode_r16__F1 SL_RLC_ModeIndication_r16__sl_Mode_r16__F2.
Definition SL_RLC_ModeIndication_r16__sl_Mode_r16__Format : T_Format SL_RLC_ModeIndication_r16__sl_Mode_r16__Type SL_RLC_ModeIndication_r16__sl_Mode_r16__cond :=
  (* Eval compute in *) proj2_format SL_RLC_ModeIndication_r16__sl_Mode_r16__cond SL_RLC_ModeIndication_r16__sl_Mode_r16__list__Format SL_RLC_ModeIndication_r16__sl_Mode_r16__F1 SL_RLC_ModeIndication_r16__sl_Mode_r16__F2 SL_RLC_ModeIndication_r16__sl_Mode_r16__helper2 SL_RLC_ModeIndication_r16__sl_Mode_r16__helper3 SL_RLC_ModeIndication_r16__sl_Mode_r16__helper4.
Opaque SL_RLC_ModeIndication_r16__sl_Mode_r16__cond SL_RLC_ModeIndication_r16__sl_Mode_r16__Format.

Definition SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Format : T_Format SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__cond := seq_of_format SL_QoS_Info_r16__Format 1 maxNrofSL_QFIsPerDest_r16 SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__helper1 SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__helper2.

Opaque SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__cond SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Format.


Definition SL_RLC_ModeIndication_r16__Format_Type := Eval cbn in seq_format_prod SL_RLC_ModeIndication_r16__list.
Definition SL_RLC_ModeIndication_r16__Format_list : SL_RLC_ModeIndication_r16__Format_Type :=
  (SL_RLC_ModeIndication_r16__sl_Mode_r16__Format, (SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Format, unit_format)).
Definition SL_RLC_ModeIndication_r16__list__Format := (*Eval compute in *) seq_format SL_RLC_ModeIndication_r16__list SL_RLC_ModeIndication_r16__Format_list.
Definition SL_RLC_ModeIndication_r16__F1 z :=
  (SL_RLC_ModeIndication_r16__sl_Mode_r16 z, (SL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16 z, tt)).
Definition SL_RLC_ModeIndication_r16__F2 (y : seq_type SL_RLC_ModeIndication_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SL_RLC_ModeIndication_r16__Type i0 i1
  end.
Lemma SL_RLC_ModeIndication_r16__F1F2_cond (z : SL_RLC_ModeIndication_r16__Type)
  : SL_RLC_ModeIndication_r16__cond z ->
  (seq_cond SL_RLC_ModeIndication_r16__list (SL_RLC_ModeIndication_r16__F1 z)).
intro H. unfold SL_RLC_ModeIndication_r16__cond in H. simpl. auto. Qed.
Lemma SL_RLC_ModeIndication_r16__F1F2_cond2 (z : SL_RLC_ModeIndication_r16__Type)
 : SL_RLC_ModeIndication_r16__F2 (SL_RLC_ModeIndication_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_RLC_ModeIndication_r16__F2F1_cond (y : seq_type SL_RLC_ModeIndication_r16__list)
  : seq_cond SL_RLC_ModeIndication_r16__list y ->
 (SL_RLC_ModeIndication_r16__cond (SL_RLC_ModeIndication_r16__F2 y)) /\  SL_RLC_ModeIndication_r16__F1 (SL_RLC_ModeIndication_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_RLC_ModeIndication_r16__cond. simpl in *. auto.
 - simpl. unfold SL_RLC_ModeIndication_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_RLC_ModeIndication_r16__Format : T_Format SL_RLC_ModeIndication_r16__Type SL_RLC_ModeIndication_r16__cond :=
        proj2_format  SL_RLC_ModeIndication_r16__cond SL_RLC_ModeIndication_r16__list__Format
    SL_RLC_ModeIndication_r16__F1 SL_RLC_ModeIndication_r16__F2 SL_RLC_ModeIndication_r16__F1F2_cond  SL_RLC_ModeIndication_r16__F1F2_cond2 SL_RLC_ModeIndication_r16__F2F1_cond.
Opaque SL_RLC_ModeIndication_r16__cond SL_RLC_ModeIndication_r16__Format.

