Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma MeasTriggerQuantityOffset__rsrp__helper1 : (-30 <= 30)%Z.  lia. Qed.
Lemma MeasTriggerQuantityOffset__rsrp__helper2 : to_bit_sz (Z.to_nat (30 - -30)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (30 - -30))%Z). { apply Zorder.Zle_minus_le_0. apply MeasTriggerQuantityOffset__rsrp__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasTriggerQuantityOffset__rsrp__Type := Z.
Definition MeasTriggerQuantityOffset__rsrp__cond := (fun z => (-30 <= z <= 30)%Z).
Lemma MeasTriggerQuantityOffset__rsrq__helper1 : (-30 <= 30)%Z.  lia. Qed.
Lemma MeasTriggerQuantityOffset__rsrq__helper2 : to_bit_sz (Z.to_nat (30 - -30)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (30 - -30))%Z). { apply Zorder.Zle_minus_le_0. apply MeasTriggerQuantityOffset__rsrq__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasTriggerQuantityOffset__rsrq__Type := Z.
Definition MeasTriggerQuantityOffset__rsrq__cond := (fun z => (-30 <= z <= 30)%Z).
Lemma MeasTriggerQuantityOffset__sinr__helper1 : (-30 <= 30)%Z.  lia. Qed.
Lemma MeasTriggerQuantityOffset__sinr__helper2 : to_bit_sz (Z.to_nat (30 - -30)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (30 - -30))%Z). { apply Zorder.Zle_minus_le_0. apply MeasTriggerQuantityOffset__sinr__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasTriggerQuantityOffset__sinr__Type := Z.
Definition MeasTriggerQuantityOffset__sinr__cond := (fun z => (-30 <= z <= 30)%Z).

Inductive MeasTriggerQuantityOffset__Type : Set :=
  | MeasTriggerQuantityOffset__rsrp : Z -> MeasTriggerQuantityOffset__Type
  | MeasTriggerQuantityOffset__rsrq : Z -> MeasTriggerQuantityOffset__Type
  | MeasTriggerQuantityOffset__sinr : Z -> MeasTriggerQuantityOffset__Type
.
Definition MeasTriggerQuantityOffset__list : list typ := (
typ_cons Z MeasTriggerQuantityOffset__rsrp__cond ::
typ_cons Z MeasTriggerQuantityOffset__rsrq__cond ::
typ_cons Z MeasTriggerQuantityOffset__sinr__cond ::
 nil).
Definition MeasTriggerQuantityOffset__cond (c : MeasTriggerQuantityOffset__Type) := 
  match c with
  | MeasTriggerQuantityOffset__rsrp t => MeasTriggerQuantityOffset__rsrp__cond t 
  | MeasTriggerQuantityOffset__rsrq t => MeasTriggerQuantityOffset__rsrq__cond t 
  | MeasTriggerQuantityOffset__sinr t => MeasTriggerQuantityOffset__sinr__cond t 
  end.

Lemma MeasTriggerQuantityOffset__len_helper1 : to_bit_sz (length MeasTriggerQuantityOffset__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasTriggerQuantityOffset__len_helper2 : 2 <= length2 MeasTriggerQuantityOffset__list.
 simpl. lia. Qed.

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
Definition MeasTriggerQuantityOffset__rsrp__Format : T_Format Z MeasTriggerQuantityOffset__rsrp__cond :=
 ranged_int_format (-30) (30) MeasTriggerQuantityOffset__rsrp__helper1 MeasTriggerQuantityOffset__rsrp__helper2.

Opaque MeasTriggerQuantityOffset__rsrp__cond MeasTriggerQuantityOffset__rsrp__Format.

Definition MeasTriggerQuantityOffset__rsrq__Format : T_Format Z MeasTriggerQuantityOffset__rsrq__cond :=
 ranged_int_format (-30) (30) MeasTriggerQuantityOffset__rsrq__helper1 MeasTriggerQuantityOffset__rsrq__helper2.

Opaque MeasTriggerQuantityOffset__rsrq__cond MeasTriggerQuantityOffset__rsrq__Format.

Definition MeasTriggerQuantityOffset__sinr__Format : T_Format Z MeasTriggerQuantityOffset__sinr__cond :=
 ranged_int_format (-30) (30) MeasTriggerQuantityOffset__sinr__helper1 MeasTriggerQuantityOffset__sinr__helper2.

Opaque MeasTriggerQuantityOffset__sinr__cond MeasTriggerQuantityOffset__sinr__Format.


Definition MeasTriggerQuantityOffset__Format_Type := Eval cbn in get_formats MeasTriggerQuantityOffset__list.
Definition MeasTriggerQuantityOffset__Format_list : MeasTriggerQuantityOffset__Format_Type :=
  (MeasTriggerQuantityOffset__rsrp__Format, (MeasTriggerQuantityOffset__rsrq__Format, (MeasTriggerQuantityOffset__sinr__Format, unit__Format))).
Definition MeasTriggerQuantityOffset__list__Format := Eval compute in choice_format MeasTriggerQuantityOffset__list MeasTriggerQuantityOffset__len_helper1 MeasTriggerQuantityOffset__len_helper2  MeasTriggerQuantityOffset__Format_list.
Definition MeasTriggerQuantityOffset__F1 (z : MeasTriggerQuantityOffset__Type) : (choice MeasTriggerQuantityOffset__list) :=
  match z with
   | MeasTriggerQuantityOffset__rsrp t => existT _ 0 t
  | MeasTriggerQuantityOffset__rsrq t => existT _ 1 t
  | MeasTriggerQuantityOffset__sinr t => existT _ 2 t
  end.
Definition MeasTriggerQuantityOffset__g := (fun n => typ_set (get_nth_typ MeasTriggerQuantityOffset__list n)).
Definition MeasTriggerQuantityOffset__F2 (y : choice MeasTriggerQuantityOffset__list) : MeasTriggerQuantityOffset__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasTriggerQuantityOffset__g n -> MeasTriggerQuantityOffset__Type) with
    | 0 => fun (t : Z) => MeasTriggerQuantityOffset__rsrp t 
    | 1 => fun (t : Z) => MeasTriggerQuantityOffset__rsrq t 
    | 2 => fun (t : Z) => MeasTriggerQuantityOffset__sinr t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : MeasTriggerQuantityOffset__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ MeasTriggerQuantityOffset__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasTriggerQuantityOffset__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return MeasTriggerQuantityOffset__Type with end) n0
           end t0).

Lemma MeasTriggerQuantityOffset__helper2 :  forall (y : MeasTriggerQuantityOffset__Type), MeasTriggerQuantityOffset__cond y -> choice_cond MeasTriggerQuantityOffset__list (MeasTriggerQuantityOffset__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasTriggerQuantityOffset__helper3 :  forall (y : MeasTriggerQuantityOffset__Type), MeasTriggerQuantityOffset__F2 (MeasTriggerQuantityOffset__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasTriggerQuantityOffset__helper4 : (forall b : choice MeasTriggerQuantityOffset__list, choice_cond MeasTriggerQuantityOffset__list b -> MeasTriggerQuantityOffset__cond (MeasTriggerQuantityOffset__F2 b) /\ MeasTriggerQuantityOffset__F1 (MeasTriggerQuantityOffset__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasTriggerQuantityOffset__F1 MeasTriggerQuantityOffset__F2.
Definition MeasTriggerQuantityOffset__Format : T_Format MeasTriggerQuantityOffset__Type MeasTriggerQuantityOffset__cond :=
  (* Eval compute in *) proj2_format MeasTriggerQuantityOffset__cond MeasTriggerQuantityOffset__list__Format MeasTriggerQuantityOffset__F1 MeasTriggerQuantityOffset__F2 MeasTriggerQuantityOffset__helper2 MeasTriggerQuantityOffset__helper3 MeasTriggerQuantityOffset__helper4.
Opaque MeasTriggerQuantityOffset__cond MeasTriggerQuantityOffset__Format.

