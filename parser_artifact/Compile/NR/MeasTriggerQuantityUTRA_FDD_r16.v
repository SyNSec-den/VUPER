Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__helper1 : (-5 <= 91)%Z.  lia. Qed.
Lemma MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__helper2 : to_bit_sz (Z.to_nat (91 - -5)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (91 - -5))%Z). { apply Zorder.Zle_minus_le_0. apply MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__Type := Z.
Definition MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__cond := (fun z => (-5 <= z <= 91)%Z).
Lemma MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__helper1 : (0 <= 49)%Z.  lia. Qed.
Lemma MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__helper2 : to_bit_sz (Z.to_nat (49 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (49 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__Type := Z.
Definition MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__cond := (fun z => (0 <= z <= 49)%Z).

Inductive MeasTriggerQuantityUTRA_FDD_r16__Type : Set :=
  | MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16 : Z -> MeasTriggerQuantityUTRA_FDD_r16__Type
  | MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16 : Z -> MeasTriggerQuantityUTRA_FDD_r16__Type
.
Definition MeasTriggerQuantityUTRA_FDD_r16__list : list typ := (
typ_cons Z MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__cond ::
typ_cons Z MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__cond ::
 nil).
Definition MeasTriggerQuantityUTRA_FDD_r16__cond (c : MeasTriggerQuantityUTRA_FDD_r16__Type) := 
  match c with
  | MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16 t => MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__cond t 
  | MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16 t => MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__cond t 
  end.

Lemma MeasTriggerQuantityUTRA_FDD_r16__len_helper1 : to_bit_sz (length MeasTriggerQuantityUTRA_FDD_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasTriggerQuantityUTRA_FDD_r16__len_helper2 : 2 <= length2 MeasTriggerQuantityUTRA_FDD_r16__list.
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
Definition MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__Format : T_Format Z MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__cond :=
 ranged_int_format (-5) (91) MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__helper1 MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__helper2.

Opaque MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__cond MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__Format.

Definition MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__Format : T_Format Z MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__cond :=
 ranged_int_format (0) (49) MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__helper1 MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__helper2.

Opaque MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__cond MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__Format.


Definition MeasTriggerQuantityUTRA_FDD_r16__Format_Type := Eval cbn in get_formats MeasTriggerQuantityUTRA_FDD_r16__list.
Definition MeasTriggerQuantityUTRA_FDD_r16__Format_list : MeasTriggerQuantityUTRA_FDD_r16__Format_Type :=
  (MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16__Format, (MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16__Format, unit__Format)).
Definition MeasTriggerQuantityUTRA_FDD_r16__list__Format := Eval compute in choice_format MeasTriggerQuantityUTRA_FDD_r16__list MeasTriggerQuantityUTRA_FDD_r16__len_helper1 MeasTriggerQuantityUTRA_FDD_r16__len_helper2  MeasTriggerQuantityUTRA_FDD_r16__Format_list.
Definition MeasTriggerQuantityUTRA_FDD_r16__F1 (z : MeasTriggerQuantityUTRA_FDD_r16__Type) : (choice MeasTriggerQuantityUTRA_FDD_r16__list) :=
  match z with
   | MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16 t => existT _ 0 t
  | MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16 t => existT _ 1 t
  end.
Definition MeasTriggerQuantityUTRA_FDD_r16__g := (fun n => typ_set (get_nth_typ MeasTriggerQuantityUTRA_FDD_r16__list n)).
Definition MeasTriggerQuantityUTRA_FDD_r16__F2 (y : choice MeasTriggerQuantityUTRA_FDD_r16__list) : MeasTriggerQuantityUTRA_FDD_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasTriggerQuantityUTRA_FDD_r16__g n -> MeasTriggerQuantityUTRA_FDD_r16__Type) with
    | 0 => fun (t : Z) => MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_RSCP_r16 t 
    | 1 => fun (t : Z) => MeasTriggerQuantityUTRA_FDD_r16__utra_FDD_EcN0_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasTriggerQuantityUTRA_FDD_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasTriggerQuantityUTRA_FDD_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasTriggerQuantityUTRA_FDD_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasTriggerQuantityUTRA_FDD_r16__Type with end) n0
           end t0).

Lemma MeasTriggerQuantityUTRA_FDD_r16__helper2 :  forall (y : MeasTriggerQuantityUTRA_FDD_r16__Type), MeasTriggerQuantityUTRA_FDD_r16__cond y -> choice_cond MeasTriggerQuantityUTRA_FDD_r16__list (MeasTriggerQuantityUTRA_FDD_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasTriggerQuantityUTRA_FDD_r16__helper3 :  forall (y : MeasTriggerQuantityUTRA_FDD_r16__Type), MeasTriggerQuantityUTRA_FDD_r16__F2 (MeasTriggerQuantityUTRA_FDD_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasTriggerQuantityUTRA_FDD_r16__helper4 : (forall b : choice MeasTriggerQuantityUTRA_FDD_r16__list, choice_cond MeasTriggerQuantityUTRA_FDD_r16__list b -> MeasTriggerQuantityUTRA_FDD_r16__cond (MeasTriggerQuantityUTRA_FDD_r16__F2 b) /\ MeasTriggerQuantityUTRA_FDD_r16__F1 (MeasTriggerQuantityUTRA_FDD_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasTriggerQuantityUTRA_FDD_r16__F1 MeasTriggerQuantityUTRA_FDD_r16__F2.
Definition MeasTriggerQuantityUTRA_FDD_r16__Format : T_Format MeasTriggerQuantityUTRA_FDD_r16__Type MeasTriggerQuantityUTRA_FDD_r16__cond :=
  (* Eval compute in *) proj2_format MeasTriggerQuantityUTRA_FDD_r16__cond MeasTriggerQuantityUTRA_FDD_r16__list__Format MeasTriggerQuantityUTRA_FDD_r16__F1 MeasTriggerQuantityUTRA_FDD_r16__F2 MeasTriggerQuantityUTRA_FDD_r16__helper2 MeasTriggerQuantityUTRA_FDD_r16__helper3 MeasTriggerQuantityUTRA_FDD_r16__helper4.
Opaque MeasTriggerQuantityUTRA_FDD_r16__cond MeasTriggerQuantityUTRA_FDD_r16__Format.

