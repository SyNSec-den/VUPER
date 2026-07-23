Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Require Import NR.BH_LogicalChannelIdentity_Ext_r16.

Opaque BH_LogicalChannelIdentity_Ext_r16__cond BH_LogicalChannelIdentity_Ext_r16__Format.


Inductive BH_LogicalChannelIdentity_r16__Type : Set :=
  | BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentity_r16 : LogicalChannelIdentity__Type -> BH_LogicalChannelIdentity_r16__Type
  | BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentityExt_r16 : BH_LogicalChannelIdentity_Ext_r16__Type -> BH_LogicalChannelIdentity_r16__Type
.
Definition BH_LogicalChannelIdentity_r16__list : list typ := (
typ_cons LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
typ_cons BH_LogicalChannelIdentity_Ext_r16__Type BH_LogicalChannelIdentity_Ext_r16__cond ::
 nil).
Definition BH_LogicalChannelIdentity_r16__cond (c : BH_LogicalChannelIdentity_r16__Type) := 
  match c with
  | BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentity_r16 t => LogicalChannelIdentity__cond t 
  | BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentityExt_r16 t => BH_LogicalChannelIdentity_Ext_r16__cond t 
  end.

Lemma BH_LogicalChannelIdentity_r16__len_helper1 : to_bit_sz (length BH_LogicalChannelIdentity_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BH_LogicalChannelIdentity_r16__len_helper2 : 2 <= length2 BH_LogicalChannelIdentity_r16__list.
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

Definition BH_LogicalChannelIdentity_r16__Format_Type := Eval cbn in get_formats BH_LogicalChannelIdentity_r16__list.
Definition BH_LogicalChannelIdentity_r16__Format_list : BH_LogicalChannelIdentity_r16__Format_Type :=
  (LogicalChannelIdentity__Format, (BH_LogicalChannelIdentity_Ext_r16__Format, unit__Format)).
Definition BH_LogicalChannelIdentity_r16__list__Format := Eval compute in choice_format BH_LogicalChannelIdentity_r16__list BH_LogicalChannelIdentity_r16__len_helper1 BH_LogicalChannelIdentity_r16__len_helper2  BH_LogicalChannelIdentity_r16__Format_list.
Definition BH_LogicalChannelIdentity_r16__F1 (z : BH_LogicalChannelIdentity_r16__Type) : (choice BH_LogicalChannelIdentity_r16__list) :=
  match z with
   | BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentity_r16 t => existT _ 0 t
  | BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentityExt_r16 t => existT _ 1 t
  end.
Definition BH_LogicalChannelIdentity_r16__g := (fun n => typ_set (get_nth_typ BH_LogicalChannelIdentity_r16__list n)).
Definition BH_LogicalChannelIdentity_r16__F2 (y : choice BH_LogicalChannelIdentity_r16__list) : BH_LogicalChannelIdentity_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BH_LogicalChannelIdentity_r16__g n -> BH_LogicalChannelIdentity_r16__Type) with
    | 0 => fun (t : LogicalChannelIdentity__Type) => BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentity_r16 t 
    | 1 => fun (t : BH_LogicalChannelIdentity_Ext_r16__Type) => BH_LogicalChannelIdentity_r16__bh_LogicalChannelIdentityExt_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BH_LogicalChannelIdentity_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BH_LogicalChannelIdentity_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BH_LogicalChannelIdentity_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BH_LogicalChannelIdentity_r16__Type with end) n0
           end t0).

Lemma BH_LogicalChannelIdentity_r16__helper2 :  forall (y : BH_LogicalChannelIdentity_r16__Type), BH_LogicalChannelIdentity_r16__cond y -> choice_cond BH_LogicalChannelIdentity_r16__list (BH_LogicalChannelIdentity_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BH_LogicalChannelIdentity_r16__helper3 :  forall (y : BH_LogicalChannelIdentity_r16__Type), BH_LogicalChannelIdentity_r16__F2 (BH_LogicalChannelIdentity_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BH_LogicalChannelIdentity_r16__helper4 : (forall b : choice BH_LogicalChannelIdentity_r16__list, choice_cond BH_LogicalChannelIdentity_r16__list b -> BH_LogicalChannelIdentity_r16__cond (BH_LogicalChannelIdentity_r16__F2 b) /\ BH_LogicalChannelIdentity_r16__F1 (BH_LogicalChannelIdentity_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BH_LogicalChannelIdentity_r16__F1 BH_LogicalChannelIdentity_r16__F2.
Definition BH_LogicalChannelIdentity_r16__Format : T_Format BH_LogicalChannelIdentity_r16__Type BH_LogicalChannelIdentity_r16__cond :=
  (* Eval compute in *) proj2_format BH_LogicalChannelIdentity_r16__cond BH_LogicalChannelIdentity_r16__list__Format BH_LogicalChannelIdentity_r16__F1 BH_LogicalChannelIdentity_r16__F2 BH_LogicalChannelIdentity_r16__helper2 BH_LogicalChannelIdentity_r16__helper3 BH_LogicalChannelIdentity_r16__helper4.
Opaque BH_LogicalChannelIdentity_r16__cond BH_LogicalChannelIdentity_r16__Format.

