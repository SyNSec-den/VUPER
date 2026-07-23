Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Record VarPendingRNA_Update__Type : Set :=
  make__VarPendingRNA_Update__Type {
    VarPendingRNA_Update__pendingRNA_Update : option bool ;
}.
Definition VarPendingRNA_Update__list := (
 Opt bool (fun _ => True) ::
 nil).
Definition VarPendingRNA_Update__cond z := 
  opt_cond (fun _ => True) (VarPendingRNA_Update__pendingRNA_Update z) /\
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

Definition VarPendingRNA_Update__Format_Type := Eval cbn in seq_format_prod VarPendingRNA_Update__list.
Definition VarPendingRNA_Update__Format_list : VarPendingRNA_Update__Format_Type :=
  (bool__Format, unit_format).
Definition VarPendingRNA_Update__list__Format := (*Eval compute in *) seq_format VarPendingRNA_Update__list VarPendingRNA_Update__Format_list.
Definition VarPendingRNA_Update__F1 z :=
  (VarPendingRNA_Update__pendingRNA_Update z, tt).
Definition VarPendingRNA_Update__F2 (y : seq_type VarPendingRNA_Update__list) :=
  match y with
  | (i0, _)=>
    make__VarPendingRNA_Update__Type i0
  end.
Lemma VarPendingRNA_Update__F1F2_cond (z : VarPendingRNA_Update__Type)
  : VarPendingRNA_Update__cond z ->
  (seq_cond VarPendingRNA_Update__list (VarPendingRNA_Update__F1 z)).
intro H. unfold VarPendingRNA_Update__cond in H. simpl. auto. Qed.
Lemma VarPendingRNA_Update__F1F2_cond2 (z : VarPendingRNA_Update__Type)
 : VarPendingRNA_Update__F2 (VarPendingRNA_Update__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarPendingRNA_Update__F2F1_cond (y : seq_type VarPendingRNA_Update__list)
  : seq_cond VarPendingRNA_Update__list y ->
 (VarPendingRNA_Update__cond (VarPendingRNA_Update__F2 y)) /\  VarPendingRNA_Update__F1 (VarPendingRNA_Update__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarPendingRNA_Update__cond. simpl in *. auto.
 - simpl. unfold VarPendingRNA_Update__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarPendingRNA_Update__Format : T_Format VarPendingRNA_Update__Type VarPendingRNA_Update__cond :=
        proj2_format  VarPendingRNA_Update__cond VarPendingRNA_Update__list__Format
    VarPendingRNA_Update__F1 VarPendingRNA_Update__F2 VarPendingRNA_Update__F1F2_cond  VarPendingRNA_Update__F1F2_cond2 VarPendingRNA_Update__F2F1_cond.
Opaque VarPendingRNA_Update__cond VarPendingRNA_Update__Format.

