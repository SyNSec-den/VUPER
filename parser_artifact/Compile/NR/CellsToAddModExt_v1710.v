Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Type : Set :=
 | CellsToAddModExt_v1710__ntn_PolarizationDL_r17__rhcp
 | CellsToAddModExt_v1710__ntn_PolarizationDL_r17__lhcp
 | CellsToAddModExt_v1710__ntn_PolarizationDL_r17__linear
.
Definition CellsToAddModExt_v1710__ntn_PolarizationDL_r17__cond := (fun (_ : CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Type) => True).
Lemma CellsToAddModExt_v1710__ntn_PolarizationDL_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellsToAddModExt_v1710__ntn_PolarizationDL_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CellsToAddModExt_v1710__ntn_PolarizationDL_r17__nat__helper.

Definition CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1 t :=
  match t with
  | CellsToAddModExt_v1710__ntn_PolarizationDL_r17__rhcp => 0
  | CellsToAddModExt_v1710__ntn_PolarizationDL_r17__lhcp => 1
  | CellsToAddModExt_v1710__ntn_PolarizationDL_r17__linear => 2
  end.
Definition CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F2 n :=
  match n with
  | 0 => CellsToAddModExt_v1710__ntn_PolarizationDL_r17__rhcp
  | 1 => CellsToAddModExt_v1710__ntn_PolarizationDL_r17__lhcp
  | 2 => CellsToAddModExt_v1710__ntn_PolarizationDL_r17__linear
  | _ => CellsToAddModExt_v1710__ntn_PolarizationDL_r17__rhcp
  end.
Lemma CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1F2 : forall x : CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Type, (CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1 x <= 2) /\ CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F2 (CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1 x) = x. imp_solve. Qed.
Lemma CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F2F1 : forall (y : nat) (H : y <= 2), CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1 (CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Type : Set :=
 | CellsToAddModExt_v1710__ntn_PolarizationUL_r17__rhcp
 | CellsToAddModExt_v1710__ntn_PolarizationUL_r17__lhcp
 | CellsToAddModExt_v1710__ntn_PolarizationUL_r17__linear
.
Definition CellsToAddModExt_v1710__ntn_PolarizationUL_r17__cond := (fun (_ : CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Type) => True).
Lemma CellsToAddModExt_v1710__ntn_PolarizationUL_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellsToAddModExt_v1710__ntn_PolarizationUL_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CellsToAddModExt_v1710__ntn_PolarizationUL_r17__nat__helper.

Definition CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1 t :=
  match t with
  | CellsToAddModExt_v1710__ntn_PolarizationUL_r17__rhcp => 0
  | CellsToAddModExt_v1710__ntn_PolarizationUL_r17__lhcp => 1
  | CellsToAddModExt_v1710__ntn_PolarizationUL_r17__linear => 2
  end.
Definition CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F2 n :=
  match n with
  | 0 => CellsToAddModExt_v1710__ntn_PolarizationUL_r17__rhcp
  | 1 => CellsToAddModExt_v1710__ntn_PolarizationUL_r17__lhcp
  | 2 => CellsToAddModExt_v1710__ntn_PolarizationUL_r17__linear
  | _ => CellsToAddModExt_v1710__ntn_PolarizationUL_r17__rhcp
  end.
Lemma CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1F2 : forall x : CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Type, (CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1 x <= 2) /\ CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F2 (CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1 x) = x. imp_solve. Qed.
Lemma CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F2F1 : forall (y : nat) (H : y <= 2), CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1 (CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F2 y) = y. enum_solve H y. Qed.

Record CellsToAddModExt_v1710__Type : Set :=
  make__CellsToAddModExt_v1710__Type {
    CellsToAddModExt_v1710__ntn_PolarizationDL_r17 : option CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Type ;
    CellsToAddModExt_v1710__ntn_PolarizationUL_r17 : option CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Type ;
}.
Definition CellsToAddModExt_v1710__list := (
 Opt CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Type CellsToAddModExt_v1710__ntn_PolarizationDL_r17__cond ::
 Opt CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Type CellsToAddModExt_v1710__ntn_PolarizationUL_r17__cond ::
 nil).
Definition CellsToAddModExt_v1710__cond z := 
  opt_cond CellsToAddModExt_v1710__ntn_PolarizationDL_r17__cond (CellsToAddModExt_v1710__ntn_PolarizationDL_r17 z) /\
  opt_cond CellsToAddModExt_v1710__ntn_PolarizationUL_r17__cond (CellsToAddModExt_v1710__ntn_PolarizationUL_r17 z) /\
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
Definition CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Format : T_Format CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellsToAddModExt_v1710__ntn_PolarizationDL_r17__nat__Format CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1 CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F2 CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F1F2 CellsToAddModExt_v1710__ntn_PolarizationDL_r17__F2F1.

Opaque CellsToAddModExt_v1710__ntn_PolarizationDL_r17__cond CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Format.

Definition CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Format : T_Format CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellsToAddModExt_v1710__ntn_PolarizationUL_r17__nat__Format CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1 CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F2 CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F1F2 CellsToAddModExt_v1710__ntn_PolarizationUL_r17__F2F1.

Opaque CellsToAddModExt_v1710__ntn_PolarizationUL_r17__cond CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Format.


Definition CellsToAddModExt_v1710__Format_Type := Eval cbn in seq_format_prod CellsToAddModExt_v1710__list.
Definition CellsToAddModExt_v1710__Format_list : CellsToAddModExt_v1710__Format_Type :=
  (CellsToAddModExt_v1710__ntn_PolarizationDL_r17__Format, (CellsToAddModExt_v1710__ntn_PolarizationUL_r17__Format, unit_format)).
Definition CellsToAddModExt_v1710__list__Format := (*Eval compute in *) seq_format CellsToAddModExt_v1710__list CellsToAddModExt_v1710__Format_list.
Definition CellsToAddModExt_v1710__F1 z :=
  (CellsToAddModExt_v1710__ntn_PolarizationDL_r17 z, (CellsToAddModExt_v1710__ntn_PolarizationUL_r17 z, tt)).
Definition CellsToAddModExt_v1710__F2 (y : seq_type CellsToAddModExt_v1710__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CellsToAddModExt_v1710__Type i0 i1
  end.
Lemma CellsToAddModExt_v1710__F1F2_cond (z : CellsToAddModExt_v1710__Type)
  : CellsToAddModExt_v1710__cond z ->
  (seq_cond CellsToAddModExt_v1710__list (CellsToAddModExt_v1710__F1 z)).
intro H. unfold CellsToAddModExt_v1710__cond in H. simpl. auto. Qed.
Lemma CellsToAddModExt_v1710__F1F2_cond2 (z : CellsToAddModExt_v1710__Type)
 : CellsToAddModExt_v1710__F2 (CellsToAddModExt_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellsToAddModExt_v1710__F2F1_cond (y : seq_type CellsToAddModExt_v1710__list)
  : seq_cond CellsToAddModExt_v1710__list y ->
 (CellsToAddModExt_v1710__cond (CellsToAddModExt_v1710__F2 y)) /\  CellsToAddModExt_v1710__F1 (CellsToAddModExt_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellsToAddModExt_v1710__cond. simpl in *. auto.
 - simpl. unfold CellsToAddModExt_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellsToAddModExt_v1710__Format : T_Format CellsToAddModExt_v1710__Type CellsToAddModExt_v1710__cond :=
        proj2_format  CellsToAddModExt_v1710__cond CellsToAddModExt_v1710__list__Format
    CellsToAddModExt_v1710__F1 CellsToAddModExt_v1710__F2 CellsToAddModExt_v1710__F1F2_cond  CellsToAddModExt_v1710__F1F2_cond2 CellsToAddModExt_v1710__F2F1_cond.
Opaque CellsToAddModExt_v1710__cond CellsToAddModExt_v1710__Format.

