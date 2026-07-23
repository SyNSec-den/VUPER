Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_SyncAllowed_r16__gnss_Sync_r16__Type : Set :=
 | SL_SyncAllowed_r16__gnss_Sync_r16__true
.
Definition SL_SyncAllowed_r16__gnss_Sync_r16__cond := (fun (_ : SL_SyncAllowed_r16__gnss_Sync_r16__Type) => True).
Lemma SL_SyncAllowed_r16__gnss_Sync_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SyncAllowed_r16__gnss_Sync_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_SyncAllowed_r16__gnss_Sync_r16__nat__helper.

Definition SL_SyncAllowed_r16__gnss_Sync_r16__F1 t :=
  match t with
  | SL_SyncAllowed_r16__gnss_Sync_r16__true => 0
  end.
Definition SL_SyncAllowed_r16__gnss_Sync_r16__F2 n :=
  match n with
  | 0 => SL_SyncAllowed_r16__gnss_Sync_r16__true
  | _ => SL_SyncAllowed_r16__gnss_Sync_r16__true
  end.
Lemma SL_SyncAllowed_r16__gnss_Sync_r16__F1F2 : forall x : SL_SyncAllowed_r16__gnss_Sync_r16__Type, (SL_SyncAllowed_r16__gnss_Sync_r16__F1 x <= 0) /\ SL_SyncAllowed_r16__gnss_Sync_r16__F2 (SL_SyncAllowed_r16__gnss_Sync_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_SyncAllowed_r16__gnss_Sync_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_SyncAllowed_r16__gnss_Sync_r16__F1 (SL_SyncAllowed_r16__gnss_Sync_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_SyncAllowed_r16__gnbEnb_Sync_r16__Type : Set :=
 | SL_SyncAllowed_r16__gnbEnb_Sync_r16__true
.
Definition SL_SyncAllowed_r16__gnbEnb_Sync_r16__cond := (fun (_ : SL_SyncAllowed_r16__gnbEnb_Sync_r16__Type) => True).
Lemma SL_SyncAllowed_r16__gnbEnb_Sync_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SyncAllowed_r16__gnbEnb_Sync_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_SyncAllowed_r16__gnbEnb_Sync_r16__nat__helper.

Definition SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1 t :=
  match t with
  | SL_SyncAllowed_r16__gnbEnb_Sync_r16__true => 0
  end.
Definition SL_SyncAllowed_r16__gnbEnb_Sync_r16__F2 n :=
  match n with
  | 0 => SL_SyncAllowed_r16__gnbEnb_Sync_r16__true
  | _ => SL_SyncAllowed_r16__gnbEnb_Sync_r16__true
  end.
Lemma SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1F2 : forall x : SL_SyncAllowed_r16__gnbEnb_Sync_r16__Type, (SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1 x <= 0) /\ SL_SyncAllowed_r16__gnbEnb_Sync_r16__F2 (SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_SyncAllowed_r16__gnbEnb_Sync_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1 (SL_SyncAllowed_r16__gnbEnb_Sync_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_SyncAllowed_r16__ue_Sync_r16__Type : Set :=
 | SL_SyncAllowed_r16__ue_Sync_r16__true
.
Definition SL_SyncAllowed_r16__ue_Sync_r16__cond := (fun (_ : SL_SyncAllowed_r16__ue_Sync_r16__Type) => True).
Lemma SL_SyncAllowed_r16__ue_Sync_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SyncAllowed_r16__ue_Sync_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_SyncAllowed_r16__ue_Sync_r16__nat__helper.

Definition SL_SyncAllowed_r16__ue_Sync_r16__F1 t :=
  match t with
  | SL_SyncAllowed_r16__ue_Sync_r16__true => 0
  end.
Definition SL_SyncAllowed_r16__ue_Sync_r16__F2 n :=
  match n with
  | 0 => SL_SyncAllowed_r16__ue_Sync_r16__true
  | _ => SL_SyncAllowed_r16__ue_Sync_r16__true
  end.
Lemma SL_SyncAllowed_r16__ue_Sync_r16__F1F2 : forall x : SL_SyncAllowed_r16__ue_Sync_r16__Type, (SL_SyncAllowed_r16__ue_Sync_r16__F1 x <= 0) /\ SL_SyncAllowed_r16__ue_Sync_r16__F2 (SL_SyncAllowed_r16__ue_Sync_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_SyncAllowed_r16__ue_Sync_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_SyncAllowed_r16__ue_Sync_r16__F1 (SL_SyncAllowed_r16__ue_Sync_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_SyncAllowed_r16__Type : Set :=
  make__SL_SyncAllowed_r16__Type {
    SL_SyncAllowed_r16__gnss_Sync_r16 : option SL_SyncAllowed_r16__gnss_Sync_r16__Type ;
    SL_SyncAllowed_r16__gnbEnb_Sync_r16 : option SL_SyncAllowed_r16__gnbEnb_Sync_r16__Type ;
    SL_SyncAllowed_r16__ue_Sync_r16 : option SL_SyncAllowed_r16__ue_Sync_r16__Type ;
}.
Definition SL_SyncAllowed_r16__list := (
 Opt SL_SyncAllowed_r16__gnss_Sync_r16__Type SL_SyncAllowed_r16__gnss_Sync_r16__cond ::
 Opt SL_SyncAllowed_r16__gnbEnb_Sync_r16__Type SL_SyncAllowed_r16__gnbEnb_Sync_r16__cond ::
 Opt SL_SyncAllowed_r16__ue_Sync_r16__Type SL_SyncAllowed_r16__ue_Sync_r16__cond ::
 nil).
Definition SL_SyncAllowed_r16__cond z := 
  opt_cond SL_SyncAllowed_r16__gnss_Sync_r16__cond (SL_SyncAllowed_r16__gnss_Sync_r16 z) /\
  opt_cond SL_SyncAllowed_r16__gnbEnb_Sync_r16__cond (SL_SyncAllowed_r16__gnbEnb_Sync_r16 z) /\
  opt_cond SL_SyncAllowed_r16__ue_Sync_r16__cond (SL_SyncAllowed_r16__ue_Sync_r16 z) /\
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
Definition SL_SyncAllowed_r16__gnss_Sync_r16__Format : T_Format SL_SyncAllowed_r16__gnss_Sync_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_SyncAllowed_r16__gnss_Sync_r16__nat__Format SL_SyncAllowed_r16__gnss_Sync_r16__F1 SL_SyncAllowed_r16__gnss_Sync_r16__F2 SL_SyncAllowed_r16__gnss_Sync_r16__F1F2 SL_SyncAllowed_r16__gnss_Sync_r16__F2F1.

Opaque SL_SyncAllowed_r16__gnss_Sync_r16__cond SL_SyncAllowed_r16__gnss_Sync_r16__Format.

Definition SL_SyncAllowed_r16__gnbEnb_Sync_r16__Format : T_Format SL_SyncAllowed_r16__gnbEnb_Sync_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_SyncAllowed_r16__gnbEnb_Sync_r16__nat__Format SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1 SL_SyncAllowed_r16__gnbEnb_Sync_r16__F2 SL_SyncAllowed_r16__gnbEnb_Sync_r16__F1F2 SL_SyncAllowed_r16__gnbEnb_Sync_r16__F2F1.

Opaque SL_SyncAllowed_r16__gnbEnb_Sync_r16__cond SL_SyncAllowed_r16__gnbEnb_Sync_r16__Format.

Definition SL_SyncAllowed_r16__ue_Sync_r16__Format : T_Format SL_SyncAllowed_r16__ue_Sync_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_SyncAllowed_r16__ue_Sync_r16__nat__Format SL_SyncAllowed_r16__ue_Sync_r16__F1 SL_SyncAllowed_r16__ue_Sync_r16__F2 SL_SyncAllowed_r16__ue_Sync_r16__F1F2 SL_SyncAllowed_r16__ue_Sync_r16__F2F1.

Opaque SL_SyncAllowed_r16__ue_Sync_r16__cond SL_SyncAllowed_r16__ue_Sync_r16__Format.


Definition SL_SyncAllowed_r16__Format_Type := Eval cbn in seq_format_prod SL_SyncAllowed_r16__list.
Definition SL_SyncAllowed_r16__Format_list : SL_SyncAllowed_r16__Format_Type :=
  (SL_SyncAllowed_r16__gnss_Sync_r16__Format, (SL_SyncAllowed_r16__gnbEnb_Sync_r16__Format, (SL_SyncAllowed_r16__ue_Sync_r16__Format, unit_format))).
Definition SL_SyncAllowed_r16__list__Format := (*Eval compute in *) seq_format SL_SyncAllowed_r16__list SL_SyncAllowed_r16__Format_list.
Definition SL_SyncAllowed_r16__F1 z :=
  (SL_SyncAllowed_r16__gnss_Sync_r16 z, (SL_SyncAllowed_r16__gnbEnb_Sync_r16 z, (SL_SyncAllowed_r16__ue_Sync_r16 z, tt))).
Definition SL_SyncAllowed_r16__F2 (y : seq_type SL_SyncAllowed_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SL_SyncAllowed_r16__Type i0 i1 i2
  end.
Lemma SL_SyncAllowed_r16__F1F2_cond (z : SL_SyncAllowed_r16__Type)
  : SL_SyncAllowed_r16__cond z ->
  (seq_cond SL_SyncAllowed_r16__list (SL_SyncAllowed_r16__F1 z)).
intro H. unfold SL_SyncAllowed_r16__cond in H. simpl. auto. Qed.
Lemma SL_SyncAllowed_r16__F1F2_cond2 (z : SL_SyncAllowed_r16__Type)
 : SL_SyncAllowed_r16__F2 (SL_SyncAllowed_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_SyncAllowed_r16__F2F1_cond (y : seq_type SL_SyncAllowed_r16__list)
  : seq_cond SL_SyncAllowed_r16__list y ->
 (SL_SyncAllowed_r16__cond (SL_SyncAllowed_r16__F2 y)) /\  SL_SyncAllowed_r16__F1 (SL_SyncAllowed_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_SyncAllowed_r16__cond. simpl in *. auto.
 - simpl. unfold SL_SyncAllowed_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_SyncAllowed_r16__Format : T_Format SL_SyncAllowed_r16__Type SL_SyncAllowed_r16__cond :=
        proj2_format  SL_SyncAllowed_r16__cond SL_SyncAllowed_r16__list__Format
    SL_SyncAllowed_r16__F1 SL_SyncAllowed_r16__F2 SL_SyncAllowed_r16__F1F2_cond  SL_SyncAllowed_r16__F1F2_cond2 SL_SyncAllowed_r16__F2F1_cond.
Opaque SL_SyncAllowed_r16__cond SL_SyncAllowed_r16__Format.

