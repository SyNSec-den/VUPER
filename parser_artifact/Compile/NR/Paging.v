Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PagingRecordList.

Opaque PagingRecordList__cond PagingRecordList__Format.

Require Import NR.Paging_v1700_IEs.

Opaque Paging_v1700_IEs__cond Paging_v1700_IEs__Format.

Record Paging__Type : Set :=
  make__Paging__Type {
    Paging__pagingRecordList : option PagingRecordList__Type ;
    Paging__lateNonCriticalExtension : option octet_string ;
    Paging__nonCriticalExtension : option Paging_v1700_IEs__Type ;
}.
Definition Paging__list := (
 Opt PagingRecordList__Type PagingRecordList__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt Paging_v1700_IEs__Type Paging_v1700_IEs__cond ::
 nil).
Definition Paging__cond z := 
  opt_cond PagingRecordList__cond (Paging__pagingRecordList z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (Paging__lateNonCriticalExtension z) /\
  opt_cond Paging_v1700_IEs__cond (Paging__nonCriticalExtension z) /\
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

Definition Paging__Format_Type := Eval cbn in seq_format_prod Paging__list.
Definition Paging__Format_list : Paging__Format_Type :=
  (PagingRecordList__Format, (octet_string_nc__Format, (Paging_v1700_IEs__Format, unit_format))).
Definition Paging__list__Format := (*Eval compute in *) seq_format Paging__list Paging__Format_list.
Definition Paging__F1 z :=
  (Paging__pagingRecordList z, (Paging__lateNonCriticalExtension z, (Paging__nonCriticalExtension z, tt))).
Definition Paging__F2 (y : seq_type Paging__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Paging__Type i0 i1 i2
  end.
Lemma Paging__F1F2_cond (z : Paging__Type)
  : Paging__cond z ->
  (seq_cond Paging__list (Paging__F1 z)).
intro H. unfold Paging__cond in H. simpl. auto. Qed.
Lemma Paging__F1F2_cond2 (z : Paging__Type)
 : Paging__F2 (Paging__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Paging__F2F1_cond (y : seq_type Paging__list)
  : seq_cond Paging__list y ->
 (Paging__cond (Paging__F2 y)) /\  Paging__F1 (Paging__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Paging__cond. simpl in *. auto.
 - simpl. unfold Paging__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Paging__Format : T_Format Paging__Type Paging__cond :=
        proj2_format  Paging__cond Paging__list__Format
    Paging__F1 Paging__F2 Paging__F1F2_cond  Paging__F1F2_cond2 Paging__F2F1_cond.
Opaque Paging__cond Paging__Format.

