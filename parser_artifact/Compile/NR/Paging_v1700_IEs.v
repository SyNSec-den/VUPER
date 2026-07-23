Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PagingRecordList_v1700.

Opaque PagingRecordList_v1700__cond PagingRecordList_v1700__Format.

Require Import NR.PagingGroupList_r17.

Opaque PagingGroupList_r17__cond PagingGroupList_r17__Format.

Record Paging_v1700_IEs__nonCriticalExtension__Type : Set := make__Paging_v1700_IEs__nonCriticalExtension__Type {}.
Definition Paging_v1700_IEs__nonCriticalExtension__cond (z : Paging_v1700_IEs__nonCriticalExtension__Type) := True.
Record Paging_v1700_IEs__Type : Set :=
  make__Paging_v1700_IEs__Type {
    Paging_v1700_IEs__pagingRecordList_v1700 : option PagingRecordList_v1700__Type ;
    Paging_v1700_IEs__pagingGroupList_r17 : option PagingGroupList_r17__Type ;
    Paging_v1700_IEs__nonCriticalExtension : option Paging_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition Paging_v1700_IEs__list := (
 Opt PagingRecordList_v1700__Type PagingRecordList_v1700__cond ::
 Opt PagingGroupList_r17__Type PagingGroupList_r17__cond ::
 Opt Paging_v1700_IEs__nonCriticalExtension__Type Paging_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition Paging_v1700_IEs__cond z := 
  opt_cond PagingRecordList_v1700__cond (Paging_v1700_IEs__pagingRecordList_v1700 z) /\
  opt_cond PagingGroupList_r17__cond (Paging_v1700_IEs__pagingGroupList_r17 z) /\
  opt_cond Paging_v1700_IEs__nonCriticalExtension__cond (Paging_v1700_IEs__nonCriticalExtension z) /\
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
Definition Paging_v1700_IEs__nonCriticalExtension__helper : forall a : Paging_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__Paging_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition Paging_v1700_IEs__nonCriticalExtension__Format : T_Format Paging_v1700_IEs__nonCriticalExtension__Type Paging_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__Paging_v1700_IEs__nonCriticalExtension__Type)
    Paging_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque Paging_v1700_IEs__nonCriticalExtension__cond Paging_v1700_IEs__nonCriticalExtension__Format.


Definition Paging_v1700_IEs__Format_Type := Eval cbn in seq_format_prod Paging_v1700_IEs__list.
Definition Paging_v1700_IEs__Format_list : Paging_v1700_IEs__Format_Type :=
  (PagingRecordList_v1700__Format, (PagingGroupList_r17__Format, (Paging_v1700_IEs__nonCriticalExtension__Format, unit_format))).
Definition Paging_v1700_IEs__list__Format := (*Eval compute in *) seq_format Paging_v1700_IEs__list Paging_v1700_IEs__Format_list.
Definition Paging_v1700_IEs__F1 z :=
  (Paging_v1700_IEs__pagingRecordList_v1700 z, (Paging_v1700_IEs__pagingGroupList_r17 z, (Paging_v1700_IEs__nonCriticalExtension z, tt))).
Definition Paging_v1700_IEs__F2 (y : seq_type Paging_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Paging_v1700_IEs__Type i0 i1 i2
  end.
Lemma Paging_v1700_IEs__F1F2_cond (z : Paging_v1700_IEs__Type)
  : Paging_v1700_IEs__cond z ->
  (seq_cond Paging_v1700_IEs__list (Paging_v1700_IEs__F1 z)).
intro H. unfold Paging_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma Paging_v1700_IEs__F1F2_cond2 (z : Paging_v1700_IEs__Type)
 : Paging_v1700_IEs__F2 (Paging_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Paging_v1700_IEs__F2F1_cond (y : seq_type Paging_v1700_IEs__list)
  : seq_cond Paging_v1700_IEs__list y ->
 (Paging_v1700_IEs__cond (Paging_v1700_IEs__F2 y)) /\  Paging_v1700_IEs__F1 (Paging_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Paging_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold Paging_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Paging_v1700_IEs__Format : T_Format Paging_v1700_IEs__Type Paging_v1700_IEs__cond :=
        proj2_format  Paging_v1700_IEs__cond Paging_v1700_IEs__list__Format
    Paging_v1700_IEs__F1 Paging_v1700_IEs__F2 Paging_v1700_IEs__F1F2_cond  Paging_v1700_IEs__F1F2_cond2 Paging_v1700_IEs__F2F1_cond.
Opaque Paging_v1700_IEs__cond Paging_v1700_IEs__Format.

