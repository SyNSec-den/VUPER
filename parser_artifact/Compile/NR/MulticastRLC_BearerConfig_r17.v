Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MRB_Identity_r17.

Opaque MRB_Identity_r17__cond MRB_Identity_r17__Format.

Inductive MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Type : Set :=
 | MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__true
.
Definition MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__cond := (fun (_ : MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Type) => True).
Lemma MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__nat__helper.

Definition MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1 t :=
  match t with
  | MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__true => 0
  end.
Definition MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F2 n :=
  match n with
  | 0 => MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__true
  | _ => MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__true
  end.
Lemma MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1F2 : forall x : MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Type, (MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1 x <= 0) /\ MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F2 (MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1 x) = x. imp_solve. Qed.
Lemma MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F2F1 : forall (y : nat) (H : y <= 0), MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1 (MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F2 y) = y. enum_solve H y. Qed.

Record MulticastRLC_BearerConfig_r17__Type : Set :=
  make__MulticastRLC_BearerConfig_r17__Type {
    MulticastRLC_BearerConfig_r17__servedMBS_RadioBearer_r17 : MRB_Identity_r17__Type ;
    MulticastRLC_BearerConfig_r17__isPTM_Entity_r17 : option MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Type ;
}.
Definition MulticastRLC_BearerConfig_r17__list := (
 Nor MRB_Identity_r17__Type MRB_Identity_r17__cond ::
 Opt MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Type MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__cond ::
 nil).
Definition MulticastRLC_BearerConfig_r17__cond z := 
  MRB_Identity_r17__cond (MulticastRLC_BearerConfig_r17__servedMBS_RadioBearer_r17 z) /\
  opt_cond MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__cond (MulticastRLC_BearerConfig_r17__isPTM_Entity_r17 z) /\
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
Definition MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Format : T_Format MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__nat__Format MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1 MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F2 MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F1F2 MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__F2F1.

Opaque MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__cond MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Format.


Definition MulticastRLC_BearerConfig_r17__Format_Type := Eval cbn in seq_format_prod MulticastRLC_BearerConfig_r17__list.
Definition MulticastRLC_BearerConfig_r17__Format_list : MulticastRLC_BearerConfig_r17__Format_Type :=
  (MRB_Identity_r17__Format, (MulticastRLC_BearerConfig_r17__isPTM_Entity_r17__Format, unit_format)).
Definition MulticastRLC_BearerConfig_r17__list__Format := (*Eval compute in *) seq_format MulticastRLC_BearerConfig_r17__list MulticastRLC_BearerConfig_r17__Format_list.
Definition MulticastRLC_BearerConfig_r17__F1 z :=
  (MulticastRLC_BearerConfig_r17__servedMBS_RadioBearer_r17 z, (MulticastRLC_BearerConfig_r17__isPTM_Entity_r17 z, tt)).
Definition MulticastRLC_BearerConfig_r17__F2 (y : seq_type MulticastRLC_BearerConfig_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MulticastRLC_BearerConfig_r17__Type i0 i1
  end.
Lemma MulticastRLC_BearerConfig_r17__F1F2_cond (z : MulticastRLC_BearerConfig_r17__Type)
  : MulticastRLC_BearerConfig_r17__cond z ->
  (seq_cond MulticastRLC_BearerConfig_r17__list (MulticastRLC_BearerConfig_r17__F1 z)).
intro H. unfold MulticastRLC_BearerConfig_r17__cond in H. simpl. auto. Qed.
Lemma MulticastRLC_BearerConfig_r17__F1F2_cond2 (z : MulticastRLC_BearerConfig_r17__Type)
 : MulticastRLC_BearerConfig_r17__F2 (MulticastRLC_BearerConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MulticastRLC_BearerConfig_r17__F2F1_cond (y : seq_type MulticastRLC_BearerConfig_r17__list)
  : seq_cond MulticastRLC_BearerConfig_r17__list y ->
 (MulticastRLC_BearerConfig_r17__cond (MulticastRLC_BearerConfig_r17__F2 y)) /\  MulticastRLC_BearerConfig_r17__F1 (MulticastRLC_BearerConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MulticastRLC_BearerConfig_r17__cond. simpl in *. auto.
 - simpl. unfold MulticastRLC_BearerConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MulticastRLC_BearerConfig_r17__Format : T_Format MulticastRLC_BearerConfig_r17__Type MulticastRLC_BearerConfig_r17__cond :=
        proj2_format  MulticastRLC_BearerConfig_r17__cond MulticastRLC_BearerConfig_r17__list__Format
    MulticastRLC_BearerConfig_r17__F1 MulticastRLC_BearerConfig_r17__F2 MulticastRLC_BearerConfig_r17__F1F2_cond  MulticastRLC_BearerConfig_r17__F1F2_cond2 MulticastRLC_BearerConfig_r17__F2F1_cond.
Opaque MulticastRLC_BearerConfig_r17__cond MulticastRLC_BearerConfig_r17__Format.

