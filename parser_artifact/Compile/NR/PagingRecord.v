Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PagingUE_Identity.

Opaque PagingUE_Identity__cond PagingUE_Identity__Format.

Inductive PagingRecord__accessType__Type : Set :=
 | PagingRecord__accessType__non3GPP
.
Definition PagingRecord__accessType__cond := (fun (_ : PagingRecord__accessType__Type) => True).
Lemma PagingRecord__accessType__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PagingRecord__accessType__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PagingRecord__accessType__nat__helper.

Definition PagingRecord__accessType__F1 t :=
  match t with
  | PagingRecord__accessType__non3GPP => 0
  end.
Definition PagingRecord__accessType__F2 n :=
  match n with
  | 0 => PagingRecord__accessType__non3GPP
  | _ => PagingRecord__accessType__non3GPP
  end.
Lemma PagingRecord__accessType__F1F2 : forall x : PagingRecord__accessType__Type, (PagingRecord__accessType__F1 x <= 0) /\ PagingRecord__accessType__F2 (PagingRecord__accessType__F1 x) = x. imp_solve. Qed.
Lemma PagingRecord__accessType__F2F1 : forall (y : nat) (H : y <= 0), PagingRecord__accessType__F1 (PagingRecord__accessType__F2 y) = y. enum_solve H y. Qed.

Record PagingRecord__Type : Set :=
  make__PagingRecord__Type {
    PagingRecord__ue_Identity : PagingUE_Identity__Type ;
    PagingRecord__accessType : option PagingRecord__accessType__Type ;
}.
Definition PagingRecord__root_list : list seq_elem := (
 Nor PagingUE_Identity__Type PagingUE_Identity__cond ::
 Opt PagingRecord__accessType__Type PagingRecord__accessType__cond ::
 nil).
Definition PagingRecord__ext_list : list typ := (
  nil).
Definition PagingRecord__cond (z : PagingRecord__Type) := 
(  PagingUE_Identity__cond (PagingRecord__ue_Identity z) /\
  opt_cond PagingRecord__accessType__cond (PagingRecord__accessType z) /\
  True) /\ 
(  True).


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
Definition PagingRecord__accessType__Format : T_Format PagingRecord__accessType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PagingRecord__accessType__nat__Format PagingRecord__accessType__F1 PagingRecord__accessType__F2 PagingRecord__accessType__F1F2 PagingRecord__accessType__F2F1.

Opaque PagingRecord__accessType__cond PagingRecord__accessType__Format.


Definition PagingRecord__root_Format_Type := Eval cbn in seq_format_prod PagingRecord__root_list.
Definition PagingRecord__root_Format_list : PagingRecord__root_Format_Type :=
  (PagingUE_Identity__Format, (PagingRecord__accessType__Format, unit_format)).

Definition PagingRecord__ext_Format_Type := Eval cbn in get_formats PagingRecord__ext_list.
Definition PagingRecord__ext_Format_list : PagingRecord__ext_Format_Type :=
  unit__Format.

Definition PagingRecord__list_type : Set := (seq_type PagingRecord__root_list) * (seq_ext_type PagingRecord__ext_list).
Definition PagingRecord__list_cond (z : PagingRecord__list_type) : Prop :=
        (seq_cond PagingRecord__root_list (fst z)) /\ (seq_ext_cond PagingRecord__ext_list (snd z)).
Definition PagingRecord__list_format : T_Format PagingRecord__list_type PagingRecord__list_cond :=
 (* Eval compute in *) seq_ext_format PagingRecord__root_list PagingRecord__root_Format_list PagingRecord__ext_list PagingRecord__ext_Format_list.

Opaque PagingRecord__list_format.
Definition PagingRecord__F1 (z : PagingRecord__Type) : PagingRecord__list_type :=
  (((PagingRecord__ue_Identity z, (PagingRecord__accessType z, tt))), (
tt)).
Definition PagingRecord__F2 (y : PagingRecord__list_type) : PagingRecord__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__PagingRecord__Type j0 j1
  end.
Definition PagingRecord__helper1 : (forall a : PagingRecord__Type, PagingRecord__cond a -> PagingRecord__list_cond (PagingRecord__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PagingRecord__helper2 : (forall a : PagingRecord__Type, PagingRecord__F2 (PagingRecord__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PagingRecord__helper3 : (forall b : PagingRecord__list_type, PagingRecord__list_cond b -> PagingRecord__cond (PagingRecord__F2 b) /\ PagingRecord__F1 (PagingRecord__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PagingRecord__cond, PagingRecord__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PagingRecord__Format : T_Format PagingRecord__Type PagingRecord__cond :=
 proj2_format PagingRecord__cond PagingRecord__list_format  PagingRecord__F1 PagingRecord__F2 PagingRecord__helper1 PagingRecord__helper2 PagingRecord__helper3.

Opaque PagingRecord__cond PagingRecord__Format.

