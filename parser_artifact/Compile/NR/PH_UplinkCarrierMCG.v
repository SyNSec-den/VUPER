Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Inductive PH_UplinkCarrierMCG__ph_Type1or3__Type : Set :=
 | PH_UplinkCarrierMCG__ph_Type1or3__type1
 | PH_UplinkCarrierMCG__ph_Type1or3__type3
.
Definition PH_UplinkCarrierMCG__ph_Type1or3__cond := (fun (_ : PH_UplinkCarrierMCG__ph_Type1or3__Type) => True).
Lemma PH_UplinkCarrierMCG__ph_Type1or3__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PH_UplinkCarrierMCG__ph_Type1or3__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PH_UplinkCarrierMCG__ph_Type1or3__nat__helper.

Definition PH_UplinkCarrierMCG__ph_Type1or3__F1 t :=
  match t with
  | PH_UplinkCarrierMCG__ph_Type1or3__type1 => 0
  | PH_UplinkCarrierMCG__ph_Type1or3__type3 => 1
  end.
Definition PH_UplinkCarrierMCG__ph_Type1or3__F2 n :=
  match n with
  | 0 => PH_UplinkCarrierMCG__ph_Type1or3__type1
  | 1 => PH_UplinkCarrierMCG__ph_Type1or3__type3
  | _ => PH_UplinkCarrierMCG__ph_Type1or3__type1
  end.
Lemma PH_UplinkCarrierMCG__ph_Type1or3__F1F2 : forall x : PH_UplinkCarrierMCG__ph_Type1or3__Type, (PH_UplinkCarrierMCG__ph_Type1or3__F1 x <= 1) /\ PH_UplinkCarrierMCG__ph_Type1or3__F2 (PH_UplinkCarrierMCG__ph_Type1or3__F1 x) = x. imp_solve. Qed.
Lemma PH_UplinkCarrierMCG__ph_Type1or3__F2F1 : forall (y : nat) (H : y <= 1), PH_UplinkCarrierMCG__ph_Type1or3__F1 (PH_UplinkCarrierMCG__ph_Type1or3__F2 y) = y. enum_solve H y. Qed.

Record PH_UplinkCarrierMCG__Type : Set :=
  make__PH_UplinkCarrierMCG__Type {
    PH_UplinkCarrierMCG__ph_Type1or3 : PH_UplinkCarrierMCG__ph_Type1or3__Type ;
}.
Definition PH_UplinkCarrierMCG__root_list : list seq_elem := (
 Nor PH_UplinkCarrierMCG__ph_Type1or3__Type PH_UplinkCarrierMCG__ph_Type1or3__cond ::
 nil).
Definition PH_UplinkCarrierMCG__ext_list : list typ := (
  nil).
Definition PH_UplinkCarrierMCG__cond (z : PH_UplinkCarrierMCG__Type) := 
(  PH_UplinkCarrierMCG__ph_Type1or3__cond (PH_UplinkCarrierMCG__ph_Type1or3 z) /\
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
Definition PH_UplinkCarrierMCG__ph_Type1or3__Format : T_Format PH_UplinkCarrierMCG__ph_Type1or3__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PH_UplinkCarrierMCG__ph_Type1or3__nat__Format PH_UplinkCarrierMCG__ph_Type1or3__F1 PH_UplinkCarrierMCG__ph_Type1or3__F2 PH_UplinkCarrierMCG__ph_Type1or3__F1F2 PH_UplinkCarrierMCG__ph_Type1or3__F2F1.

Opaque PH_UplinkCarrierMCG__ph_Type1or3__cond PH_UplinkCarrierMCG__ph_Type1or3__Format.


Definition PH_UplinkCarrierMCG__root_Format_Type := Eval cbn in seq_format_prod PH_UplinkCarrierMCG__root_list.
Definition PH_UplinkCarrierMCG__root_Format_list : PH_UplinkCarrierMCG__root_Format_Type :=
  (PH_UplinkCarrierMCG__ph_Type1or3__Format, unit_format).

Definition PH_UplinkCarrierMCG__ext_Format_Type := Eval cbn in get_formats PH_UplinkCarrierMCG__ext_list.
Definition PH_UplinkCarrierMCG__ext_Format_list : PH_UplinkCarrierMCG__ext_Format_Type :=
  unit__Format.

Definition PH_UplinkCarrierMCG__list_type : Set := (seq_type PH_UplinkCarrierMCG__root_list) * (seq_ext_type PH_UplinkCarrierMCG__ext_list).
Definition PH_UplinkCarrierMCG__list_cond (z : PH_UplinkCarrierMCG__list_type) : Prop :=
        (seq_cond PH_UplinkCarrierMCG__root_list (fst z)) /\ (seq_ext_cond PH_UplinkCarrierMCG__ext_list (snd z)).
Definition PH_UplinkCarrierMCG__list_format : T_Format PH_UplinkCarrierMCG__list_type PH_UplinkCarrierMCG__list_cond :=
 (* Eval compute in *) seq_ext_format PH_UplinkCarrierMCG__root_list PH_UplinkCarrierMCG__root_Format_list PH_UplinkCarrierMCG__ext_list PH_UplinkCarrierMCG__ext_Format_list.

Opaque PH_UplinkCarrierMCG__list_format.
Definition PH_UplinkCarrierMCG__F1 (z : PH_UplinkCarrierMCG__Type) : PH_UplinkCarrierMCG__list_type :=
  (((PH_UplinkCarrierMCG__ph_Type1or3 z, tt)), (
tt)).
Definition PH_UplinkCarrierMCG__F2 (y : PH_UplinkCarrierMCG__list_type) : PH_UplinkCarrierMCG__Type :=
  match y with
  | ((j0, _), _)=>
    make__PH_UplinkCarrierMCG__Type j0
  end.
Definition PH_UplinkCarrierMCG__helper1 : (forall a : PH_UplinkCarrierMCG__Type, PH_UplinkCarrierMCG__cond a -> PH_UplinkCarrierMCG__list_cond (PH_UplinkCarrierMCG__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PH_UplinkCarrierMCG__helper2 : (forall a : PH_UplinkCarrierMCG__Type, PH_UplinkCarrierMCG__F2 (PH_UplinkCarrierMCG__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PH_UplinkCarrierMCG__helper3 : (forall b : PH_UplinkCarrierMCG__list_type, PH_UplinkCarrierMCG__list_cond b -> PH_UplinkCarrierMCG__cond (PH_UplinkCarrierMCG__F2 b) /\ PH_UplinkCarrierMCG__F1 (PH_UplinkCarrierMCG__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PH_UplinkCarrierMCG__cond, PH_UplinkCarrierMCG__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PH_UplinkCarrierMCG__Format : T_Format PH_UplinkCarrierMCG__Type PH_UplinkCarrierMCG__cond :=
 proj2_format PH_UplinkCarrierMCG__cond PH_UplinkCarrierMCG__list_format  PH_UplinkCarrierMCG__F1 PH_UplinkCarrierMCG__F2 PH_UplinkCarrierMCG__helper1 PH_UplinkCarrierMCG__helper2 PH_UplinkCarrierMCG__helper3.

Opaque PH_UplinkCarrierMCG__cond PH_UplinkCarrierMCG__Format.

