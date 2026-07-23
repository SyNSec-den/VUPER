Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SecurityAlgorithmConfig.

Opaque SecurityAlgorithmConfig__cond SecurityAlgorithmConfig__Format.

Inductive SecurityConfig__keyToUse__Type : Set :=
 | SecurityConfig__keyToUse__master
 | SecurityConfig__keyToUse__secondary
.
Definition SecurityConfig__keyToUse__cond := (fun (_ : SecurityConfig__keyToUse__Type) => True).
Lemma SecurityConfig__keyToUse__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SecurityConfig__keyToUse__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SecurityConfig__keyToUse__nat__helper.

Definition SecurityConfig__keyToUse__F1 t :=
  match t with
  | SecurityConfig__keyToUse__master => 0
  | SecurityConfig__keyToUse__secondary => 1
  end.
Definition SecurityConfig__keyToUse__F2 n :=
  match n with
  | 0 => SecurityConfig__keyToUse__master
  | 1 => SecurityConfig__keyToUse__secondary
  | _ => SecurityConfig__keyToUse__master
  end.
Lemma SecurityConfig__keyToUse__F1F2 : forall x : SecurityConfig__keyToUse__Type, (SecurityConfig__keyToUse__F1 x <= 1) /\ SecurityConfig__keyToUse__F2 (SecurityConfig__keyToUse__F1 x) = x. imp_solve. Qed.
Lemma SecurityConfig__keyToUse__F2F1 : forall (y : nat) (H : y <= 1), SecurityConfig__keyToUse__F1 (SecurityConfig__keyToUse__F2 y) = y. enum_solve H y. Qed.

Record SecurityConfig__Type : Set :=
  make__SecurityConfig__Type {
    SecurityConfig__securityAlgorithmConfig : option SecurityAlgorithmConfig__Type ;
    SecurityConfig__keyToUse : option SecurityConfig__keyToUse__Type ;
}.
Definition SecurityConfig__root_list : list seq_elem := (
 Opt SecurityAlgorithmConfig__Type SecurityAlgorithmConfig__cond ::
 Opt SecurityConfig__keyToUse__Type SecurityConfig__keyToUse__cond ::
 nil).
Definition SecurityConfig__ext_list : list typ := (
  nil).
Definition SecurityConfig__cond (z : SecurityConfig__Type) := 
(  opt_cond SecurityAlgorithmConfig__cond (SecurityConfig__securityAlgorithmConfig z) /\
  opt_cond SecurityConfig__keyToUse__cond (SecurityConfig__keyToUse z) /\
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
Definition SecurityConfig__keyToUse__Format : T_Format SecurityConfig__keyToUse__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SecurityConfig__keyToUse__nat__Format SecurityConfig__keyToUse__F1 SecurityConfig__keyToUse__F2 SecurityConfig__keyToUse__F1F2 SecurityConfig__keyToUse__F2F1.

Opaque SecurityConfig__keyToUse__cond SecurityConfig__keyToUse__Format.


Definition SecurityConfig__root_Format_Type := Eval cbn in seq_format_prod SecurityConfig__root_list.
Definition SecurityConfig__root_Format_list : SecurityConfig__root_Format_Type :=
  (SecurityAlgorithmConfig__Format, (SecurityConfig__keyToUse__Format, unit_format)).

Definition SecurityConfig__ext_Format_Type := Eval cbn in get_formats SecurityConfig__ext_list.
Definition SecurityConfig__ext_Format_list : SecurityConfig__ext_Format_Type :=
  unit__Format.

Definition SecurityConfig__list_type : Set := (seq_type SecurityConfig__root_list) * (seq_ext_type SecurityConfig__ext_list).
Definition SecurityConfig__list_cond (z : SecurityConfig__list_type) : Prop :=
        (seq_cond SecurityConfig__root_list (fst z)) /\ (seq_ext_cond SecurityConfig__ext_list (snd z)).
Definition SecurityConfig__list_format : T_Format SecurityConfig__list_type SecurityConfig__list_cond :=
 (* Eval compute in *) seq_ext_format SecurityConfig__root_list SecurityConfig__root_Format_list SecurityConfig__ext_list SecurityConfig__ext_Format_list.

Opaque SecurityConfig__list_format.
Definition SecurityConfig__F1 (z : SecurityConfig__Type) : SecurityConfig__list_type :=
  (((SecurityConfig__securityAlgorithmConfig z, (SecurityConfig__keyToUse z, tt))), (
tt)).
Definition SecurityConfig__F2 (y : SecurityConfig__list_type) : SecurityConfig__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__SecurityConfig__Type j0 j1
  end.
Definition SecurityConfig__helper1 : (forall a : SecurityConfig__Type, SecurityConfig__cond a -> SecurityConfig__list_cond (SecurityConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SecurityConfig__helper2 : (forall a : SecurityConfig__Type, SecurityConfig__F2 (SecurityConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SecurityConfig__helper3 : (forall b : SecurityConfig__list_type, SecurityConfig__list_cond b -> SecurityConfig__cond (SecurityConfig__F2 b) /\ SecurityConfig__F1 (SecurityConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SecurityConfig__cond, SecurityConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SecurityConfig__Format : T_Format SecurityConfig__Type SecurityConfig__cond :=
 proj2_format SecurityConfig__cond SecurityConfig__list_format  SecurityConfig__F1 SecurityConfig__F2 SecurityConfig__helper1 SecurityConfig__helper2 SecurityConfig__helper3.

Opaque SecurityConfig__cond SecurityConfig__Format.

