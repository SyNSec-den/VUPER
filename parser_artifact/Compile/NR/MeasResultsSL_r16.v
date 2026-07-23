Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasResultNR_SL_r16.

Opaque MeasResultNR_SL_r16__cond MeasResultNR_SL_r16__Format.


Inductive MeasResultsSL_r16__measResultsListSL_r16__root__Type : Set := | MeasResultsSL_r16__measResultsListSL_r16__root__measResultNR_SL_r16 : MeasResultNR_SL_r16__Type -> MeasResultsSL_r16__measResultsListSL_r16__root__Type.
Definition MeasResultsSL_r16__measResultsListSL_r16__root__cond (c : MeasResultsSL_r16__measResultsListSL_r16__root__Type) := 
  match c with
  | MeasResultsSL_r16__measResultsListSL_r16__root__measResultNR_SL_r16 t => MeasResultNR_SL_r16__cond t 
  end.


Definition MeasResultsSL_r16__measResultsListSL_r16__ext__Type : Set := Empty_set.
Definition MeasResultsSL_r16__measResultsListSL_r16__ext__cond (c : MeasResultsSL_r16__measResultsListSL_r16__ext__Type) := True.
Definition MeasResultsSL_r16__measResultsListSL_r16__Type : Set := MeasResultsSL_r16__measResultsListSL_r16__root__Type + MeasResultsSL_r16__measResultsListSL_r16__ext__Type.
Definition MeasResultsSL_r16__measResultsListSL_r16__cond :=
  sum_cond MeasResultsSL_r16__measResultsListSL_r16__root__cond MeasResultsSL_r16__measResultsListSL_r16__ext__cond.
Record MeasResultsSL_r16__Type : Set :=
  make__MeasResultsSL_r16__Type {
    MeasResultsSL_r16__measResultsListSL_r16 : MeasResultsSL_r16__measResultsListSL_r16__Type ;
}.
Definition MeasResultsSL_r16__root_list : list seq_elem := (
 Nor MeasResultsSL_r16__measResultsListSL_r16__Type MeasResultsSL_r16__measResultsListSL_r16__cond ::
 nil).
Definition MeasResultsSL_r16__ext_list : list typ := (
  nil).
Definition MeasResultsSL_r16__cond (z : MeasResultsSL_r16__Type) := 
(  MeasResultsSL_r16__measResultsListSL_r16__cond (MeasResultsSL_r16__measResultsListSL_r16 z) /\
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
Definition MeasResultsSL_r16__measResultsListSL_r16__root__F1 (z : MeasResultsSL_r16__measResultsListSL_r16__root__Type) : MeasResultNR_SL_r16__Type := 
  match z with
  | MeasResultsSL_r16__measResultsListSL_r16__root__measResultNR_SL_r16 t => t
  end.
Definition MeasResultsSL_r16__measResultsListSL_r16__root__F2 (y : MeasResultNR_SL_r16__Type) : MeasResultsSL_r16__measResultsListSL_r16__root__Type := MeasResultsSL_r16__measResultsListSL_r16__root__measResultNR_SL_r16 y.

Definition MeasResultsSL_r16__measResultsListSL_r16__root__helper2 : (forall z : MeasResultsSL_r16__measResultsListSL_r16__root__Type, MeasResultsSL_r16__measResultsListSL_r16__root__cond z -> MeasResultNR_SL_r16__cond (MeasResultsSL_r16__measResultsListSL_r16__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition MeasResultsSL_r16__measResultsListSL_r16__root__helper3 : (forall z : MeasResultsSL_r16__measResultsListSL_r16__root__Type, MeasResultsSL_r16__measResultsListSL_r16__root__F2 (MeasResultsSL_r16__measResultsListSL_r16__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition MeasResultsSL_r16__measResultsListSL_r16__root__helper4 : (forall y : MeasResultNR_SL_r16__Type, MeasResultNR_SL_r16__cond y -> MeasResultsSL_r16__measResultsListSL_r16__root__cond (MeasResultsSL_r16__measResultsListSL_r16__root__F2 y) /\  MeasResultsSL_r16__measResultsListSL_r16__root__F1 (MeasResultsSL_r16__measResultsListSL_r16__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition MeasResultsSL_r16__measResultsListSL_r16__root__Format : T_Format MeasResultsSL_r16__measResultsListSL_r16__root__Type MeasResultsSL_r16__measResultsListSL_r16__root__cond :=
  proj2_format MeasResultsSL_r16__measResultsListSL_r16__root__cond MeasResultNR_SL_r16__Format MeasResultsSL_r16__measResultsListSL_r16__root__F1 MeasResultsSL_r16__measResultsListSL_r16__root__F2 MeasResultsSL_r16__measResultsListSL_r16__root__helper2 MeasResultsSL_r16__measResultsListSL_r16__root__helper3 MeasResultsSL_r16__measResultsListSL_r16__root__helper4.
Opaque MeasResultsSL_r16__measResultsListSL_r16__root__cond MeasResultsSL_r16__measResultsListSL_r16__root__Format.

Definition MeasResultsSL_r16__measResultsListSL_r16__ext__Format : T_Format MeasResultsSL_r16__measResultsListSL_r16__ext__Type MeasResultsSL_r16__measResultsListSL_r16__ext__cond := empty_format.
Opaque MeasResultsSL_r16__measResultsListSL_r16__ext__cond MeasResultsSL_r16__measResultsListSL_r16__ext__Format.

Definition MeasResultsSL_r16__measResultsListSL_r16__Format : T_Format MeasResultsSL_r16__measResultsListSL_r16__Type MeasResultsSL_r16__measResultsListSL_r16__cond := sum_format MeasResultsSL_r16__measResultsListSL_r16__root__Format MeasResultsSL_r16__measResultsListSL_r16__ext__Format.
Opaque MeasResultsSL_r16__measResultsListSL_r16__cond MeasResultsSL_r16__measResultsListSL_r16__Format.


Definition MeasResultsSL_r16__root_Format_Type := Eval cbn in seq_format_prod MeasResultsSL_r16__root_list.
Definition MeasResultsSL_r16__root_Format_list : MeasResultsSL_r16__root_Format_Type :=
  (MeasResultsSL_r16__measResultsListSL_r16__Format, unit_format).

Definition MeasResultsSL_r16__ext_Format_Type := Eval cbn in get_formats MeasResultsSL_r16__ext_list.
Definition MeasResultsSL_r16__ext_Format_list : MeasResultsSL_r16__ext_Format_Type :=
  unit__Format.

Definition MeasResultsSL_r16__list_type : Set := (seq_type MeasResultsSL_r16__root_list) * (seq_ext_type MeasResultsSL_r16__ext_list).
Definition MeasResultsSL_r16__list_cond (z : MeasResultsSL_r16__list_type) : Prop :=
        (seq_cond MeasResultsSL_r16__root_list (fst z)) /\ (seq_ext_cond MeasResultsSL_r16__ext_list (snd z)).
Definition MeasResultsSL_r16__list_format : T_Format MeasResultsSL_r16__list_type MeasResultsSL_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultsSL_r16__root_list MeasResultsSL_r16__root_Format_list MeasResultsSL_r16__ext_list MeasResultsSL_r16__ext_Format_list.

Opaque MeasResultsSL_r16__list_format.
Definition MeasResultsSL_r16__F1 (z : MeasResultsSL_r16__Type) : MeasResultsSL_r16__list_type :=
  (((MeasResultsSL_r16__measResultsListSL_r16 z, tt)), (
tt)).
Definition MeasResultsSL_r16__F2 (y : MeasResultsSL_r16__list_type) : MeasResultsSL_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__MeasResultsSL_r16__Type j0
  end.
Definition MeasResultsSL_r16__helper1 : (forall a : MeasResultsSL_r16__Type, MeasResultsSL_r16__cond a -> MeasResultsSL_r16__list_cond (MeasResultsSL_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultsSL_r16__helper2 : (forall a : MeasResultsSL_r16__Type, MeasResultsSL_r16__F2 (MeasResultsSL_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultsSL_r16__helper3 : (forall b : MeasResultsSL_r16__list_type, MeasResultsSL_r16__list_cond b -> MeasResultsSL_r16__cond (MeasResultsSL_r16__F2 b) /\ MeasResultsSL_r16__F1 (MeasResultsSL_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultsSL_r16__cond, MeasResultsSL_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultsSL_r16__Format : T_Format MeasResultsSL_r16__Type MeasResultsSL_r16__cond :=
 proj2_format MeasResultsSL_r16__cond MeasResultsSL_r16__list_format  MeasResultsSL_r16__F1 MeasResultsSL_r16__F2 MeasResultsSL_r16__helper1 MeasResultsSL_r16__helper2 MeasResultsSL_r16__helper3.

Opaque MeasResultsSL_r16__cond MeasResultsSL_r16__Format.

