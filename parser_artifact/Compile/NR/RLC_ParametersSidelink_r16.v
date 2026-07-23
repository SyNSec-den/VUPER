Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Type : Set :=
 | RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__supported
.
Definition RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__cond := (fun (_ : RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Type) => True).
Lemma RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__nat__helper.

Definition RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1 t :=
  match t with
  | RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__supported => 0
  end.
Definition RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F2 n :=
  match n with
  | 0 => RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__supported
  | _ => RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__supported
  end.
Lemma RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1F2 : forall x : RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Type, (RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1 x <= 0) /\ RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F2 (RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1 (RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Type : Set :=
 | RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__supported
.
Definition RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__cond := (fun (_ : RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Type) => True).
Lemma RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__nat__helper.

Definition RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1 t :=
  match t with
  | RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__supported => 0
  end.
Definition RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F2 n :=
  match n with
  | 0 => RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__supported
  | _ => RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__supported
  end.
Lemma RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1F2 : forall x : RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Type, (RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1 x <= 0) /\ RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F2 (RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1 (RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F2 y) = y. enum_solve H y. Qed.

Record RLC_ParametersSidelink_r16__Type : Set :=
  make__RLC_ParametersSidelink_r16__Type {
    RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16 : option RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Type ;
    RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16 : option RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Type ;
}.
Definition RLC_ParametersSidelink_r16__root_list : list seq_elem := (
 Opt RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Type RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__cond ::
 Opt RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Type RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__cond ::
 nil).
Definition RLC_ParametersSidelink_r16__ext_list : list typ := (
  nil).
Definition RLC_ParametersSidelink_r16__cond (z : RLC_ParametersSidelink_r16__Type) := 
(  opt_cond RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__cond (RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16 z) /\
  opt_cond RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__cond (RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16 z) /\
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
Definition RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Format : T_Format RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__nat__Format RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1 RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F2 RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F1F2 RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__F2F1.

Opaque RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__cond RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Format.

Definition RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Format : T_Format RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__nat__Format RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1 RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F2 RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F1F2 RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__F2F1.

Opaque RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__cond RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Format.


Definition RLC_ParametersSidelink_r16__root_Format_Type := Eval cbn in seq_format_prod RLC_ParametersSidelink_r16__root_list.
Definition RLC_ParametersSidelink_r16__root_Format_list : RLC_ParametersSidelink_r16__root_Format_Type :=
  (RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16__Format, (RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16__Format, unit_format)).

Definition RLC_ParametersSidelink_r16__ext_Format_Type := Eval cbn in get_formats RLC_ParametersSidelink_r16__ext_list.
Definition RLC_ParametersSidelink_r16__ext_Format_list : RLC_ParametersSidelink_r16__ext_Format_Type :=
  unit__Format.

Definition RLC_ParametersSidelink_r16__list_type : Set := (seq_type RLC_ParametersSidelink_r16__root_list) * (seq_ext_type RLC_ParametersSidelink_r16__ext_list).
Definition RLC_ParametersSidelink_r16__list_cond (z : RLC_ParametersSidelink_r16__list_type) : Prop :=
        (seq_cond RLC_ParametersSidelink_r16__root_list (fst z)) /\ (seq_ext_cond RLC_ParametersSidelink_r16__ext_list (snd z)).
Definition RLC_ParametersSidelink_r16__list_format : T_Format RLC_ParametersSidelink_r16__list_type RLC_ParametersSidelink_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RLC_ParametersSidelink_r16__root_list RLC_ParametersSidelink_r16__root_Format_list RLC_ParametersSidelink_r16__ext_list RLC_ParametersSidelink_r16__ext_Format_list.

Opaque RLC_ParametersSidelink_r16__list_format.
Definition RLC_ParametersSidelink_r16__F1 (z : RLC_ParametersSidelink_r16__Type) : RLC_ParametersSidelink_r16__list_type :=
  (((RLC_ParametersSidelink_r16__am_WithLongSN_Sidelink_r16 z, (RLC_ParametersSidelink_r16__um_WithLongSN_Sidelink_r16 z, tt))), (
tt)).
Definition RLC_ParametersSidelink_r16__F2 (y : RLC_ParametersSidelink_r16__list_type) : RLC_ParametersSidelink_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__RLC_ParametersSidelink_r16__Type j0 j1
  end.
Definition RLC_ParametersSidelink_r16__helper1 : (forall a : RLC_ParametersSidelink_r16__Type, RLC_ParametersSidelink_r16__cond a -> RLC_ParametersSidelink_r16__list_cond (RLC_ParametersSidelink_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RLC_ParametersSidelink_r16__helper2 : (forall a : RLC_ParametersSidelink_r16__Type, RLC_ParametersSidelink_r16__F2 (RLC_ParametersSidelink_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RLC_ParametersSidelink_r16__helper3 : (forall b : RLC_ParametersSidelink_r16__list_type, RLC_ParametersSidelink_r16__list_cond b -> RLC_ParametersSidelink_r16__cond (RLC_ParametersSidelink_r16__F2 b) /\ RLC_ParametersSidelink_r16__F1 (RLC_ParametersSidelink_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RLC_ParametersSidelink_r16__cond, RLC_ParametersSidelink_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RLC_ParametersSidelink_r16__Format : T_Format RLC_ParametersSidelink_r16__Type RLC_ParametersSidelink_r16__cond :=
 proj2_format RLC_ParametersSidelink_r16__cond RLC_ParametersSidelink_r16__list_format  RLC_ParametersSidelink_r16__F1 RLC_ParametersSidelink_r16__F2 RLC_ParametersSidelink_r16__helper1 RLC_ParametersSidelink_r16__helper2 RLC_ParametersSidelink_r16__helper3.

Opaque RLC_ParametersSidelink_r16__cond RLC_ParametersSidelink_r16__Format.

