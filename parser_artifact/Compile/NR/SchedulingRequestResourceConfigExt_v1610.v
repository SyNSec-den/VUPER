Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Type : Set :=
 | SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p0
 | SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p1
.
Definition SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__cond := (fun (_ : SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Type) => True).
Lemma SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__nat__helper.

Definition SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1 t :=
  match t with
  | SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p0 => 0
  | SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p1 => 1
  end.
Definition SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F2 n :=
  match n with
  | 0 => SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p0
  | 1 => SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p1
  | _ => SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__p0
  end.
Lemma SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1F2 : forall x : SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Type, (SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1 x <= 1) /\ SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F2 (SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F2F1 : forall (y : nat) (H : y <= 1), SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1 (SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F2 y) = y. enum_solve H y. Qed.

Record SchedulingRequestResourceConfigExt_v1610__Type : Set :=
  make__SchedulingRequestResourceConfigExt_v1610__Type {
    SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16 : option SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Type ;
}.
Definition SchedulingRequestResourceConfigExt_v1610__root_list : list seq_elem := (
 Opt SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Type SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__cond ::
 nil).
Definition SchedulingRequestResourceConfigExt_v1610__ext_list : list typ := (
  nil).
Definition SchedulingRequestResourceConfigExt_v1610__cond (z : SchedulingRequestResourceConfigExt_v1610__Type) := 
(  opt_cond SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__cond (SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16 z) /\
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
Definition SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Format : T_Format SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__nat__Format SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1 SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F2 SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F1F2 SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__F2F1.

Opaque SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__cond SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Format.


Definition SchedulingRequestResourceConfigExt_v1610__root_Format_Type := Eval cbn in seq_format_prod SchedulingRequestResourceConfigExt_v1610__root_list.
Definition SchedulingRequestResourceConfigExt_v1610__root_Format_list : SchedulingRequestResourceConfigExt_v1610__root_Format_Type :=
  (SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16__Format, unit_format).

Definition SchedulingRequestResourceConfigExt_v1610__ext_Format_Type := Eval cbn in get_formats SchedulingRequestResourceConfigExt_v1610__ext_list.
Definition SchedulingRequestResourceConfigExt_v1610__ext_Format_list : SchedulingRequestResourceConfigExt_v1610__ext_Format_Type :=
  unit__Format.

Definition SchedulingRequestResourceConfigExt_v1610__list_type : Set := (seq_type SchedulingRequestResourceConfigExt_v1610__root_list) * (seq_ext_type SchedulingRequestResourceConfigExt_v1610__ext_list).
Definition SchedulingRequestResourceConfigExt_v1610__list_cond (z : SchedulingRequestResourceConfigExt_v1610__list_type) : Prop :=
        (seq_cond SchedulingRequestResourceConfigExt_v1610__root_list (fst z)) /\ (seq_ext_cond SchedulingRequestResourceConfigExt_v1610__ext_list (snd z)).
Definition SchedulingRequestResourceConfigExt_v1610__list_format : T_Format SchedulingRequestResourceConfigExt_v1610__list_type SchedulingRequestResourceConfigExt_v1610__list_cond :=
 (* Eval compute in *) seq_ext_format SchedulingRequestResourceConfigExt_v1610__root_list SchedulingRequestResourceConfigExt_v1610__root_Format_list SchedulingRequestResourceConfigExt_v1610__ext_list SchedulingRequestResourceConfigExt_v1610__ext_Format_list.

Opaque SchedulingRequestResourceConfigExt_v1610__list_format.
Definition SchedulingRequestResourceConfigExt_v1610__F1 (z : SchedulingRequestResourceConfigExt_v1610__Type) : SchedulingRequestResourceConfigExt_v1610__list_type :=
  (((SchedulingRequestResourceConfigExt_v1610__phy_PriorityIndex_r16 z, tt)), (
tt)).
Definition SchedulingRequestResourceConfigExt_v1610__F2 (y : SchedulingRequestResourceConfigExt_v1610__list_type) : SchedulingRequestResourceConfigExt_v1610__Type :=
  match y with
  | ((j0, _), _)=>
    make__SchedulingRequestResourceConfigExt_v1610__Type j0
  end.
Definition SchedulingRequestResourceConfigExt_v1610__helper1 : (forall a : SchedulingRequestResourceConfigExt_v1610__Type, SchedulingRequestResourceConfigExt_v1610__cond a -> SchedulingRequestResourceConfigExt_v1610__list_cond (SchedulingRequestResourceConfigExt_v1610__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SchedulingRequestResourceConfigExt_v1610__helper2 : (forall a : SchedulingRequestResourceConfigExt_v1610__Type, SchedulingRequestResourceConfigExt_v1610__F2 (SchedulingRequestResourceConfigExt_v1610__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SchedulingRequestResourceConfigExt_v1610__helper3 : (forall b : SchedulingRequestResourceConfigExt_v1610__list_type, SchedulingRequestResourceConfigExt_v1610__list_cond b -> SchedulingRequestResourceConfigExt_v1610__cond (SchedulingRequestResourceConfigExt_v1610__F2 b) /\ SchedulingRequestResourceConfigExt_v1610__F1 (SchedulingRequestResourceConfigExt_v1610__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SchedulingRequestResourceConfigExt_v1610__cond, SchedulingRequestResourceConfigExt_v1610__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SchedulingRequestResourceConfigExt_v1610__Format : T_Format SchedulingRequestResourceConfigExt_v1610__Type SchedulingRequestResourceConfigExt_v1610__cond :=
 proj2_format SchedulingRequestResourceConfigExt_v1610__cond SchedulingRequestResourceConfigExt_v1610__list_format  SchedulingRequestResourceConfigExt_v1610__F1 SchedulingRequestResourceConfigExt_v1610__F2 SchedulingRequestResourceConfigExt_v1610__helper1 SchedulingRequestResourceConfigExt_v1610__helper2 SchedulingRequestResourceConfigExt_v1610__helper3.

Opaque SchedulingRequestResourceConfigExt_v1610__cond SchedulingRequestResourceConfigExt_v1610__Format.

