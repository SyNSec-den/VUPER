Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SBAS_ID_r16__sbas_id_r16__root__Type : Set :=
 | SBAS_ID_r16__sbas_id_r16__root__waas
 | SBAS_ID_r16__sbas_id_r16__root__egnos
 | SBAS_ID_r16__sbas_id_r16__root__msas
 | SBAS_ID_r16__sbas_id_r16__root__gagan
.
Definition SBAS_ID_r16__sbas_id_r16__root__cond := (fun (_ : SBAS_ID_r16__sbas_id_r16__root__Type) => True).
Lemma SBAS_ID_r16__sbas_id_r16__root__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SBAS_ID_r16__sbas_id_r16__root__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SBAS_ID_r16__sbas_id_r16__root__nat__helper.

Definition SBAS_ID_r16__sbas_id_r16__root__F1 t :=
  match t with
  | SBAS_ID_r16__sbas_id_r16__root__waas => 0
  | SBAS_ID_r16__sbas_id_r16__root__egnos => 1
  | SBAS_ID_r16__sbas_id_r16__root__msas => 2
  | SBAS_ID_r16__sbas_id_r16__root__gagan => 3
  end.
Definition SBAS_ID_r16__sbas_id_r16__root__F2 n :=
  match n with
  | 0 => SBAS_ID_r16__sbas_id_r16__root__waas
  | 1 => SBAS_ID_r16__sbas_id_r16__root__egnos
  | 2 => SBAS_ID_r16__sbas_id_r16__root__msas
  | 3 => SBAS_ID_r16__sbas_id_r16__root__gagan
  | _ => SBAS_ID_r16__sbas_id_r16__root__waas
  end.
Lemma SBAS_ID_r16__sbas_id_r16__root__F1F2 : forall x : SBAS_ID_r16__sbas_id_r16__root__Type, (SBAS_ID_r16__sbas_id_r16__root__F1 x <= 3) /\ SBAS_ID_r16__sbas_id_r16__root__F2 (SBAS_ID_r16__sbas_id_r16__root__F1 x) = x. imp_solve. Qed.
Lemma SBAS_ID_r16__sbas_id_r16__root__F2F1 : forall (y : nat) (H : y <= 3), SBAS_ID_r16__sbas_id_r16__root__F1 (SBAS_ID_r16__sbas_id_r16__root__F2 y) = y. enum_solve H y. Qed.

Definition SBAS_ID_r16__sbas_id_r16__ext__Type : Set := Empty_set.
Definition SBAS_ID_r16__sbas_id_r16__ext__cond := (fun (_ : SBAS_ID_r16__sbas_id_r16__ext__Type) => True).
Definition SBAS_ID_r16__sbas_id_r16__Type : Set := SBAS_ID_r16__sbas_id_r16__root__Type + SBAS_ID_r16__sbas_id_r16__ext__Type.
Definition SBAS_ID_r16__sbas_id_r16__cond := sum_cond SBAS_ID_r16__sbas_id_r16__root__cond SBAS_ID_r16__sbas_id_r16__ext__cond.

Record SBAS_ID_r16__Type : Set :=
  make__SBAS_ID_r16__Type {
    SBAS_ID_r16__sbas_id_r16 : SBAS_ID_r16__sbas_id_r16__Type ;
}.
Definition SBAS_ID_r16__root_list : list seq_elem := (
 Nor SBAS_ID_r16__sbas_id_r16__Type SBAS_ID_r16__sbas_id_r16__cond ::
 nil).
Definition SBAS_ID_r16__ext_list : list typ := (
  nil).
Definition SBAS_ID_r16__cond (z : SBAS_ID_r16__Type) := 
(  SBAS_ID_r16__sbas_id_r16__cond (SBAS_ID_r16__sbas_id_r16 z) /\
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
Definition SBAS_ID_r16__sbas_id_r16__root__Format : T_Format SBAS_ID_r16__sbas_id_r16__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format SBAS_ID_r16__sbas_id_r16__root__nat__Format SBAS_ID_r16__sbas_id_r16__root__F1 SBAS_ID_r16__sbas_id_r16__root__F2 SBAS_ID_r16__sbas_id_r16__root__F1F2 SBAS_ID_r16__sbas_id_r16__root__F2F1.

Opaque SBAS_ID_r16__sbas_id_r16__root__cond SBAS_ID_r16__sbas_id_r16__root__Format.

Definition SBAS_ID_r16__sbas_id_r16__ext__Format : T_Format SBAS_ID_r16__sbas_id_r16__ext__Type SBAS_ID_r16__sbas_id_r16__ext__cond := empty_format.

Opaque SBAS_ID_r16__sbas_id_r16__ext__cond SBAS_ID_r16__sbas_id_r16__ext__Format.

Definition SBAS_ID_r16__sbas_id_r16__Format : T_Format SBAS_ID_r16__sbas_id_r16__Type SBAS_ID_r16__sbas_id_r16__cond := sum_format SBAS_ID_r16__sbas_id_r16__root__Format SBAS_ID_r16__sbas_id_r16__ext__Format.
Opaque SBAS_ID_r16__sbas_id_r16__cond SBAS_ID_r16__sbas_id_r16__Format.

Opaque SBAS_ID_r16__sbas_id_r16__cond SBAS_ID_r16__sbas_id_r16__Format.


Definition SBAS_ID_r16__root_Format_Type := Eval cbn in seq_format_prod SBAS_ID_r16__root_list.
Definition SBAS_ID_r16__root_Format_list : SBAS_ID_r16__root_Format_Type :=
  (SBAS_ID_r16__sbas_id_r16__Format, unit_format).

Definition SBAS_ID_r16__ext_Format_Type := Eval cbn in get_formats SBAS_ID_r16__ext_list.
Definition SBAS_ID_r16__ext_Format_list : SBAS_ID_r16__ext_Format_Type :=
  unit__Format.

Definition SBAS_ID_r16__list_type : Set := (seq_type SBAS_ID_r16__root_list) * (seq_ext_type SBAS_ID_r16__ext_list).
Definition SBAS_ID_r16__list_cond (z : SBAS_ID_r16__list_type) : Prop :=
        (seq_cond SBAS_ID_r16__root_list (fst z)) /\ (seq_ext_cond SBAS_ID_r16__ext_list (snd z)).
Definition SBAS_ID_r16__list_format : T_Format SBAS_ID_r16__list_type SBAS_ID_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SBAS_ID_r16__root_list SBAS_ID_r16__root_Format_list SBAS_ID_r16__ext_list SBAS_ID_r16__ext_Format_list.

Opaque SBAS_ID_r16__list_format.
Definition SBAS_ID_r16__F1 (z : SBAS_ID_r16__Type) : SBAS_ID_r16__list_type :=
  (((SBAS_ID_r16__sbas_id_r16 z, tt)), (
tt)).
Definition SBAS_ID_r16__F2 (y : SBAS_ID_r16__list_type) : SBAS_ID_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__SBAS_ID_r16__Type j0
  end.
Definition SBAS_ID_r16__helper1 : (forall a : SBAS_ID_r16__Type, SBAS_ID_r16__cond a -> SBAS_ID_r16__list_cond (SBAS_ID_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SBAS_ID_r16__helper2 : (forall a : SBAS_ID_r16__Type, SBAS_ID_r16__F2 (SBAS_ID_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SBAS_ID_r16__helper3 : (forall b : SBAS_ID_r16__list_type, SBAS_ID_r16__list_cond b -> SBAS_ID_r16__cond (SBAS_ID_r16__F2 b) /\ SBAS_ID_r16__F1 (SBAS_ID_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SBAS_ID_r16__cond, SBAS_ID_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SBAS_ID_r16__Format : T_Format SBAS_ID_r16__Type SBAS_ID_r16__cond :=
 proj2_format SBAS_ID_r16__cond SBAS_ID_r16__list_format  SBAS_ID_r16__F1 SBAS_ID_r16__F2 SBAS_ID_r16__helper1 SBAS_ID_r16__helper2 SBAS_ID_r16__helper3.

Opaque SBAS_ID_r16__cond SBAS_ID_r16__Format.

