Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive GNSS_ID_r16__gnss_id_r16__root__Type : Set :=
 | GNSS_ID_r16__gnss_id_r16__root__gps
 | GNSS_ID_r16__gnss_id_r16__root__sbas
 | GNSS_ID_r16__gnss_id_r16__root__qzss
 | GNSS_ID_r16__gnss_id_r16__root__galileo
 | GNSS_ID_r16__gnss_id_r16__root__glonass
 | GNSS_ID_r16__gnss_id_r16__root__bds
.
Definition GNSS_ID_r16__gnss_id_r16__root__cond := (fun (_ : GNSS_ID_r16__gnss_id_r16__root__Type) => True).
Lemma GNSS_ID_r16__gnss_id_r16__root__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GNSS_ID_r16__gnss_id_r16__root__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 GNSS_ID_r16__gnss_id_r16__root__nat__helper.

Definition GNSS_ID_r16__gnss_id_r16__root__F1 t :=
  match t with
  | GNSS_ID_r16__gnss_id_r16__root__gps => 0
  | GNSS_ID_r16__gnss_id_r16__root__sbas => 1
  | GNSS_ID_r16__gnss_id_r16__root__qzss => 2
  | GNSS_ID_r16__gnss_id_r16__root__galileo => 3
  | GNSS_ID_r16__gnss_id_r16__root__glonass => 4
  | GNSS_ID_r16__gnss_id_r16__root__bds => 5
  end.
Definition GNSS_ID_r16__gnss_id_r16__root__F2 n :=
  match n with
  | 0 => GNSS_ID_r16__gnss_id_r16__root__gps
  | 1 => GNSS_ID_r16__gnss_id_r16__root__sbas
  | 2 => GNSS_ID_r16__gnss_id_r16__root__qzss
  | 3 => GNSS_ID_r16__gnss_id_r16__root__galileo
  | 4 => GNSS_ID_r16__gnss_id_r16__root__glonass
  | 5 => GNSS_ID_r16__gnss_id_r16__root__bds
  | _ => GNSS_ID_r16__gnss_id_r16__root__gps
  end.
Lemma GNSS_ID_r16__gnss_id_r16__root__F1F2 : forall x : GNSS_ID_r16__gnss_id_r16__root__Type, (GNSS_ID_r16__gnss_id_r16__root__F1 x <= 5) /\ GNSS_ID_r16__gnss_id_r16__root__F2 (GNSS_ID_r16__gnss_id_r16__root__F1 x) = x. imp_solve. Qed.
Lemma GNSS_ID_r16__gnss_id_r16__root__F2F1 : forall (y : nat) (H : y <= 5), GNSS_ID_r16__gnss_id_r16__root__F1 (GNSS_ID_r16__gnss_id_r16__root__F2 y) = y. enum_solve H y. Qed.

Definition GNSS_ID_r16__gnss_id_r16__ext__Type : Set := Empty_set.
Definition GNSS_ID_r16__gnss_id_r16__ext__cond := (fun (_ : GNSS_ID_r16__gnss_id_r16__ext__Type) => True).
Definition GNSS_ID_r16__gnss_id_r16__Type : Set := GNSS_ID_r16__gnss_id_r16__root__Type + GNSS_ID_r16__gnss_id_r16__ext__Type.
Definition GNSS_ID_r16__gnss_id_r16__cond := sum_cond GNSS_ID_r16__gnss_id_r16__root__cond GNSS_ID_r16__gnss_id_r16__ext__cond.

Record GNSS_ID_r16__Type : Set :=
  make__GNSS_ID_r16__Type {
    GNSS_ID_r16__gnss_id_r16 : GNSS_ID_r16__gnss_id_r16__Type ;
}.
Definition GNSS_ID_r16__root_list : list seq_elem := (
 Nor GNSS_ID_r16__gnss_id_r16__Type GNSS_ID_r16__gnss_id_r16__cond ::
 nil).
Definition GNSS_ID_r16__ext_list : list typ := (
  nil).
Definition GNSS_ID_r16__cond (z : GNSS_ID_r16__Type) := 
(  GNSS_ID_r16__gnss_id_r16__cond (GNSS_ID_r16__gnss_id_r16 z) /\
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
Definition GNSS_ID_r16__gnss_id_r16__root__Format : T_Format GNSS_ID_r16__gnss_id_r16__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format GNSS_ID_r16__gnss_id_r16__root__nat__Format GNSS_ID_r16__gnss_id_r16__root__F1 GNSS_ID_r16__gnss_id_r16__root__F2 GNSS_ID_r16__gnss_id_r16__root__F1F2 GNSS_ID_r16__gnss_id_r16__root__F2F1.

Opaque GNSS_ID_r16__gnss_id_r16__root__cond GNSS_ID_r16__gnss_id_r16__root__Format.

Definition GNSS_ID_r16__gnss_id_r16__ext__Format : T_Format GNSS_ID_r16__gnss_id_r16__ext__Type GNSS_ID_r16__gnss_id_r16__ext__cond := empty_format.

Opaque GNSS_ID_r16__gnss_id_r16__ext__cond GNSS_ID_r16__gnss_id_r16__ext__Format.

Definition GNSS_ID_r16__gnss_id_r16__Format : T_Format GNSS_ID_r16__gnss_id_r16__Type GNSS_ID_r16__gnss_id_r16__cond := sum_format GNSS_ID_r16__gnss_id_r16__root__Format GNSS_ID_r16__gnss_id_r16__ext__Format.
Opaque GNSS_ID_r16__gnss_id_r16__cond GNSS_ID_r16__gnss_id_r16__Format.

Opaque GNSS_ID_r16__gnss_id_r16__cond GNSS_ID_r16__gnss_id_r16__Format.


Definition GNSS_ID_r16__root_Format_Type := Eval cbn in seq_format_prod GNSS_ID_r16__root_list.
Definition GNSS_ID_r16__root_Format_list : GNSS_ID_r16__root_Format_Type :=
  (GNSS_ID_r16__gnss_id_r16__Format, unit_format).

Definition GNSS_ID_r16__ext_Format_Type := Eval cbn in get_formats GNSS_ID_r16__ext_list.
Definition GNSS_ID_r16__ext_Format_list : GNSS_ID_r16__ext_Format_Type :=
  unit__Format.

Definition GNSS_ID_r16__list_type : Set := (seq_type GNSS_ID_r16__root_list) * (seq_ext_type GNSS_ID_r16__ext_list).
Definition GNSS_ID_r16__list_cond (z : GNSS_ID_r16__list_type) : Prop :=
        (seq_cond GNSS_ID_r16__root_list (fst z)) /\ (seq_ext_cond GNSS_ID_r16__ext_list (snd z)).
Definition GNSS_ID_r16__list_format : T_Format GNSS_ID_r16__list_type GNSS_ID_r16__list_cond :=
 (* Eval compute in *) seq_ext_format GNSS_ID_r16__root_list GNSS_ID_r16__root_Format_list GNSS_ID_r16__ext_list GNSS_ID_r16__ext_Format_list.

Opaque GNSS_ID_r16__list_format.
Definition GNSS_ID_r16__F1 (z : GNSS_ID_r16__Type) : GNSS_ID_r16__list_type :=
  (((GNSS_ID_r16__gnss_id_r16 z, tt)), (
tt)).
Definition GNSS_ID_r16__F2 (y : GNSS_ID_r16__list_type) : GNSS_ID_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__GNSS_ID_r16__Type j0
  end.
Definition GNSS_ID_r16__helper1 : (forall a : GNSS_ID_r16__Type, GNSS_ID_r16__cond a -> GNSS_ID_r16__list_cond (GNSS_ID_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition GNSS_ID_r16__helper2 : (forall a : GNSS_ID_r16__Type, GNSS_ID_r16__F2 (GNSS_ID_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition GNSS_ID_r16__helper3 : (forall b : GNSS_ID_r16__list_type, GNSS_ID_r16__list_cond b -> GNSS_ID_r16__cond (GNSS_ID_r16__F2 b) /\ GNSS_ID_r16__F1 (GNSS_ID_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold GNSS_ID_r16__cond, GNSS_ID_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition GNSS_ID_r16__Format : T_Format GNSS_ID_r16__Type GNSS_ID_r16__cond :=
 proj2_format GNSS_ID_r16__cond GNSS_ID_r16__list_format  GNSS_ID_r16__F1 GNSS_ID_r16__F2 GNSS_ID_r16__helper1 GNSS_ID_r16__helper2 GNSS_ID_r16__helper3.

Opaque GNSS_ID_r16__cond GNSS_ID_r16__Format.

