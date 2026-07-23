Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SDAP_Parameters__as_ReflectiveQoS__Type : Set :=
 | SDAP_Parameters__as_ReflectiveQoS__true
.
Definition SDAP_Parameters__as_ReflectiveQoS__cond := (fun (_ : SDAP_Parameters__as_ReflectiveQoS__Type) => True).
Lemma SDAP_Parameters__as_ReflectiveQoS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDAP_Parameters__as_ReflectiveQoS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SDAP_Parameters__as_ReflectiveQoS__nat__helper.

Definition SDAP_Parameters__as_ReflectiveQoS__F1 t :=
  match t with
  | SDAP_Parameters__as_ReflectiveQoS__true => 0
  end.
Definition SDAP_Parameters__as_ReflectiveQoS__F2 n :=
  match n with
  | 0 => SDAP_Parameters__as_ReflectiveQoS__true
  | _ => SDAP_Parameters__as_ReflectiveQoS__true
  end.
Lemma SDAP_Parameters__as_ReflectiveQoS__F1F2 : forall x : SDAP_Parameters__as_ReflectiveQoS__Type, (SDAP_Parameters__as_ReflectiveQoS__F1 x <= 0) /\ SDAP_Parameters__as_ReflectiveQoS__F2 (SDAP_Parameters__as_ReflectiveQoS__F1 x) = x. imp_solve. Qed.
Lemma SDAP_Parameters__as_ReflectiveQoS__F2F1 : forall (y : nat) (H : y <= 0), SDAP_Parameters__as_ReflectiveQoS__F1 (SDAP_Parameters__as_ReflectiveQoS__F2 y) = y. enum_solve H y. Qed.

Inductive SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Type : Set :=
 | SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__supported
.
Definition SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__cond := (fun (_ : SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Type) => True).
Lemma SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__nat__helper.

Definition SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1 t :=
  match t with
  | SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__supported => 0
  end.
Definition SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F2 n :=
  match n with
  | 0 => SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__supported
  | _ => SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__supported
  end.
Lemma SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1F2 : forall x : SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Type, (SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1 x <= 0) /\ SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F2 (SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1 (SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Type : Set :=
 | SDAP_Parameters__ext0O__sdapHeaderIAB_r16__supported
.
Definition SDAP_Parameters__ext0O__sdapHeaderIAB_r16__cond := (fun (_ : SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Type) => True).
Lemma SDAP_Parameters__ext0O__sdapHeaderIAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SDAP_Parameters__ext0O__sdapHeaderIAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SDAP_Parameters__ext0O__sdapHeaderIAB_r16__nat__helper.

Definition SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1 t :=
  match t with
  | SDAP_Parameters__ext0O__sdapHeaderIAB_r16__supported => 0
  end.
Definition SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F2 n :=
  match n with
  | 0 => SDAP_Parameters__ext0O__sdapHeaderIAB_r16__supported
  | _ => SDAP_Parameters__ext0O__sdapHeaderIAB_r16__supported
  end.
Lemma SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1F2 : forall x : SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Type, (SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1 x <= 0) /\ SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F2 (SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1 x) = x. imp_solve. Qed.
Lemma SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F2F1 : forall (y : nat) (H : y <= 0), SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1 (SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F2 y) = y. enum_solve H y. Qed.

Record SDAP_Parameters__ext0O__Type : Set :=
  make__SDAP_Parameters__ext0O__Type {
    SDAP_Parameters__ext0O__sdap_QOS_IAB_r16 : option SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Type ;
    SDAP_Parameters__ext0O__sdapHeaderIAB_r16 : option SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Type ;
}.
Definition SDAP_Parameters__ext0O__list := (
 Opt SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Type SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__cond ::
 Opt SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Type SDAP_Parameters__ext0O__sdapHeaderIAB_r16__cond ::
 nil).
Definition SDAP_Parameters__ext0O__cond z := 
  opt_cond SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__cond (SDAP_Parameters__ext0O__sdap_QOS_IAB_r16 z) /\
  opt_cond SDAP_Parameters__ext0O__sdapHeaderIAB_r16__cond (SDAP_Parameters__ext0O__sdapHeaderIAB_r16 z) /\
  True.

Definition SDAP_Parameters__ext0__Type := SDAP_Parameters__ext0O__Type.
Definition SDAP_Parameters__ext0__cond := SDAP_Parameters__ext0O__cond.

Record SDAP_Parameters__Type : Set :=
  make__SDAP_Parameters__Type {
    SDAP_Parameters__as_ReflectiveQoS : option SDAP_Parameters__as_ReflectiveQoS__Type ;
    SDAP_Parameters__ext0 : option SDAP_Parameters__ext0__Type ;
}.
Definition SDAP_Parameters__root_list : list seq_elem := (
 Opt SDAP_Parameters__as_ReflectiveQoS__Type SDAP_Parameters__as_ReflectiveQoS__cond ::
 nil).
Definition SDAP_Parameters__ext_list : list typ := (
  typ_cons SDAP_Parameters__ext0__Type SDAP_Parameters__ext0__cond ::
  nil).
Definition SDAP_Parameters__cond (z : SDAP_Parameters__Type) := 
(  opt_cond SDAP_Parameters__as_ReflectiveQoS__cond (SDAP_Parameters__as_ReflectiveQoS z) /\
  True) /\ 
(  opt_cond SDAP_Parameters__ext0__cond (SDAP_Parameters__ext0 z) /\
  True).


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
Definition SDAP_Parameters__as_ReflectiveQoS__Format : T_Format SDAP_Parameters__as_ReflectiveQoS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDAP_Parameters__as_ReflectiveQoS__nat__Format SDAP_Parameters__as_ReflectiveQoS__F1 SDAP_Parameters__as_ReflectiveQoS__F2 SDAP_Parameters__as_ReflectiveQoS__F1F2 SDAP_Parameters__as_ReflectiveQoS__F2F1.

Opaque SDAP_Parameters__as_ReflectiveQoS__cond SDAP_Parameters__as_ReflectiveQoS__Format.

Definition SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Format : T_Format SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__nat__Format SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1 SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F2 SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F1F2 SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__F2F1.

Opaque SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__cond SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Format.

Definition SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Format : T_Format SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SDAP_Parameters__ext0O__sdapHeaderIAB_r16__nat__Format SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1 SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F2 SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F1F2 SDAP_Parameters__ext0O__sdapHeaderIAB_r16__F2F1.

Opaque SDAP_Parameters__ext0O__sdapHeaderIAB_r16__cond SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Format.


Definition SDAP_Parameters__ext0O__Format_Type := Eval cbn in seq_format_prod SDAP_Parameters__ext0O__list.
Definition SDAP_Parameters__ext0O__Format_list : SDAP_Parameters__ext0O__Format_Type :=
  (SDAP_Parameters__ext0O__sdap_QOS_IAB_r16__Format, (SDAP_Parameters__ext0O__sdapHeaderIAB_r16__Format, unit_format)).
Definition SDAP_Parameters__ext0O__list__Format := (*Eval compute in *) seq_format SDAP_Parameters__ext0O__list SDAP_Parameters__ext0O__Format_list.
Definition SDAP_Parameters__ext0O__F1 z :=
  (SDAP_Parameters__ext0O__sdap_QOS_IAB_r16 z, (SDAP_Parameters__ext0O__sdapHeaderIAB_r16 z, tt)).
Definition SDAP_Parameters__ext0O__F2 (y : seq_type SDAP_Parameters__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SDAP_Parameters__ext0O__Type i0 i1
  end.
Lemma SDAP_Parameters__ext0O__F1F2_cond (z : SDAP_Parameters__ext0O__Type)
  : SDAP_Parameters__ext0O__cond z ->
  (seq_cond SDAP_Parameters__ext0O__list (SDAP_Parameters__ext0O__F1 z)).
intro H. unfold SDAP_Parameters__ext0O__cond in H. simpl. auto. Qed.
Lemma SDAP_Parameters__ext0O__F1F2_cond2 (z : SDAP_Parameters__ext0O__Type)
 : SDAP_Parameters__ext0O__F2 (SDAP_Parameters__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SDAP_Parameters__ext0O__F2F1_cond (y : seq_type SDAP_Parameters__ext0O__list)
  : seq_cond SDAP_Parameters__ext0O__list y ->
 (SDAP_Parameters__ext0O__cond (SDAP_Parameters__ext0O__F2 y)) /\  SDAP_Parameters__ext0O__F1 (SDAP_Parameters__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SDAP_Parameters__ext0O__cond. simpl in *. auto.
 - simpl. unfold SDAP_Parameters__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SDAP_Parameters__ext0O__Format : T_Format SDAP_Parameters__ext0O__Type SDAP_Parameters__ext0O__cond :=
        proj2_format  SDAP_Parameters__ext0O__cond SDAP_Parameters__ext0O__list__Format
    SDAP_Parameters__ext0O__F1 SDAP_Parameters__ext0O__F2 SDAP_Parameters__ext0O__F1F2_cond  SDAP_Parameters__ext0O__F1F2_cond2 SDAP_Parameters__ext0O__F2F1_cond.
Opaque SDAP_Parameters__ext0O__cond SDAP_Parameters__ext0O__Format.

Definition SDAP_Parameters__ext0__check_all_none (b : SDAP_Parameters__ext0O__Type) : bool :=
match b with 
  | make__SDAP_Parameters__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition SDAP_Parameters__ext0__Format : T_Format SDAP_Parameters__ext0__Type SDAP_Parameters__ext0__cond :=
  restrict_add_format SDAP_Parameters__ext0__check_all_none SDAP_Parameters__ext0O__Format.

Opaque SDAP_Parameters__ext0__cond SDAP_Parameters__ext0__Format.


Definition SDAP_Parameters__root_Format_Type := Eval cbn in seq_format_prod SDAP_Parameters__root_list.
Definition SDAP_Parameters__root_Format_list : SDAP_Parameters__root_Format_Type :=
  (SDAP_Parameters__as_ReflectiveQoS__Format, unit_format).

Definition SDAP_Parameters__ext_Format_Type := Eval cbn in get_formats SDAP_Parameters__ext_list.
Definition SDAP_Parameters__ext_Format_list : SDAP_Parameters__ext_Format_Type :=
  (SDAP_Parameters__ext0__Format, unit__Format).

Definition SDAP_Parameters__list_type : Set := (seq_type SDAP_Parameters__root_list) * (seq_ext_type SDAP_Parameters__ext_list).
Definition SDAP_Parameters__list_cond (z : SDAP_Parameters__list_type) : Prop :=
        (seq_cond SDAP_Parameters__root_list (fst z)) /\ (seq_ext_cond SDAP_Parameters__ext_list (snd z)).
Definition SDAP_Parameters__list_format : T_Format SDAP_Parameters__list_type SDAP_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format SDAP_Parameters__root_list SDAP_Parameters__root_Format_list SDAP_Parameters__ext_list SDAP_Parameters__ext_Format_list.

Opaque SDAP_Parameters__list_format.
Definition SDAP_Parameters__F1 (z : SDAP_Parameters__Type) : SDAP_Parameters__list_type :=
  (((SDAP_Parameters__as_ReflectiveQoS z, tt)), (
(SDAP_Parameters__ext0 z, tt))).
Definition SDAP_Parameters__F2 (y : SDAP_Parameters__list_type) : SDAP_Parameters__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__SDAP_Parameters__Type j0 i0
  end.
Definition SDAP_Parameters__helper1 : (forall a : SDAP_Parameters__Type, SDAP_Parameters__cond a -> SDAP_Parameters__list_cond (SDAP_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SDAP_Parameters__helper2 : (forall a : SDAP_Parameters__Type, SDAP_Parameters__F2 (SDAP_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SDAP_Parameters__helper3 : (forall b : SDAP_Parameters__list_type, SDAP_Parameters__list_cond b -> SDAP_Parameters__cond (SDAP_Parameters__F2 b) /\ SDAP_Parameters__F1 (SDAP_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SDAP_Parameters__cond, SDAP_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SDAP_Parameters__Format : T_Format SDAP_Parameters__Type SDAP_Parameters__cond :=
 proj2_format SDAP_Parameters__cond SDAP_Parameters__list_format  SDAP_Parameters__F1 SDAP_Parameters__F2 SDAP_Parameters__helper1 SDAP_Parameters__helper2 SDAP_Parameters__helper3.

Opaque SDAP_Parameters__cond SDAP_Parameters__Format.

