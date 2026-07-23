Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SHR_Cause_r17__t304_cause_r17__Type : Set :=
 | SHR_Cause_r17__t304_cause_r17__true
.
Definition SHR_Cause_r17__t304_cause_r17__cond := (fun (_ : SHR_Cause_r17__t304_cause_r17__Type) => True).
Lemma SHR_Cause_r17__t304_cause_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SHR_Cause_r17__t304_cause_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SHR_Cause_r17__t304_cause_r17__nat__helper.

Definition SHR_Cause_r17__t304_cause_r17__F1 t :=
  match t with
  | SHR_Cause_r17__t304_cause_r17__true => 0
  end.
Definition SHR_Cause_r17__t304_cause_r17__F2 n :=
  match n with
  | 0 => SHR_Cause_r17__t304_cause_r17__true
  | _ => SHR_Cause_r17__t304_cause_r17__true
  end.
Lemma SHR_Cause_r17__t304_cause_r17__F1F2 : forall x : SHR_Cause_r17__t304_cause_r17__Type, (SHR_Cause_r17__t304_cause_r17__F1 x <= 0) /\ SHR_Cause_r17__t304_cause_r17__F2 (SHR_Cause_r17__t304_cause_r17__F1 x) = x. imp_solve. Qed.
Lemma SHR_Cause_r17__t304_cause_r17__F2F1 : forall (y : nat) (H : y <= 0), SHR_Cause_r17__t304_cause_r17__F1 (SHR_Cause_r17__t304_cause_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SHR_Cause_r17__t310_cause_r17__Type : Set :=
 | SHR_Cause_r17__t310_cause_r17__true
.
Definition SHR_Cause_r17__t310_cause_r17__cond := (fun (_ : SHR_Cause_r17__t310_cause_r17__Type) => True).
Lemma SHR_Cause_r17__t310_cause_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SHR_Cause_r17__t310_cause_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SHR_Cause_r17__t310_cause_r17__nat__helper.

Definition SHR_Cause_r17__t310_cause_r17__F1 t :=
  match t with
  | SHR_Cause_r17__t310_cause_r17__true => 0
  end.
Definition SHR_Cause_r17__t310_cause_r17__F2 n :=
  match n with
  | 0 => SHR_Cause_r17__t310_cause_r17__true
  | _ => SHR_Cause_r17__t310_cause_r17__true
  end.
Lemma SHR_Cause_r17__t310_cause_r17__F1F2 : forall x : SHR_Cause_r17__t310_cause_r17__Type, (SHR_Cause_r17__t310_cause_r17__F1 x <= 0) /\ SHR_Cause_r17__t310_cause_r17__F2 (SHR_Cause_r17__t310_cause_r17__F1 x) = x. imp_solve. Qed.
Lemma SHR_Cause_r17__t310_cause_r17__F2F1 : forall (y : nat) (H : y <= 0), SHR_Cause_r17__t310_cause_r17__F1 (SHR_Cause_r17__t310_cause_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SHR_Cause_r17__t312_cause_r17__Type : Set :=
 | SHR_Cause_r17__t312_cause_r17__true
.
Definition SHR_Cause_r17__t312_cause_r17__cond := (fun (_ : SHR_Cause_r17__t312_cause_r17__Type) => True).
Lemma SHR_Cause_r17__t312_cause_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SHR_Cause_r17__t312_cause_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SHR_Cause_r17__t312_cause_r17__nat__helper.

Definition SHR_Cause_r17__t312_cause_r17__F1 t :=
  match t with
  | SHR_Cause_r17__t312_cause_r17__true => 0
  end.
Definition SHR_Cause_r17__t312_cause_r17__F2 n :=
  match n with
  | 0 => SHR_Cause_r17__t312_cause_r17__true
  | _ => SHR_Cause_r17__t312_cause_r17__true
  end.
Lemma SHR_Cause_r17__t312_cause_r17__F1F2 : forall x : SHR_Cause_r17__t312_cause_r17__Type, (SHR_Cause_r17__t312_cause_r17__F1 x <= 0) /\ SHR_Cause_r17__t312_cause_r17__F2 (SHR_Cause_r17__t312_cause_r17__F1 x) = x. imp_solve. Qed.
Lemma SHR_Cause_r17__t312_cause_r17__F2F1 : forall (y : nat) (H : y <= 0), SHR_Cause_r17__t312_cause_r17__F1 (SHR_Cause_r17__t312_cause_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SHR_Cause_r17__sourceDAPS_Failure_r17__Type : Set :=
 | SHR_Cause_r17__sourceDAPS_Failure_r17__true
.
Definition SHR_Cause_r17__sourceDAPS_Failure_r17__cond := (fun (_ : SHR_Cause_r17__sourceDAPS_Failure_r17__Type) => True).
Lemma SHR_Cause_r17__sourceDAPS_Failure_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SHR_Cause_r17__sourceDAPS_Failure_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SHR_Cause_r17__sourceDAPS_Failure_r17__nat__helper.

Definition SHR_Cause_r17__sourceDAPS_Failure_r17__F1 t :=
  match t with
  | SHR_Cause_r17__sourceDAPS_Failure_r17__true => 0
  end.
Definition SHR_Cause_r17__sourceDAPS_Failure_r17__F2 n :=
  match n with
  | 0 => SHR_Cause_r17__sourceDAPS_Failure_r17__true
  | _ => SHR_Cause_r17__sourceDAPS_Failure_r17__true
  end.
Lemma SHR_Cause_r17__sourceDAPS_Failure_r17__F1F2 : forall x : SHR_Cause_r17__sourceDAPS_Failure_r17__Type, (SHR_Cause_r17__sourceDAPS_Failure_r17__F1 x <= 0) /\ SHR_Cause_r17__sourceDAPS_Failure_r17__F2 (SHR_Cause_r17__sourceDAPS_Failure_r17__F1 x) = x. imp_solve. Qed.
Lemma SHR_Cause_r17__sourceDAPS_Failure_r17__F2F1 : forall (y : nat) (H : y <= 0), SHR_Cause_r17__sourceDAPS_Failure_r17__F1 (SHR_Cause_r17__sourceDAPS_Failure_r17__F2 y) = y. enum_solve H y. Qed.

Record SHR_Cause_r17__Type : Set :=
  make__SHR_Cause_r17__Type {
    SHR_Cause_r17__t304_cause_r17 : option SHR_Cause_r17__t304_cause_r17__Type ;
    SHR_Cause_r17__t310_cause_r17 : option SHR_Cause_r17__t310_cause_r17__Type ;
    SHR_Cause_r17__t312_cause_r17 : option SHR_Cause_r17__t312_cause_r17__Type ;
    SHR_Cause_r17__sourceDAPS_Failure_r17 : option SHR_Cause_r17__sourceDAPS_Failure_r17__Type ;
}.
Definition SHR_Cause_r17__root_list : list seq_elem := (
 Opt SHR_Cause_r17__t304_cause_r17__Type SHR_Cause_r17__t304_cause_r17__cond ::
 Opt SHR_Cause_r17__t310_cause_r17__Type SHR_Cause_r17__t310_cause_r17__cond ::
 Opt SHR_Cause_r17__t312_cause_r17__Type SHR_Cause_r17__t312_cause_r17__cond ::
 Opt SHR_Cause_r17__sourceDAPS_Failure_r17__Type SHR_Cause_r17__sourceDAPS_Failure_r17__cond ::
 nil).
Definition SHR_Cause_r17__ext_list : list typ := (
  nil).
Definition SHR_Cause_r17__cond (z : SHR_Cause_r17__Type) := 
(  opt_cond SHR_Cause_r17__t304_cause_r17__cond (SHR_Cause_r17__t304_cause_r17 z) /\
  opt_cond SHR_Cause_r17__t310_cause_r17__cond (SHR_Cause_r17__t310_cause_r17 z) /\
  opt_cond SHR_Cause_r17__t312_cause_r17__cond (SHR_Cause_r17__t312_cause_r17 z) /\
  opt_cond SHR_Cause_r17__sourceDAPS_Failure_r17__cond (SHR_Cause_r17__sourceDAPS_Failure_r17 z) /\
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
Definition SHR_Cause_r17__t304_cause_r17__Format : T_Format SHR_Cause_r17__t304_cause_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SHR_Cause_r17__t304_cause_r17__nat__Format SHR_Cause_r17__t304_cause_r17__F1 SHR_Cause_r17__t304_cause_r17__F2 SHR_Cause_r17__t304_cause_r17__F1F2 SHR_Cause_r17__t304_cause_r17__F2F1.

Opaque SHR_Cause_r17__t304_cause_r17__cond SHR_Cause_r17__t304_cause_r17__Format.

Definition SHR_Cause_r17__t310_cause_r17__Format : T_Format SHR_Cause_r17__t310_cause_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SHR_Cause_r17__t310_cause_r17__nat__Format SHR_Cause_r17__t310_cause_r17__F1 SHR_Cause_r17__t310_cause_r17__F2 SHR_Cause_r17__t310_cause_r17__F1F2 SHR_Cause_r17__t310_cause_r17__F2F1.

Opaque SHR_Cause_r17__t310_cause_r17__cond SHR_Cause_r17__t310_cause_r17__Format.

Definition SHR_Cause_r17__t312_cause_r17__Format : T_Format SHR_Cause_r17__t312_cause_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SHR_Cause_r17__t312_cause_r17__nat__Format SHR_Cause_r17__t312_cause_r17__F1 SHR_Cause_r17__t312_cause_r17__F2 SHR_Cause_r17__t312_cause_r17__F1F2 SHR_Cause_r17__t312_cause_r17__F2F1.

Opaque SHR_Cause_r17__t312_cause_r17__cond SHR_Cause_r17__t312_cause_r17__Format.

Definition SHR_Cause_r17__sourceDAPS_Failure_r17__Format : T_Format SHR_Cause_r17__sourceDAPS_Failure_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SHR_Cause_r17__sourceDAPS_Failure_r17__nat__Format SHR_Cause_r17__sourceDAPS_Failure_r17__F1 SHR_Cause_r17__sourceDAPS_Failure_r17__F2 SHR_Cause_r17__sourceDAPS_Failure_r17__F1F2 SHR_Cause_r17__sourceDAPS_Failure_r17__F2F1.

Opaque SHR_Cause_r17__sourceDAPS_Failure_r17__cond SHR_Cause_r17__sourceDAPS_Failure_r17__Format.


Definition SHR_Cause_r17__root_Format_Type := Eval cbn in seq_format_prod SHR_Cause_r17__root_list.
Definition SHR_Cause_r17__root_Format_list : SHR_Cause_r17__root_Format_Type :=
  (SHR_Cause_r17__t304_cause_r17__Format, (SHR_Cause_r17__t310_cause_r17__Format, (SHR_Cause_r17__t312_cause_r17__Format, (SHR_Cause_r17__sourceDAPS_Failure_r17__Format, unit_format)))).

Definition SHR_Cause_r17__ext_Format_Type := Eval cbn in get_formats SHR_Cause_r17__ext_list.
Definition SHR_Cause_r17__ext_Format_list : SHR_Cause_r17__ext_Format_Type :=
  unit__Format.

Definition SHR_Cause_r17__list_type : Set := (seq_type SHR_Cause_r17__root_list) * (seq_ext_type SHR_Cause_r17__ext_list).
Definition SHR_Cause_r17__list_cond (z : SHR_Cause_r17__list_type) : Prop :=
        (seq_cond SHR_Cause_r17__root_list (fst z)) /\ (seq_ext_cond SHR_Cause_r17__ext_list (snd z)).
Definition SHR_Cause_r17__list_format : T_Format SHR_Cause_r17__list_type SHR_Cause_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SHR_Cause_r17__root_list SHR_Cause_r17__root_Format_list SHR_Cause_r17__ext_list SHR_Cause_r17__ext_Format_list.

Opaque SHR_Cause_r17__list_format.
Definition SHR_Cause_r17__F1 (z : SHR_Cause_r17__Type) : SHR_Cause_r17__list_type :=
  (((SHR_Cause_r17__t304_cause_r17 z, (SHR_Cause_r17__t310_cause_r17 z, (SHR_Cause_r17__t312_cause_r17 z, (SHR_Cause_r17__sourceDAPS_Failure_r17 z, tt))))), (
tt)).
Definition SHR_Cause_r17__F2 (y : SHR_Cause_r17__list_type) : SHR_Cause_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SHR_Cause_r17__Type j0 j1 j2 j3
  end.
Definition SHR_Cause_r17__helper1 : (forall a : SHR_Cause_r17__Type, SHR_Cause_r17__cond a -> SHR_Cause_r17__list_cond (SHR_Cause_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SHR_Cause_r17__helper2 : (forall a : SHR_Cause_r17__Type, SHR_Cause_r17__F2 (SHR_Cause_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SHR_Cause_r17__helper3 : (forall b : SHR_Cause_r17__list_type, SHR_Cause_r17__list_cond b -> SHR_Cause_r17__cond (SHR_Cause_r17__F2 b) /\ SHR_Cause_r17__F1 (SHR_Cause_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SHR_Cause_r17__cond, SHR_Cause_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SHR_Cause_r17__Format : T_Format SHR_Cause_r17__Type SHR_Cause_r17__cond :=
 proj2_format SHR_Cause_r17__cond SHR_Cause_r17__list_format  SHR_Cause_r17__F1 SHR_Cause_r17__F2 SHR_Cause_r17__helper1 SHR_Cause_r17__helper2 SHR_Cause_r17__helper3.

Opaque SHR_Cause_r17__cond SHR_Cause_r17__Format.

