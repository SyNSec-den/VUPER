Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Inductive NonCellDefiningSSB_r17__ssb_Periodicity_r17__Type : Set :=
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms5
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms10
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms20
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms40
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms80
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms160
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__spare2
 | NonCellDefiningSSB_r17__ssb_Periodicity_r17__spare1
.
Definition NonCellDefiningSSB_r17__ssb_Periodicity_r17__cond := (fun (_ : NonCellDefiningSSB_r17__ssb_Periodicity_r17__Type) => True).
Lemma NonCellDefiningSSB_r17__ssb_Periodicity_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NonCellDefiningSSB_r17__ssb_Periodicity_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 NonCellDefiningSSB_r17__ssb_Periodicity_r17__nat__helper.

Definition NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1 t :=
  match t with
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms5 => 0
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms10 => 1
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms20 => 2
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms40 => 3
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms80 => 4
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms160 => 5
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__spare2 => 6
  | NonCellDefiningSSB_r17__ssb_Periodicity_r17__spare1 => 7
  end.
Definition NonCellDefiningSSB_r17__ssb_Periodicity_r17__F2 n :=
  match n with
  | 0 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms5
  | 1 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms10
  | 2 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms20
  | 3 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms40
  | 4 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms80
  | 5 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms160
  | 6 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__spare2
  | 7 => NonCellDefiningSSB_r17__ssb_Periodicity_r17__spare1
  | _ => NonCellDefiningSSB_r17__ssb_Periodicity_r17__ms5
  end.
Lemma NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1F2 : forall x : NonCellDefiningSSB_r17__ssb_Periodicity_r17__Type, (NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1 x <= 7) /\ NonCellDefiningSSB_r17__ssb_Periodicity_r17__F2 (NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1 x) = x. imp_solve. Qed.
Lemma NonCellDefiningSSB_r17__ssb_Periodicity_r17__F2F1 : forall (y : nat) (H : y <= 7), NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1 (NonCellDefiningSSB_r17__ssb_Periodicity_r17__F2 y) = y. enum_solve H y. Qed.

Inductive NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Type : Set :=
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms5
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms10
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms15
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms20
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms40
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms80
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__spare2
 | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__spare1
.
Definition NonCellDefiningSSB_r17__ssb_TimeOffset_r17__cond := (fun (_ : NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Type) => True).
Lemma NonCellDefiningSSB_r17__ssb_TimeOffset_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NonCellDefiningSSB_r17__ssb_TimeOffset_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 NonCellDefiningSSB_r17__ssb_TimeOffset_r17__nat__helper.

Definition NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1 t :=
  match t with
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms5 => 0
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms10 => 1
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms15 => 2
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms20 => 3
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms40 => 4
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms80 => 5
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__spare2 => 6
  | NonCellDefiningSSB_r17__ssb_TimeOffset_r17__spare1 => 7
  end.
Definition NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F2 n :=
  match n with
  | 0 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms5
  | 1 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms10
  | 2 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms15
  | 3 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms20
  | 4 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms40
  | 5 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms80
  | 6 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__spare2
  | 7 => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__spare1
  | _ => NonCellDefiningSSB_r17__ssb_TimeOffset_r17__ms5
  end.
Lemma NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1F2 : forall x : NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Type, (NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1 x <= 7) /\ NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F2 (NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1 x) = x. imp_solve. Qed.
Lemma NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F2F1 : forall (y : nat) (H : y <= 7), NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1 (NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F2 y) = y. enum_solve H y. Qed.

Record NonCellDefiningSSB_r17__Type : Set :=
  make__NonCellDefiningSSB_r17__Type {
    NonCellDefiningSSB_r17__absoluteFrequencySSB_r17 : ARFCN_ValueNR__Type ;
    NonCellDefiningSSB_r17__ssb_Periodicity_r17 : option NonCellDefiningSSB_r17__ssb_Periodicity_r17__Type ;
    NonCellDefiningSSB_r17__ssb_TimeOffset_r17 : option NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Type ;
}.
Definition NonCellDefiningSSB_r17__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt NonCellDefiningSSB_r17__ssb_Periodicity_r17__Type NonCellDefiningSSB_r17__ssb_Periodicity_r17__cond ::
 Opt NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Type NonCellDefiningSSB_r17__ssb_TimeOffset_r17__cond ::
 nil).
Definition NonCellDefiningSSB_r17__ext_list : list typ := (
  nil).
Definition NonCellDefiningSSB_r17__cond (z : NonCellDefiningSSB_r17__Type) := 
(  ARFCN_ValueNR__cond (NonCellDefiningSSB_r17__absoluteFrequencySSB_r17 z) /\
  opt_cond NonCellDefiningSSB_r17__ssb_Periodicity_r17__cond (NonCellDefiningSSB_r17__ssb_Periodicity_r17 z) /\
  opt_cond NonCellDefiningSSB_r17__ssb_TimeOffset_r17__cond (NonCellDefiningSSB_r17__ssb_TimeOffset_r17 z) /\
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
Definition NonCellDefiningSSB_r17__ssb_Periodicity_r17__Format : T_Format NonCellDefiningSSB_r17__ssb_Periodicity_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NonCellDefiningSSB_r17__ssb_Periodicity_r17__nat__Format NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1 NonCellDefiningSSB_r17__ssb_Periodicity_r17__F2 NonCellDefiningSSB_r17__ssb_Periodicity_r17__F1F2 NonCellDefiningSSB_r17__ssb_Periodicity_r17__F2F1.

Opaque NonCellDefiningSSB_r17__ssb_Periodicity_r17__cond NonCellDefiningSSB_r17__ssb_Periodicity_r17__Format.

Definition NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Format : T_Format NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NonCellDefiningSSB_r17__ssb_TimeOffset_r17__nat__Format NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1 NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F2 NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F1F2 NonCellDefiningSSB_r17__ssb_TimeOffset_r17__F2F1.

Opaque NonCellDefiningSSB_r17__ssb_TimeOffset_r17__cond NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Format.


Definition NonCellDefiningSSB_r17__root_Format_Type := Eval cbn in seq_format_prod NonCellDefiningSSB_r17__root_list.
Definition NonCellDefiningSSB_r17__root_Format_list : NonCellDefiningSSB_r17__root_Format_Type :=
  (ARFCN_ValueNR__Format, (NonCellDefiningSSB_r17__ssb_Periodicity_r17__Format, (NonCellDefiningSSB_r17__ssb_TimeOffset_r17__Format, unit_format))).

Definition NonCellDefiningSSB_r17__ext_Format_Type := Eval cbn in get_formats NonCellDefiningSSB_r17__ext_list.
Definition NonCellDefiningSSB_r17__ext_Format_list : NonCellDefiningSSB_r17__ext_Format_Type :=
  unit__Format.

Definition NonCellDefiningSSB_r17__list_type : Set := (seq_type NonCellDefiningSSB_r17__root_list) * (seq_ext_type NonCellDefiningSSB_r17__ext_list).
Definition NonCellDefiningSSB_r17__list_cond (z : NonCellDefiningSSB_r17__list_type) : Prop :=
        (seq_cond NonCellDefiningSSB_r17__root_list (fst z)) /\ (seq_ext_cond NonCellDefiningSSB_r17__ext_list (snd z)).
Definition NonCellDefiningSSB_r17__list_format : T_Format NonCellDefiningSSB_r17__list_type NonCellDefiningSSB_r17__list_cond :=
 (* Eval compute in *) seq_ext_format NonCellDefiningSSB_r17__root_list NonCellDefiningSSB_r17__root_Format_list NonCellDefiningSSB_r17__ext_list NonCellDefiningSSB_r17__ext_Format_list.

Opaque NonCellDefiningSSB_r17__list_format.
Definition NonCellDefiningSSB_r17__F1 (z : NonCellDefiningSSB_r17__Type) : NonCellDefiningSSB_r17__list_type :=
  (((NonCellDefiningSSB_r17__absoluteFrequencySSB_r17 z, (NonCellDefiningSSB_r17__ssb_Periodicity_r17 z, (NonCellDefiningSSB_r17__ssb_TimeOffset_r17 z, tt)))), (
tt)).
Definition NonCellDefiningSSB_r17__F2 (y : NonCellDefiningSSB_r17__list_type) : NonCellDefiningSSB_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__NonCellDefiningSSB_r17__Type j0 j1 j2
  end.
Definition NonCellDefiningSSB_r17__helper1 : (forall a : NonCellDefiningSSB_r17__Type, NonCellDefiningSSB_r17__cond a -> NonCellDefiningSSB_r17__list_cond (NonCellDefiningSSB_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NonCellDefiningSSB_r17__helper2 : (forall a : NonCellDefiningSSB_r17__Type, NonCellDefiningSSB_r17__F2 (NonCellDefiningSSB_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NonCellDefiningSSB_r17__helper3 : (forall b : NonCellDefiningSSB_r17__list_type, NonCellDefiningSSB_r17__list_cond b -> NonCellDefiningSSB_r17__cond (NonCellDefiningSSB_r17__F2 b) /\ NonCellDefiningSSB_r17__F1 (NonCellDefiningSSB_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NonCellDefiningSSB_r17__cond, NonCellDefiningSSB_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NonCellDefiningSSB_r17__Format : T_Format NonCellDefiningSSB_r17__Type NonCellDefiningSSB_r17__cond :=
 proj2_format NonCellDefiningSSB_r17__cond NonCellDefiningSSB_r17__list_format  NonCellDefiningSSB_r17__F1 NonCellDefiningSSB_r17__F2 NonCellDefiningSSB_r17__helper1 NonCellDefiningSSB_r17__helper2 NonCellDefiningSSB_r17__helper3.

Opaque NonCellDefiningSSB_r17__cond NonCellDefiningSSB_r17__Format.

