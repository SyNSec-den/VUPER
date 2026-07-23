Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Type : Set :=
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0dot5
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s1
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s2
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s5
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s10
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s20
 | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s30
.
Definition OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__cond := (fun (_ : OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Type) => True).
Lemma OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__nat__helper.

Definition OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1 t :=
  match t with
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0 => 0
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0dot5 => 1
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s1 => 2
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s2 => 3
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s5 => 4
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s10 => 5
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s20 => 6
  | OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s30 => 7
  end.
Definition OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F2 n :=
  match n with
  | 0 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0
  | 1 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0dot5
  | 2 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s1
  | 3 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s2
  | 4 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s5
  | 5 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s10
  | 6 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s20
  | 7 => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s30
  | _ => OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__s0
  end.
Lemma OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1F2 : forall x : OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Type, (OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1 x <= 7) /\ OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F2 (OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F2F1 : forall (y : nat) (H : y <= 7), OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1 (OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F2 y) = y. enum_solve H y. Qed.

Record OnDemandSIB_Request_r16__Type : Set :=
  make__OnDemandSIB_Request_r16__Type {
    OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16 : OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Type ;
}.
Definition OnDemandSIB_Request_r16__list := (
 Nor OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Type OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__cond ::
 nil).
Definition OnDemandSIB_Request_r16__cond z := 
  OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__cond (OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16 z) /\
  True.


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
Definition OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Format : T_Format OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__nat__Format OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1 OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F2 OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F1F2 OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__F2F1.

Opaque OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__cond OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Format.


Definition OnDemandSIB_Request_r16__Format_Type := Eval cbn in seq_format_prod OnDemandSIB_Request_r16__list.
Definition OnDemandSIB_Request_r16__Format_list : OnDemandSIB_Request_r16__Format_Type :=
  (OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16__Format, unit_format).
Definition OnDemandSIB_Request_r16__list__Format := (*Eval compute in *) seq_format OnDemandSIB_Request_r16__list OnDemandSIB_Request_r16__Format_list.
Definition OnDemandSIB_Request_r16__F1 z :=
  (OnDemandSIB_Request_r16__onDemandSIB_RequestProhibitTimer_r16 z, tt).
Definition OnDemandSIB_Request_r16__F2 (y : seq_type OnDemandSIB_Request_r16__list) :=
  match y with
  | (i0, _)=>
    make__OnDemandSIB_Request_r16__Type i0
  end.
Lemma OnDemandSIB_Request_r16__F1F2_cond (z : OnDemandSIB_Request_r16__Type)
  : OnDemandSIB_Request_r16__cond z ->
  (seq_cond OnDemandSIB_Request_r16__list (OnDemandSIB_Request_r16__F1 z)).
intro H. unfold OnDemandSIB_Request_r16__cond in H. simpl. auto. Qed.
Lemma OnDemandSIB_Request_r16__F1F2_cond2 (z : OnDemandSIB_Request_r16__Type)
 : OnDemandSIB_Request_r16__F2 (OnDemandSIB_Request_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OnDemandSIB_Request_r16__F2F1_cond (y : seq_type OnDemandSIB_Request_r16__list)
  : seq_cond OnDemandSIB_Request_r16__list y ->
 (OnDemandSIB_Request_r16__cond (OnDemandSIB_Request_r16__F2 y)) /\  OnDemandSIB_Request_r16__F1 (OnDemandSIB_Request_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OnDemandSIB_Request_r16__cond. simpl in *. auto.
 - simpl. unfold OnDemandSIB_Request_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OnDemandSIB_Request_r16__Format : T_Format OnDemandSIB_Request_r16__Type OnDemandSIB_Request_r16__cond :=
        proj2_format  OnDemandSIB_Request_r16__cond OnDemandSIB_Request_r16__list__Format
    OnDemandSIB_Request_r16__F1 OnDemandSIB_Request_r16__F2 OnDemandSIB_Request_r16__F1F2_cond  OnDemandSIB_Request_r16__F1F2_cond2 OnDemandSIB_Request_r16__F2F1_cond.
Opaque OnDemandSIB_Request_r16__cond OnDemandSIB_Request_r16__Format.

