Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RLC_Parameters__am_WithShortSN__Type : Set :=
 | RLC_Parameters__am_WithShortSN__supported
.
Definition RLC_Parameters__am_WithShortSN__cond := (fun (_ : RLC_Parameters__am_WithShortSN__Type) => True).
Lemma RLC_Parameters__am_WithShortSN__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_Parameters__am_WithShortSN__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_Parameters__am_WithShortSN__nat__helper.

Definition RLC_Parameters__am_WithShortSN__F1 t :=
  match t with
  | RLC_Parameters__am_WithShortSN__supported => 0
  end.
Definition RLC_Parameters__am_WithShortSN__F2 n :=
  match n with
  | 0 => RLC_Parameters__am_WithShortSN__supported
  | _ => RLC_Parameters__am_WithShortSN__supported
  end.
Lemma RLC_Parameters__am_WithShortSN__F1F2 : forall x : RLC_Parameters__am_WithShortSN__Type, (RLC_Parameters__am_WithShortSN__F1 x <= 0) /\ RLC_Parameters__am_WithShortSN__F2 (RLC_Parameters__am_WithShortSN__F1 x) = x. imp_solve. Qed.
Lemma RLC_Parameters__am_WithShortSN__F2F1 : forall (y : nat) (H : y <= 0), RLC_Parameters__am_WithShortSN__F1 (RLC_Parameters__am_WithShortSN__F2 y) = y. enum_solve H y. Qed.

Inductive RLC_Parameters__um_WithShortSN__Type : Set :=
 | RLC_Parameters__um_WithShortSN__supported
.
Definition RLC_Parameters__um_WithShortSN__cond := (fun (_ : RLC_Parameters__um_WithShortSN__Type) => True).
Lemma RLC_Parameters__um_WithShortSN__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_Parameters__um_WithShortSN__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_Parameters__um_WithShortSN__nat__helper.

Definition RLC_Parameters__um_WithShortSN__F1 t :=
  match t with
  | RLC_Parameters__um_WithShortSN__supported => 0
  end.
Definition RLC_Parameters__um_WithShortSN__F2 n :=
  match n with
  | 0 => RLC_Parameters__um_WithShortSN__supported
  | _ => RLC_Parameters__um_WithShortSN__supported
  end.
Lemma RLC_Parameters__um_WithShortSN__F1F2 : forall x : RLC_Parameters__um_WithShortSN__Type, (RLC_Parameters__um_WithShortSN__F1 x <= 0) /\ RLC_Parameters__um_WithShortSN__F2 (RLC_Parameters__um_WithShortSN__F1 x) = x. imp_solve. Qed.
Lemma RLC_Parameters__um_WithShortSN__F2F1 : forall (y : nat) (H : y <= 0), RLC_Parameters__um_WithShortSN__F1 (RLC_Parameters__um_WithShortSN__F2 y) = y. enum_solve H y. Qed.

Inductive RLC_Parameters__um_WithLongSN__Type : Set :=
 | RLC_Parameters__um_WithLongSN__supported
.
Definition RLC_Parameters__um_WithLongSN__cond := (fun (_ : RLC_Parameters__um_WithLongSN__Type) => True).
Lemma RLC_Parameters__um_WithLongSN__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_Parameters__um_WithLongSN__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_Parameters__um_WithLongSN__nat__helper.

Definition RLC_Parameters__um_WithLongSN__F1 t :=
  match t with
  | RLC_Parameters__um_WithLongSN__supported => 0
  end.
Definition RLC_Parameters__um_WithLongSN__F2 n :=
  match n with
  | 0 => RLC_Parameters__um_WithLongSN__supported
  | _ => RLC_Parameters__um_WithLongSN__supported
  end.
Lemma RLC_Parameters__um_WithLongSN__F1F2 : forall x : RLC_Parameters__um_WithLongSN__Type, (RLC_Parameters__um_WithLongSN__F1 x <= 0) /\ RLC_Parameters__um_WithLongSN__F2 (RLC_Parameters__um_WithLongSN__F1 x) = x. imp_solve. Qed.
Lemma RLC_Parameters__um_WithLongSN__F2F1 : forall (y : nat) (H : y <= 0), RLC_Parameters__um_WithLongSN__F1 (RLC_Parameters__um_WithLongSN__F2 y) = y. enum_solve H y. Qed.

Inductive RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Type : Set :=
 | RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__supported
.
Definition RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__cond := (fun (_ : RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Type) => True).
Lemma RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__nat__helper.

Definition RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1 t :=
  match t with
  | RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__supported => 0
  end.
Definition RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F2 n :=
  match n with
  | 0 => RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__supported
  | _ => RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__supported
  end.
Lemma RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1F2 : forall x : RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Type, (RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1 x <= 0) /\ RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F2 (RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1 x) = x. imp_solve. Qed.
Lemma RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F2F1 : forall (y : nat) (H : y <= 0), RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1 (RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Type : Set :=
 | RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__supported
.
Definition RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__cond := (fun (_ : RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Type) => True).
Lemma RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__nat__helper.

Definition RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1 t :=
  match t with
  | RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__supported => 0
  end.
Definition RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F2 n :=
  match n with
  | 0 => RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__supported
  | _ => RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__supported
  end.
Lemma RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1F2 : forall x : RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Type, (RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1 x <= 0) /\ RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F2 (RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1 x) = x. imp_solve. Qed.
Lemma RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F2F1 : forall (y : nat) (H : y <= 0), RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1 (RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F2 y) = y. enum_solve H y. Qed.

Record RLC_Parameters__ext0O__Type : Set :=
  make__RLC_Parameters__ext0O__Type {
    RLC_Parameters__ext0O__extendedT_PollRetransmit_r16 : option RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Type ;
    RLC_Parameters__ext0O__extendedT_StatusProhibit_r16 : option RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Type ;
}.
Definition RLC_Parameters__ext0O__list := (
 Opt RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Type RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__cond ::
 Opt RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Type RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__cond ::
 nil).
Definition RLC_Parameters__ext0O__cond z := 
  opt_cond RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__cond (RLC_Parameters__ext0O__extendedT_PollRetransmit_r16 z) /\
  opt_cond RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__cond (RLC_Parameters__ext0O__extendedT_StatusProhibit_r16 z) /\
  True.

Definition RLC_Parameters__ext0__Type := RLC_Parameters__ext0O__Type.
Definition RLC_Parameters__ext0__cond := RLC_Parameters__ext0O__cond.

Inductive RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Type : Set :=
 | RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__supported
.
Definition RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__cond := (fun (_ : RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Type) => True).
Lemma RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__nat__helper.

Definition RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1 t :=
  match t with
  | RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__supported => 0
  end.
Definition RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F2 n :=
  match n with
  | 0 => RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__supported
  | _ => RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__supported
  end.
Lemma RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1F2 : forall x : RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Type, (RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1 x <= 0) /\ RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F2 (RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F2F1 : forall (y : nat) (H : y <= 0), RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1 (RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F2 y) = y. enum_solve H y. Qed.

Record RLC_Parameters__ext1O__Type : Set :=
  make__RLC_Parameters__ext1O__Type {
    RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17 : option RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Type ;
}.
Definition RLC_Parameters__ext1O__list := (
 Opt RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Type RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__cond ::
 nil).
Definition RLC_Parameters__ext1O__cond z := 
  opt_cond RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__cond (RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17 z) /\
  True.

Definition RLC_Parameters__ext1__Type := RLC_Parameters__ext1O__Type.
Definition RLC_Parameters__ext1__cond := RLC_Parameters__ext1O__cond.

Record RLC_Parameters__Type : Set :=
  make__RLC_Parameters__Type {
    RLC_Parameters__am_WithShortSN : option RLC_Parameters__am_WithShortSN__Type ;
    RLC_Parameters__um_WithShortSN : option RLC_Parameters__um_WithShortSN__Type ;
    RLC_Parameters__um_WithLongSN : option RLC_Parameters__um_WithLongSN__Type ;
    RLC_Parameters__ext0 : option RLC_Parameters__ext0__Type ;
    RLC_Parameters__ext1 : option RLC_Parameters__ext1__Type ;
}.
Definition RLC_Parameters__root_list : list seq_elem := (
 Opt RLC_Parameters__am_WithShortSN__Type RLC_Parameters__am_WithShortSN__cond ::
 Opt RLC_Parameters__um_WithShortSN__Type RLC_Parameters__um_WithShortSN__cond ::
 Opt RLC_Parameters__um_WithLongSN__Type RLC_Parameters__um_WithLongSN__cond ::
 nil).
Definition RLC_Parameters__ext_list : list typ := (
  typ_cons RLC_Parameters__ext0__Type RLC_Parameters__ext0__cond ::
  typ_cons RLC_Parameters__ext1__Type RLC_Parameters__ext1__cond ::
  nil).
Definition RLC_Parameters__cond (z : RLC_Parameters__Type) := 
(  opt_cond RLC_Parameters__am_WithShortSN__cond (RLC_Parameters__am_WithShortSN z) /\
  opt_cond RLC_Parameters__um_WithShortSN__cond (RLC_Parameters__um_WithShortSN z) /\
  opt_cond RLC_Parameters__um_WithLongSN__cond (RLC_Parameters__um_WithLongSN z) /\
  True) /\ 
(  opt_cond RLC_Parameters__ext0__cond (RLC_Parameters__ext0 z) /\
  opt_cond RLC_Parameters__ext1__cond (RLC_Parameters__ext1 z) /\
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
Definition RLC_Parameters__am_WithShortSN__Format : T_Format RLC_Parameters__am_WithShortSN__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_Parameters__am_WithShortSN__nat__Format RLC_Parameters__am_WithShortSN__F1 RLC_Parameters__am_WithShortSN__F2 RLC_Parameters__am_WithShortSN__F1F2 RLC_Parameters__am_WithShortSN__F2F1.

Opaque RLC_Parameters__am_WithShortSN__cond RLC_Parameters__am_WithShortSN__Format.

Definition RLC_Parameters__um_WithShortSN__Format : T_Format RLC_Parameters__um_WithShortSN__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_Parameters__um_WithShortSN__nat__Format RLC_Parameters__um_WithShortSN__F1 RLC_Parameters__um_WithShortSN__F2 RLC_Parameters__um_WithShortSN__F1F2 RLC_Parameters__um_WithShortSN__F2F1.

Opaque RLC_Parameters__um_WithShortSN__cond RLC_Parameters__um_WithShortSN__Format.

Definition RLC_Parameters__um_WithLongSN__Format : T_Format RLC_Parameters__um_WithLongSN__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_Parameters__um_WithLongSN__nat__Format RLC_Parameters__um_WithLongSN__F1 RLC_Parameters__um_WithLongSN__F2 RLC_Parameters__um_WithLongSN__F1F2 RLC_Parameters__um_WithLongSN__F2F1.

Opaque RLC_Parameters__um_WithLongSN__cond RLC_Parameters__um_WithLongSN__Format.

Definition RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Format : T_Format RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__nat__Format RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1 RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F2 RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F1F2 RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__F2F1.

Opaque RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__cond RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Format.

Definition RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Format : T_Format RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__nat__Format RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1 RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F2 RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F1F2 RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__F2F1.

Opaque RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__cond RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Format.


Definition RLC_Parameters__ext0O__Format_Type := Eval cbn in seq_format_prod RLC_Parameters__ext0O__list.
Definition RLC_Parameters__ext0O__Format_list : RLC_Parameters__ext0O__Format_Type :=
  (RLC_Parameters__ext0O__extendedT_PollRetransmit_r16__Format, (RLC_Parameters__ext0O__extendedT_StatusProhibit_r16__Format, unit_format)).
Definition RLC_Parameters__ext0O__list__Format := (*Eval compute in *) seq_format RLC_Parameters__ext0O__list RLC_Parameters__ext0O__Format_list.
Definition RLC_Parameters__ext0O__F1 z :=
  (RLC_Parameters__ext0O__extendedT_PollRetransmit_r16 z, (RLC_Parameters__ext0O__extendedT_StatusProhibit_r16 z, tt)).
Definition RLC_Parameters__ext0O__F2 (y : seq_type RLC_Parameters__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RLC_Parameters__ext0O__Type i0 i1
  end.
Lemma RLC_Parameters__ext0O__F1F2_cond (z : RLC_Parameters__ext0O__Type)
  : RLC_Parameters__ext0O__cond z ->
  (seq_cond RLC_Parameters__ext0O__list (RLC_Parameters__ext0O__F1 z)).
intro H. unfold RLC_Parameters__ext0O__cond in H. simpl. auto. Qed.
Lemma RLC_Parameters__ext0O__F1F2_cond2 (z : RLC_Parameters__ext0O__Type)
 : RLC_Parameters__ext0O__F2 (RLC_Parameters__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_Parameters__ext0O__F2F1_cond (y : seq_type RLC_Parameters__ext0O__list)
  : seq_cond RLC_Parameters__ext0O__list y ->
 (RLC_Parameters__ext0O__cond (RLC_Parameters__ext0O__F2 y)) /\  RLC_Parameters__ext0O__F1 (RLC_Parameters__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_Parameters__ext0O__cond. simpl in *. auto.
 - simpl. unfold RLC_Parameters__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_Parameters__ext0O__Format : T_Format RLC_Parameters__ext0O__Type RLC_Parameters__ext0O__cond :=
        proj2_format  RLC_Parameters__ext0O__cond RLC_Parameters__ext0O__list__Format
    RLC_Parameters__ext0O__F1 RLC_Parameters__ext0O__F2 RLC_Parameters__ext0O__F1F2_cond  RLC_Parameters__ext0O__F1F2_cond2 RLC_Parameters__ext0O__F2F1_cond.
Opaque RLC_Parameters__ext0O__cond RLC_Parameters__ext0O__Format.

Definition RLC_Parameters__ext0__check_all_none (b : RLC_Parameters__ext0O__Type) : bool :=
match b with 
  | make__RLC_Parameters__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition RLC_Parameters__ext0__Format : T_Format RLC_Parameters__ext0__Type RLC_Parameters__ext0__cond :=
  restrict_add_format RLC_Parameters__ext0__check_all_none RLC_Parameters__ext0O__Format.

Opaque RLC_Parameters__ext0__cond RLC_Parameters__ext0__Format.

Definition RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Format : T_Format RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__nat__Format RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1 RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F2 RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F1F2 RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__F2F1.

Opaque RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__cond RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Format.


Definition RLC_Parameters__ext1O__Format_Type := Eval cbn in seq_format_prod RLC_Parameters__ext1O__list.
Definition RLC_Parameters__ext1O__Format_list : RLC_Parameters__ext1O__Format_Type :=
  (RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17__Format, unit_format).
Definition RLC_Parameters__ext1O__list__Format := (*Eval compute in *) seq_format RLC_Parameters__ext1O__list RLC_Parameters__ext1O__Format_list.
Definition RLC_Parameters__ext1O__F1 z :=
  (RLC_Parameters__ext1O__am_WithLongSN_RedCap_r17 z, tt).
Definition RLC_Parameters__ext1O__F2 (y : seq_type RLC_Parameters__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__RLC_Parameters__ext1O__Type i0
  end.
Lemma RLC_Parameters__ext1O__F1F2_cond (z : RLC_Parameters__ext1O__Type)
  : RLC_Parameters__ext1O__cond z ->
  (seq_cond RLC_Parameters__ext1O__list (RLC_Parameters__ext1O__F1 z)).
intro H. unfold RLC_Parameters__ext1O__cond in H. simpl. auto. Qed.
Lemma RLC_Parameters__ext1O__F1F2_cond2 (z : RLC_Parameters__ext1O__Type)
 : RLC_Parameters__ext1O__F2 (RLC_Parameters__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_Parameters__ext1O__F2F1_cond (y : seq_type RLC_Parameters__ext1O__list)
  : seq_cond RLC_Parameters__ext1O__list y ->
 (RLC_Parameters__ext1O__cond (RLC_Parameters__ext1O__F2 y)) /\  RLC_Parameters__ext1O__F1 (RLC_Parameters__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_Parameters__ext1O__cond. simpl in *. auto.
 - simpl. unfold RLC_Parameters__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_Parameters__ext1O__Format : T_Format RLC_Parameters__ext1O__Type RLC_Parameters__ext1O__cond :=
        proj2_format  RLC_Parameters__ext1O__cond RLC_Parameters__ext1O__list__Format
    RLC_Parameters__ext1O__F1 RLC_Parameters__ext1O__F2 RLC_Parameters__ext1O__F1F2_cond  RLC_Parameters__ext1O__F1F2_cond2 RLC_Parameters__ext1O__F2F1_cond.
Opaque RLC_Parameters__ext1O__cond RLC_Parameters__ext1O__Format.

Definition RLC_Parameters__ext1__check_all_none (b : RLC_Parameters__ext1O__Type) : bool :=
match b with 
  | make__RLC_Parameters__ext1O__Type None  => false 
  | _ => true 
 end.
Definition RLC_Parameters__ext1__Format : T_Format RLC_Parameters__ext1__Type RLC_Parameters__ext1__cond :=
  restrict_add_format RLC_Parameters__ext1__check_all_none RLC_Parameters__ext1O__Format.

Opaque RLC_Parameters__ext1__cond RLC_Parameters__ext1__Format.


Definition RLC_Parameters__root_Format_Type := Eval cbn in seq_format_prod RLC_Parameters__root_list.
Definition RLC_Parameters__root_Format_list : RLC_Parameters__root_Format_Type :=
  (RLC_Parameters__am_WithShortSN__Format, (RLC_Parameters__um_WithShortSN__Format, (RLC_Parameters__um_WithLongSN__Format, unit_format))).

Definition RLC_Parameters__ext_Format_Type := Eval cbn in get_formats RLC_Parameters__ext_list.
Definition RLC_Parameters__ext_Format_list : RLC_Parameters__ext_Format_Type :=
  (RLC_Parameters__ext0__Format, (RLC_Parameters__ext1__Format, unit__Format)).

Definition RLC_Parameters__list_type : Set := (seq_type RLC_Parameters__root_list) * (seq_ext_type RLC_Parameters__ext_list).
Definition RLC_Parameters__list_cond (z : RLC_Parameters__list_type) : Prop :=
        (seq_cond RLC_Parameters__root_list (fst z)) /\ (seq_ext_cond RLC_Parameters__ext_list (snd z)).
Definition RLC_Parameters__list_format : T_Format RLC_Parameters__list_type RLC_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format RLC_Parameters__root_list RLC_Parameters__root_Format_list RLC_Parameters__ext_list RLC_Parameters__ext_Format_list.

Opaque RLC_Parameters__list_format.
Definition RLC_Parameters__F1 (z : RLC_Parameters__Type) : RLC_Parameters__list_type :=
  (((RLC_Parameters__am_WithShortSN z, (RLC_Parameters__um_WithShortSN z, (RLC_Parameters__um_WithLongSN z, tt)))), (
(RLC_Parameters__ext0 z, (RLC_Parameters__ext1 z, tt)))).
Definition RLC_Parameters__F2 (y : RLC_Parameters__list_type) : RLC_Parameters__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, _)))=>
    make__RLC_Parameters__Type j0 j1 j2 i0 i1
  end.
Definition RLC_Parameters__helper1 : (forall a : RLC_Parameters__Type, RLC_Parameters__cond a -> RLC_Parameters__list_cond (RLC_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RLC_Parameters__helper2 : (forall a : RLC_Parameters__Type, RLC_Parameters__F2 (RLC_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RLC_Parameters__helper3 : (forall b : RLC_Parameters__list_type, RLC_Parameters__list_cond b -> RLC_Parameters__cond (RLC_Parameters__F2 b) /\ RLC_Parameters__F1 (RLC_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RLC_Parameters__cond, RLC_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RLC_Parameters__Format : T_Format RLC_Parameters__Type RLC_Parameters__cond :=
 proj2_format RLC_Parameters__cond RLC_Parameters__list_format  RLC_Parameters__F1 RLC_Parameters__F2 RLC_Parameters__helper1 RLC_Parameters__helper2 RLC_Parameters__helper3.

Opaque RLC_Parameters__cond RLC_Parameters__Format.

