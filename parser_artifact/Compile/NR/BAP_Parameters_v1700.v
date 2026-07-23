Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Type : Set :=
 | BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__supported
.
Definition BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__cond := (fun (_ : BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Type) => True).
Lemma BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__nat__helper.

Definition BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1 t :=
  match t with
  | BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__supported => 0
  end.
Definition BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F2 n :=
  match n with
  | 0 => BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__supported
  | _ => BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__supported
  end.
Lemma BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1F2 : forall x : BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Type, (BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1 x <= 0) /\ BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F2 (BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1 x) = x. imp_solve. Qed.
Lemma BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F2F1 : forall (y : nat) (H : y <= 0), BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1 (BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Type : Set :=
 | BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__supported
.
Definition BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__cond := (fun (_ : BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Type) => True).
Lemma BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__nat__helper.

Definition BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1 t :=
  match t with
  | BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__supported => 0
  end.
Definition BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F2 n :=
  match n with
  | 0 => BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__supported
  | _ => BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__supported
  end.
Lemma BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1F2 : forall x : BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Type, (BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1 x <= 0) /\ BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F2 (BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1 x) = x. imp_solve. Qed.
Lemma BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F2F1 : forall (y : nat) (H : y <= 0), BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1 (BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F2 y) = y. enum_solve H y. Qed.

Record BAP_Parameters_v1700__Type : Set :=
  make__BAP_Parameters_v1700__Type {
    BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17 : option BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Type ;
    BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17 : option BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Type ;
}.
Definition BAP_Parameters_v1700__list := (
 Opt BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Type BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__cond ::
 Opt BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Type BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__cond ::
 nil).
Definition BAP_Parameters_v1700__cond z := 
  opt_cond BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__cond (BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17 z) /\
  opt_cond BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__cond (BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17 z) /\
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
Definition BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Format : T_Format BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__nat__Format BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1 BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F2 BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F1F2 BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__F2F1.

Opaque BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__cond BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Format.

Definition BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Format : T_Format BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__nat__Format BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1 BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F2 BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F1F2 BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__F2F1.

Opaque BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__cond BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Format.


Definition BAP_Parameters_v1700__Format_Type := Eval cbn in seq_format_prod BAP_Parameters_v1700__list.
Definition BAP_Parameters_v1700__Format_list : BAP_Parameters_v1700__Format_Type :=
  (BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17__Format, (BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17__Format, unit_format)).
Definition BAP_Parameters_v1700__list__Format := (*Eval compute in *) seq_format BAP_Parameters_v1700__list BAP_Parameters_v1700__Format_list.
Definition BAP_Parameters_v1700__F1 z :=
  (BAP_Parameters_v1700__bapHeaderRewriting_Rerouting_r17 z, (BAP_Parameters_v1700__bapHeaderRewriting_Routing_r17 z, tt)).
Definition BAP_Parameters_v1700__F2 (y : seq_type BAP_Parameters_v1700__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BAP_Parameters_v1700__Type i0 i1
  end.
Lemma BAP_Parameters_v1700__F1F2_cond (z : BAP_Parameters_v1700__Type)
  : BAP_Parameters_v1700__cond z ->
  (seq_cond BAP_Parameters_v1700__list (BAP_Parameters_v1700__F1 z)).
intro H. unfold BAP_Parameters_v1700__cond in H. simpl. auto. Qed.
Lemma BAP_Parameters_v1700__F1F2_cond2 (z : BAP_Parameters_v1700__Type)
 : BAP_Parameters_v1700__F2 (BAP_Parameters_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BAP_Parameters_v1700__F2F1_cond (y : seq_type BAP_Parameters_v1700__list)
  : seq_cond BAP_Parameters_v1700__list y ->
 (BAP_Parameters_v1700__cond (BAP_Parameters_v1700__F2 y)) /\  BAP_Parameters_v1700__F1 (BAP_Parameters_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BAP_Parameters_v1700__cond. simpl in *. auto.
 - simpl. unfold BAP_Parameters_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BAP_Parameters_v1700__Format : T_Format BAP_Parameters_v1700__Type BAP_Parameters_v1700__cond :=
        proj2_format  BAP_Parameters_v1700__cond BAP_Parameters_v1700__list__Format
    BAP_Parameters_v1700__F1 BAP_Parameters_v1700__F2 BAP_Parameters_v1700__F1F2_cond  BAP_Parameters_v1700__F1F2_cond2 BAP_Parameters_v1700__F2F1_cond.
Opaque BAP_Parameters_v1700__cond BAP_Parameters_v1700__Format.

