Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SemiStaticChannelAccessConfig_r16__period__Type : Set :=
 | SemiStaticChannelAccessConfig_r16__period__ms1
 | SemiStaticChannelAccessConfig_r16__period__ms2
 | SemiStaticChannelAccessConfig_r16__period__ms2dot5
 | SemiStaticChannelAccessConfig_r16__period__ms4
 | SemiStaticChannelAccessConfig_r16__period__ms5
 | SemiStaticChannelAccessConfig_r16__period__ms10
.
Definition SemiStaticChannelAccessConfig_r16__period__cond := (fun (_ : SemiStaticChannelAccessConfig_r16__period__Type) => True).
Lemma SemiStaticChannelAccessConfig_r16__period__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SemiStaticChannelAccessConfig_r16__period__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 SemiStaticChannelAccessConfig_r16__period__nat__helper.

Definition SemiStaticChannelAccessConfig_r16__period__F1 t :=
  match t with
  | SemiStaticChannelAccessConfig_r16__period__ms1 => 0
  | SemiStaticChannelAccessConfig_r16__period__ms2 => 1
  | SemiStaticChannelAccessConfig_r16__period__ms2dot5 => 2
  | SemiStaticChannelAccessConfig_r16__period__ms4 => 3
  | SemiStaticChannelAccessConfig_r16__period__ms5 => 4
  | SemiStaticChannelAccessConfig_r16__period__ms10 => 5
  end.
Definition SemiStaticChannelAccessConfig_r16__period__F2 n :=
  match n with
  | 0 => SemiStaticChannelAccessConfig_r16__period__ms1
  | 1 => SemiStaticChannelAccessConfig_r16__period__ms2
  | 2 => SemiStaticChannelAccessConfig_r16__period__ms2dot5
  | 3 => SemiStaticChannelAccessConfig_r16__period__ms4
  | 4 => SemiStaticChannelAccessConfig_r16__period__ms5
  | 5 => SemiStaticChannelAccessConfig_r16__period__ms10
  | _ => SemiStaticChannelAccessConfig_r16__period__ms1
  end.
Lemma SemiStaticChannelAccessConfig_r16__period__F1F2 : forall x : SemiStaticChannelAccessConfig_r16__period__Type, (SemiStaticChannelAccessConfig_r16__period__F1 x <= 5) /\ SemiStaticChannelAccessConfig_r16__period__F2 (SemiStaticChannelAccessConfig_r16__period__F1 x) = x. imp_solve. Qed.
Lemma SemiStaticChannelAccessConfig_r16__period__F2F1 : forall (y : nat) (H : y <= 5), SemiStaticChannelAccessConfig_r16__period__F1 (SemiStaticChannelAccessConfig_r16__period__F2 y) = y. enum_solve H y. Qed.

Record SemiStaticChannelAccessConfig_r16__Type : Set :=
  make__SemiStaticChannelAccessConfig_r16__Type {
    SemiStaticChannelAccessConfig_r16__period : SemiStaticChannelAccessConfig_r16__period__Type ;
}.
Definition SemiStaticChannelAccessConfig_r16__list := (
 Nor SemiStaticChannelAccessConfig_r16__period__Type SemiStaticChannelAccessConfig_r16__period__cond ::
 nil).
Definition SemiStaticChannelAccessConfig_r16__cond z := 
  SemiStaticChannelAccessConfig_r16__period__cond (SemiStaticChannelAccessConfig_r16__period z) /\
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
Definition SemiStaticChannelAccessConfig_r16__period__Format : T_Format SemiStaticChannelAccessConfig_r16__period__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SemiStaticChannelAccessConfig_r16__period__nat__Format SemiStaticChannelAccessConfig_r16__period__F1 SemiStaticChannelAccessConfig_r16__period__F2 SemiStaticChannelAccessConfig_r16__period__F1F2 SemiStaticChannelAccessConfig_r16__period__F2F1.

Opaque SemiStaticChannelAccessConfig_r16__period__cond SemiStaticChannelAccessConfig_r16__period__Format.


Definition SemiStaticChannelAccessConfig_r16__Format_Type := Eval cbn in seq_format_prod SemiStaticChannelAccessConfig_r16__list.
Definition SemiStaticChannelAccessConfig_r16__Format_list : SemiStaticChannelAccessConfig_r16__Format_Type :=
  (SemiStaticChannelAccessConfig_r16__period__Format, unit_format).
Definition SemiStaticChannelAccessConfig_r16__list__Format := (*Eval compute in *) seq_format SemiStaticChannelAccessConfig_r16__list SemiStaticChannelAccessConfig_r16__Format_list.
Definition SemiStaticChannelAccessConfig_r16__F1 z :=
  (SemiStaticChannelAccessConfig_r16__period z, tt).
Definition SemiStaticChannelAccessConfig_r16__F2 (y : seq_type SemiStaticChannelAccessConfig_r16__list) :=
  match y with
  | (i0, _)=>
    make__SemiStaticChannelAccessConfig_r16__Type i0
  end.
Lemma SemiStaticChannelAccessConfig_r16__F1F2_cond (z : SemiStaticChannelAccessConfig_r16__Type)
  : SemiStaticChannelAccessConfig_r16__cond z ->
  (seq_cond SemiStaticChannelAccessConfig_r16__list (SemiStaticChannelAccessConfig_r16__F1 z)).
intro H. unfold SemiStaticChannelAccessConfig_r16__cond in H. simpl. auto. Qed.
Lemma SemiStaticChannelAccessConfig_r16__F1F2_cond2 (z : SemiStaticChannelAccessConfig_r16__Type)
 : SemiStaticChannelAccessConfig_r16__F2 (SemiStaticChannelAccessConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SemiStaticChannelAccessConfig_r16__F2F1_cond (y : seq_type SemiStaticChannelAccessConfig_r16__list)
  : seq_cond SemiStaticChannelAccessConfig_r16__list y ->
 (SemiStaticChannelAccessConfig_r16__cond (SemiStaticChannelAccessConfig_r16__F2 y)) /\  SemiStaticChannelAccessConfig_r16__F1 (SemiStaticChannelAccessConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SemiStaticChannelAccessConfig_r16__cond. simpl in *. auto.
 - simpl. unfold SemiStaticChannelAccessConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SemiStaticChannelAccessConfig_r16__Format : T_Format SemiStaticChannelAccessConfig_r16__Type SemiStaticChannelAccessConfig_r16__cond :=
        proj2_format  SemiStaticChannelAccessConfig_r16__cond SemiStaticChannelAccessConfig_r16__list__Format
    SemiStaticChannelAccessConfig_r16__F1 SemiStaticChannelAccessConfig_r16__F2 SemiStaticChannelAccessConfig_r16__F1F2_cond  SemiStaticChannelAccessConfig_r16__F1F2_cond2 SemiStaticChannelAccessConfig_r16__F2F1_cond.
Opaque SemiStaticChannelAccessConfig_r16__cond SemiStaticChannelAccessConfig_r16__Format.

