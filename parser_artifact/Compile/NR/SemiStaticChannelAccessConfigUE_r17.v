Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Type : Set :=
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms1
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms2
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms2dot5
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms4
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms5
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms10
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__spare2
 | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__spare1
.
Definition SemiStaticChannelAccessConfigUE_r17__periodUE_r17__cond := (fun (_ : SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Type) => True).
Lemma SemiStaticChannelAccessConfigUE_r17__periodUE_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SemiStaticChannelAccessConfigUE_r17__periodUE_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SemiStaticChannelAccessConfigUE_r17__periodUE_r17__nat__helper.

Definition SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1 t :=
  match t with
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms1 => 0
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms2 => 1
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms2dot5 => 2
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms4 => 3
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms5 => 4
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms10 => 5
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__spare2 => 6
  | SemiStaticChannelAccessConfigUE_r17__periodUE_r17__spare1 => 7
  end.
Definition SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F2 n :=
  match n with
  | 0 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms1
  | 1 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms2
  | 2 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms2dot5
  | 3 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms4
  | 4 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms5
  | 5 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms10
  | 6 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__spare2
  | 7 => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__spare1
  | _ => SemiStaticChannelAccessConfigUE_r17__periodUE_r17__ms1
  end.
Lemma SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1F2 : forall x : SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Type, (SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1 x <= 7) /\ SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F2 (SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1 x) = x. imp_solve. Qed.
Lemma SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F2F1 : forall (y : nat) (H : y <= 7), SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1 (SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F2 y) = y. enum_solve H y. Qed.

Lemma SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__helper1 : (0 <= 559)%Z.  lia. Qed.
Lemma SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__helper2 : to_bit_sz (Z.to_nat (559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__Type := Z.
Definition SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__cond := (fun z => (0 <= z <= 559)%Z).
Record SemiStaticChannelAccessConfigUE_r17__Type : Set :=
  make__SemiStaticChannelAccessConfigUE_r17__Type {
    SemiStaticChannelAccessConfigUE_r17__periodUE_r17 : SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Type ;
    SemiStaticChannelAccessConfigUE_r17__offsetUE_r17 : Z ;
}.
Definition SemiStaticChannelAccessConfigUE_r17__list := (
 Nor SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Type SemiStaticChannelAccessConfigUE_r17__periodUE_r17__cond ::
 Nor Z SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__cond ::
 nil).
Definition SemiStaticChannelAccessConfigUE_r17__cond z := 
  SemiStaticChannelAccessConfigUE_r17__periodUE_r17__cond (SemiStaticChannelAccessConfigUE_r17__periodUE_r17 z) /\
  SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__cond (SemiStaticChannelAccessConfigUE_r17__offsetUE_r17 z) /\
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
Definition SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Format : T_Format SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SemiStaticChannelAccessConfigUE_r17__periodUE_r17__nat__Format SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1 SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F2 SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F1F2 SemiStaticChannelAccessConfigUE_r17__periodUE_r17__F2F1.

Opaque SemiStaticChannelAccessConfigUE_r17__periodUE_r17__cond SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Format.

Definition SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__Format : T_Format Z SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__cond :=
 ranged_int_format (0) (559) SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__helper1 SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__helper2.

Opaque SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__cond SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__Format.


Definition SemiStaticChannelAccessConfigUE_r17__Format_Type := Eval cbn in seq_format_prod SemiStaticChannelAccessConfigUE_r17__list.
Definition SemiStaticChannelAccessConfigUE_r17__Format_list : SemiStaticChannelAccessConfigUE_r17__Format_Type :=
  (SemiStaticChannelAccessConfigUE_r17__periodUE_r17__Format, (SemiStaticChannelAccessConfigUE_r17__offsetUE_r17__Format, unit_format)).
Definition SemiStaticChannelAccessConfigUE_r17__list__Format := (*Eval compute in *) seq_format SemiStaticChannelAccessConfigUE_r17__list SemiStaticChannelAccessConfigUE_r17__Format_list.
Definition SemiStaticChannelAccessConfigUE_r17__F1 z :=
  (SemiStaticChannelAccessConfigUE_r17__periodUE_r17 z, (SemiStaticChannelAccessConfigUE_r17__offsetUE_r17 z, tt)).
Definition SemiStaticChannelAccessConfigUE_r17__F2 (y : seq_type SemiStaticChannelAccessConfigUE_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SemiStaticChannelAccessConfigUE_r17__Type i0 i1
  end.
Lemma SemiStaticChannelAccessConfigUE_r17__F1F2_cond (z : SemiStaticChannelAccessConfigUE_r17__Type)
  : SemiStaticChannelAccessConfigUE_r17__cond z ->
  (seq_cond SemiStaticChannelAccessConfigUE_r17__list (SemiStaticChannelAccessConfigUE_r17__F1 z)).
intro H. unfold SemiStaticChannelAccessConfigUE_r17__cond in H. simpl. auto. Qed.
Lemma SemiStaticChannelAccessConfigUE_r17__F1F2_cond2 (z : SemiStaticChannelAccessConfigUE_r17__Type)
 : SemiStaticChannelAccessConfigUE_r17__F2 (SemiStaticChannelAccessConfigUE_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SemiStaticChannelAccessConfigUE_r17__F2F1_cond (y : seq_type SemiStaticChannelAccessConfigUE_r17__list)
  : seq_cond SemiStaticChannelAccessConfigUE_r17__list y ->
 (SemiStaticChannelAccessConfigUE_r17__cond (SemiStaticChannelAccessConfigUE_r17__F2 y)) /\  SemiStaticChannelAccessConfigUE_r17__F1 (SemiStaticChannelAccessConfigUE_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SemiStaticChannelAccessConfigUE_r17__cond. simpl in *. auto.
 - simpl. unfold SemiStaticChannelAccessConfigUE_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SemiStaticChannelAccessConfigUE_r17__Format : T_Format SemiStaticChannelAccessConfigUE_r17__Type SemiStaticChannelAccessConfigUE_r17__cond :=
        proj2_format  SemiStaticChannelAccessConfigUE_r17__cond SemiStaticChannelAccessConfigUE_r17__list__Format
    SemiStaticChannelAccessConfigUE_r17__F1 SemiStaticChannelAccessConfigUE_r17__F2 SemiStaticChannelAccessConfigUE_r17__F1F2_cond  SemiStaticChannelAccessConfigUE_r17__F1F2_cond2 SemiStaticChannelAccessConfigUE_r17__F2F1_cond.
Opaque SemiStaticChannelAccessConfigUE_r17__cond SemiStaticChannelAccessConfigUE_r17__Format.

