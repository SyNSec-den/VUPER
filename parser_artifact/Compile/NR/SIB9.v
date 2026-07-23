Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SIB9__timeInfo__timeInfoUTC__helper1 : (0 <= 549755813887)%Z.  lia. Qed.
Lemma SIB9__timeInfo__timeInfoUTC__helper2 : to_bit_sz (Z.to_nat (549755813887 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (549755813887 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB9__timeInfo__timeInfoUTC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB9__timeInfo__timeInfoUTC__Type := Z.
Definition SIB9__timeInfo__timeInfoUTC__cond := (fun z => (0 <= z <= 549755813887)%Z).
Definition SIB9__timeInfo__dayLightSavingTime__Type := bit_string_fixed.
Definition SIB9__timeInfo__dayLightSavingTime__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Lemma SIB9__timeInfo__leapSeconds__helper1 : (-127 <= 128)%Z.  lia. Qed.
Lemma SIB9__timeInfo__leapSeconds__helper2 : to_bit_sz (Z.to_nat (128 - -127)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - -127))%Z). { apply Zorder.Zle_minus_le_0. apply SIB9__timeInfo__leapSeconds__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB9__timeInfo__leapSeconds__Type := Z.
Definition SIB9__timeInfo__leapSeconds__cond := (fun z => (-127 <= z <= 128)%Z).
Lemma SIB9__timeInfo__localTimeOffset__helper1 : (-63 <= 64)%Z.  lia. Qed.
Lemma SIB9__timeInfo__localTimeOffset__helper2 : to_bit_sz (Z.to_nat (64 - -63)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - -63))%Z). { apply Zorder.Zle_minus_le_0. apply SIB9__timeInfo__localTimeOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB9__timeInfo__localTimeOffset__Type := Z.
Definition SIB9__timeInfo__localTimeOffset__cond := (fun z => (-63 <= z <= 64)%Z).
Record SIB9__timeInfo__Type : Set :=
  make__SIB9__timeInfo__Type {
    SIB9__timeInfo__timeInfoUTC : Z ;
    SIB9__timeInfo__dayLightSavingTime : option SIB9__timeInfo__dayLightSavingTime__Type ;
    SIB9__timeInfo__leapSeconds : option Z ;
    SIB9__timeInfo__localTimeOffset : option Z ;
}.
Definition SIB9__timeInfo__list := (
 Nor Z SIB9__timeInfo__timeInfoUTC__cond ::
 Opt SIB9__timeInfo__dayLightSavingTime__Type SIB9__timeInfo__dayLightSavingTime__cond ::
 Opt Z SIB9__timeInfo__leapSeconds__cond ::
 Opt Z SIB9__timeInfo__localTimeOffset__cond ::
 nil).
Definition SIB9__timeInfo__cond z := 
  SIB9__timeInfo__timeInfoUTC__cond (SIB9__timeInfo__timeInfoUTC z) /\
  opt_cond SIB9__timeInfo__dayLightSavingTime__cond (SIB9__timeInfo__dayLightSavingTime z) /\
  opt_cond SIB9__timeInfo__leapSeconds__cond (SIB9__timeInfo__leapSeconds z) /\
  opt_cond SIB9__timeInfo__localTimeOffset__cond (SIB9__timeInfo__localTimeOffset z) /\
  True.

Require Import NR.ReferenceTimeInfo_r16.

Opaque ReferenceTimeInfo_r16__cond ReferenceTimeInfo_r16__Format.

Record SIB9__ext0O__Type : Set :=
  make__SIB9__ext0O__Type {
    SIB9__ext0O__referenceTimeInfo_r16 : option ReferenceTimeInfo_r16__Type ;
}.
Definition SIB9__ext0O__list := (
 Opt ReferenceTimeInfo_r16__Type ReferenceTimeInfo_r16__cond ::
 nil).
Definition SIB9__ext0O__cond z := 
  opt_cond ReferenceTimeInfo_r16__cond (SIB9__ext0O__referenceTimeInfo_r16 z) /\
  True.

Definition SIB9__ext0__Type := SIB9__ext0O__Type.
Definition SIB9__ext0__cond := SIB9__ext0O__cond.

Record SIB9__Type : Set :=
  make__SIB9__Type {
    SIB9__timeInfo : option SIB9__timeInfo__Type ;
    SIB9__lateNonCriticalExtension : option octet_string ;
    SIB9__ext0 : option SIB9__ext0__Type ;
}.
Definition SIB9__root_list : list seq_elem := (
 Opt SIB9__timeInfo__Type SIB9__timeInfo__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB9__ext_list : list typ := (
  typ_cons SIB9__ext0__Type SIB9__ext0__cond ::
  nil).
Definition SIB9__cond (z : SIB9__Type) := 
(  opt_cond SIB9__timeInfo__cond (SIB9__timeInfo z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB9__lateNonCriticalExtension z) /\
  True) /\ 
(  opt_cond SIB9__ext0__cond (SIB9__ext0 z) /\
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
Definition SIB9__timeInfo__timeInfoUTC__Format : T_Format Z SIB9__timeInfo__timeInfoUTC__cond :=
 ranged_int_format (0) (549755813887) SIB9__timeInfo__timeInfoUTC__helper1 SIB9__timeInfo__timeInfoUTC__helper2.

Opaque SIB9__timeInfo__timeInfoUTC__cond SIB9__timeInfo__timeInfoUTC__Format.

Definition SIB9__timeInfo__dayLightSavingTime__Format : T_Format SIB9__timeInfo__dayLightSavingTime__Type SIB9__timeInfo__dayLightSavingTime__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque SIB9__timeInfo__dayLightSavingTime__cond SIB9__timeInfo__dayLightSavingTime__Format.

Definition SIB9__timeInfo__leapSeconds__Format : T_Format Z SIB9__timeInfo__leapSeconds__cond :=
 ranged_int_format (-127) (128) SIB9__timeInfo__leapSeconds__helper1 SIB9__timeInfo__leapSeconds__helper2.

Opaque SIB9__timeInfo__leapSeconds__cond SIB9__timeInfo__leapSeconds__Format.

Definition SIB9__timeInfo__localTimeOffset__Format : T_Format Z SIB9__timeInfo__localTimeOffset__cond :=
 ranged_int_format (-63) (64) SIB9__timeInfo__localTimeOffset__helper1 SIB9__timeInfo__localTimeOffset__helper2.

Opaque SIB9__timeInfo__localTimeOffset__cond SIB9__timeInfo__localTimeOffset__Format.


Definition SIB9__timeInfo__Format_Type := Eval cbn in seq_format_prod SIB9__timeInfo__list.
Definition SIB9__timeInfo__Format_list : SIB9__timeInfo__Format_Type :=
  (SIB9__timeInfo__timeInfoUTC__Format, (SIB9__timeInfo__dayLightSavingTime__Format, (SIB9__timeInfo__leapSeconds__Format, (SIB9__timeInfo__localTimeOffset__Format, unit_format)))).
Definition SIB9__timeInfo__list__Format := (*Eval compute in *) seq_format SIB9__timeInfo__list SIB9__timeInfo__Format_list.
Definition SIB9__timeInfo__F1 z :=
  (SIB9__timeInfo__timeInfoUTC z, (SIB9__timeInfo__dayLightSavingTime z, (SIB9__timeInfo__leapSeconds z, (SIB9__timeInfo__localTimeOffset z, tt)))).
Definition SIB9__timeInfo__F2 (y : seq_type SIB9__timeInfo__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SIB9__timeInfo__Type i0 i1 i2 i3
  end.
Lemma SIB9__timeInfo__F1F2_cond (z : SIB9__timeInfo__Type)
  : SIB9__timeInfo__cond z ->
  (seq_cond SIB9__timeInfo__list (SIB9__timeInfo__F1 z)).
intro H. unfold SIB9__timeInfo__cond in H. simpl. auto. Qed.
Lemma SIB9__timeInfo__F1F2_cond2 (z : SIB9__timeInfo__Type)
 : SIB9__timeInfo__F2 (SIB9__timeInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB9__timeInfo__F2F1_cond (y : seq_type SIB9__timeInfo__list)
  : seq_cond SIB9__timeInfo__list y ->
 (SIB9__timeInfo__cond (SIB9__timeInfo__F2 y)) /\  SIB9__timeInfo__F1 (SIB9__timeInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB9__timeInfo__cond. simpl in *. auto.
 - simpl. unfold SIB9__timeInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB9__timeInfo__Format : T_Format SIB9__timeInfo__Type SIB9__timeInfo__cond :=
        proj2_format  SIB9__timeInfo__cond SIB9__timeInfo__list__Format
    SIB9__timeInfo__F1 SIB9__timeInfo__F2 SIB9__timeInfo__F1F2_cond  SIB9__timeInfo__F1F2_cond2 SIB9__timeInfo__F2F1_cond.
Opaque SIB9__timeInfo__cond SIB9__timeInfo__Format.


Definition SIB9__ext0O__Format_Type := Eval cbn in seq_format_prod SIB9__ext0O__list.
Definition SIB9__ext0O__Format_list : SIB9__ext0O__Format_Type :=
  (ReferenceTimeInfo_r16__Format, unit_format).
Definition SIB9__ext0O__list__Format := (*Eval compute in *) seq_format SIB9__ext0O__list SIB9__ext0O__Format_list.
Definition SIB9__ext0O__F1 z :=
  (SIB9__ext0O__referenceTimeInfo_r16 z, tt).
Definition SIB9__ext0O__F2 (y : seq_type SIB9__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SIB9__ext0O__Type i0
  end.
Lemma SIB9__ext0O__F1F2_cond (z : SIB9__ext0O__Type)
  : SIB9__ext0O__cond z ->
  (seq_cond SIB9__ext0O__list (SIB9__ext0O__F1 z)).
intro H. unfold SIB9__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB9__ext0O__F1F2_cond2 (z : SIB9__ext0O__Type)
 : SIB9__ext0O__F2 (SIB9__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB9__ext0O__F2F1_cond (y : seq_type SIB9__ext0O__list)
  : seq_cond SIB9__ext0O__list y ->
 (SIB9__ext0O__cond (SIB9__ext0O__F2 y)) /\  SIB9__ext0O__F1 (SIB9__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB9__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB9__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB9__ext0O__Format : T_Format SIB9__ext0O__Type SIB9__ext0O__cond :=
        proj2_format  SIB9__ext0O__cond SIB9__ext0O__list__Format
    SIB9__ext0O__F1 SIB9__ext0O__F2 SIB9__ext0O__F1F2_cond  SIB9__ext0O__F1F2_cond2 SIB9__ext0O__F2F1_cond.
Opaque SIB9__ext0O__cond SIB9__ext0O__Format.

Definition SIB9__ext0__check_all_none (b : SIB9__ext0O__Type) : bool :=
match b with 
  | make__SIB9__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SIB9__ext0__Format : T_Format SIB9__ext0__Type SIB9__ext0__cond :=
  restrict_add_format SIB9__ext0__check_all_none SIB9__ext0O__Format.

Opaque SIB9__ext0__cond SIB9__ext0__Format.


Definition SIB9__root_Format_Type := Eval cbn in seq_format_prod SIB9__root_list.
Definition SIB9__root_Format_list : SIB9__root_Format_Type :=
  (SIB9__timeInfo__Format, (octet_string_nc__Format, unit_format)).

Definition SIB9__ext_Format_Type := Eval cbn in get_formats SIB9__ext_list.
Definition SIB9__ext_Format_list : SIB9__ext_Format_Type :=
  (SIB9__ext0__Format, unit__Format).

Definition SIB9__list_type : Set := (seq_type SIB9__root_list) * (seq_ext_type SIB9__ext_list).
Definition SIB9__list_cond (z : SIB9__list_type) : Prop :=
        (seq_cond SIB9__root_list (fst z)) /\ (seq_ext_cond SIB9__ext_list (snd z)).
Definition SIB9__list_format : T_Format SIB9__list_type SIB9__list_cond :=
 (* Eval compute in *) seq_ext_format SIB9__root_list SIB9__root_Format_list SIB9__ext_list SIB9__ext_Format_list.

Opaque SIB9__list_format.
Definition SIB9__F1 (z : SIB9__Type) : SIB9__list_type :=
  (((SIB9__timeInfo z, (SIB9__lateNonCriticalExtension z, tt))), (
(SIB9__ext0 z, tt))).
Definition SIB9__F2 (y : SIB9__list_type) : SIB9__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__SIB9__Type j0 j1 i0
  end.
Definition SIB9__helper1 : (forall a : SIB9__Type, SIB9__cond a -> SIB9__list_cond (SIB9__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB9__helper2 : (forall a : SIB9__Type, SIB9__F2 (SIB9__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB9__helper3 : (forall b : SIB9__list_type, SIB9__list_cond b -> SIB9__cond (SIB9__F2 b) /\ SIB9__F1 (SIB9__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB9__cond, SIB9__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB9__Format : T_Format SIB9__Type SIB9__cond :=
 proj2_format SIB9__cond SIB9__list_format  SIB9__F1 SIB9__F2 SIB9__helper1 SIB9__helper2 SIB9__helper3.

Opaque SIB9__cond SIB9__Format.

