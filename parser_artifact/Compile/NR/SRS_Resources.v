Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SRS_Resources__maxNumberAperiodicSRS_PerBWP__Type : Set :=
 | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n1
 | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n2
 | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n4
 | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n8
 | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n16
.
Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP__cond := (fun (_ : SRS_Resources__maxNumberAperiodicSRS_PerBWP__Type) => True).
Lemma SRS_Resources__maxNumberAperiodicSRS_PerBWP__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SRS_Resources__maxNumberAperiodicSRS_PerBWP__nat__helper.

Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1 t :=
  match t with
  | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n1 => 0
  | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n2 => 1
  | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n4 => 2
  | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n8 => 3
  | SRS_Resources__maxNumberAperiodicSRS_PerBWP__n16 => 4
  end.
Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP__F2 n :=
  match n with
  | 0 => SRS_Resources__maxNumberAperiodicSRS_PerBWP__n1
  | 1 => SRS_Resources__maxNumberAperiodicSRS_PerBWP__n2
  | 2 => SRS_Resources__maxNumberAperiodicSRS_PerBWP__n4
  | 3 => SRS_Resources__maxNumberAperiodicSRS_PerBWP__n8
  | 4 => SRS_Resources__maxNumberAperiodicSRS_PerBWP__n16
  | _ => SRS_Resources__maxNumberAperiodicSRS_PerBWP__n1
  end.
Lemma SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1F2 : forall x : SRS_Resources__maxNumberAperiodicSRS_PerBWP__Type, (SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1 x <= 4) /\ SRS_Resources__maxNumberAperiodicSRS_PerBWP__F2 (SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resources__maxNumberAperiodicSRS_PerBWP__F2F1 : forall (y : nat) (H : y <= 4), SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1 (SRS_Resources__maxNumberAperiodicSRS_PerBWP__F2 y) = y. enum_solve H y. Qed.

Lemma SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__helper1 : (1 <= 6)%Z.  lia. Qed.
Lemma SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__helper2 : to_bit_sz (Z.to_nat (6 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__Type := Z.
Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__cond := (fun z => (1 <= z <= 6)%Z).
Inductive SRS_Resources__maxNumberPeriodicSRS_PerBWP__Type : Set :=
 | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n1
 | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n2
 | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n4
 | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n8
 | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n16
.
Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP__cond := (fun (_ : SRS_Resources__maxNumberPeriodicSRS_PerBWP__Type) => True).
Lemma SRS_Resources__maxNumberPeriodicSRS_PerBWP__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SRS_Resources__maxNumberPeriodicSRS_PerBWP__nat__helper.

Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1 t :=
  match t with
  | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n1 => 0
  | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n2 => 1
  | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n4 => 2
  | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n8 => 3
  | SRS_Resources__maxNumberPeriodicSRS_PerBWP__n16 => 4
  end.
Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP__F2 n :=
  match n with
  | 0 => SRS_Resources__maxNumberPeriodicSRS_PerBWP__n1
  | 1 => SRS_Resources__maxNumberPeriodicSRS_PerBWP__n2
  | 2 => SRS_Resources__maxNumberPeriodicSRS_PerBWP__n4
  | 3 => SRS_Resources__maxNumberPeriodicSRS_PerBWP__n8
  | 4 => SRS_Resources__maxNumberPeriodicSRS_PerBWP__n16
  | _ => SRS_Resources__maxNumberPeriodicSRS_PerBWP__n1
  end.
Lemma SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1F2 : forall x : SRS_Resources__maxNumberPeriodicSRS_PerBWP__Type, (SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1 x <= 4) /\ SRS_Resources__maxNumberPeriodicSRS_PerBWP__F2 (SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resources__maxNumberPeriodicSRS_PerBWP__F2F1 : forall (y : nat) (H : y <= 4), SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1 (SRS_Resources__maxNumberPeriodicSRS_PerBWP__F2 y) = y. enum_solve H y. Qed.

Lemma SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__helper1 : (1 <= 6)%Z.  lia. Qed.
Lemma SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__helper2 : to_bit_sz (Z.to_nat (6 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__Type := Z.
Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__cond := (fun z => (1 <= z <= 6)%Z).
Inductive SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Type : Set :=
 | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n1
 | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n2
 | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n4
 | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n8
 | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n16
.
Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__cond := (fun (_ : SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Type) => True).
Lemma SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__nat__helper.

Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1 t :=
  match t with
  | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n1 => 0
  | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n2 => 1
  | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n4 => 2
  | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n8 => 3
  | SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n16 => 4
  end.
Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F2 n :=
  match n with
  | 0 => SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n1
  | 1 => SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n2
  | 2 => SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n4
  | 3 => SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n8
  | 4 => SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n16
  | _ => SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__n1
  end.
Lemma SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1F2 : forall x : SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Type, (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1 x <= 4) /\ SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F2 (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F2F1 : forall (y : nat) (H : y <= 4), SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1 (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F2 y) = y. enum_solve H y. Qed.

Lemma SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__helper1 : (1 <= 6)%Z.  lia. Qed.
Lemma SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__helper2 : to_bit_sz (Z.to_nat (6 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__Type := Z.
Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__cond := (fun z => (1 <= z <= 6)%Z).
Inductive SRS_Resources__maxNumberSRS_Ports_PerResource__Type : Set :=
 | SRS_Resources__maxNumberSRS_Ports_PerResource__n1
 | SRS_Resources__maxNumberSRS_Ports_PerResource__n2
 | SRS_Resources__maxNumberSRS_Ports_PerResource__n4
.
Definition SRS_Resources__maxNumberSRS_Ports_PerResource__cond := (fun (_ : SRS_Resources__maxNumberSRS_Ports_PerResource__Type) => True).
Lemma SRS_Resources__maxNumberSRS_Ports_PerResource__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resources__maxNumberSRS_Ports_PerResource__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resources__maxNumberSRS_Ports_PerResource__nat__helper.

Definition SRS_Resources__maxNumberSRS_Ports_PerResource__F1 t :=
  match t with
  | SRS_Resources__maxNumberSRS_Ports_PerResource__n1 => 0
  | SRS_Resources__maxNumberSRS_Ports_PerResource__n2 => 1
  | SRS_Resources__maxNumberSRS_Ports_PerResource__n4 => 2
  end.
Definition SRS_Resources__maxNumberSRS_Ports_PerResource__F2 n :=
  match n with
  | 0 => SRS_Resources__maxNumberSRS_Ports_PerResource__n1
  | 1 => SRS_Resources__maxNumberSRS_Ports_PerResource__n2
  | 2 => SRS_Resources__maxNumberSRS_Ports_PerResource__n4
  | _ => SRS_Resources__maxNumberSRS_Ports_PerResource__n1
  end.
Lemma SRS_Resources__maxNumberSRS_Ports_PerResource__F1F2 : forall x : SRS_Resources__maxNumberSRS_Ports_PerResource__Type, (SRS_Resources__maxNumberSRS_Ports_PerResource__F1 x <= 2) /\ SRS_Resources__maxNumberSRS_Ports_PerResource__F2 (SRS_Resources__maxNumberSRS_Ports_PerResource__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resources__maxNumberSRS_Ports_PerResource__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resources__maxNumberSRS_Ports_PerResource__F1 (SRS_Resources__maxNumberSRS_Ports_PerResource__F2 y) = y. enum_solve H y. Qed.

Record SRS_Resources__Type : Set :=
  make__SRS_Resources__Type {
    SRS_Resources__maxNumberAperiodicSRS_PerBWP : SRS_Resources__maxNumberAperiodicSRS_PerBWP__Type ;
    SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot : Z ;
    SRS_Resources__maxNumberPeriodicSRS_PerBWP : SRS_Resources__maxNumberPeriodicSRS_PerBWP__Type ;
    SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot : Z ;
    SRS_Resources__maxNumberSemiPersistentSRS_PerBWP : SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Type ;
    SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot : Z ;
    SRS_Resources__maxNumberSRS_Ports_PerResource : SRS_Resources__maxNumberSRS_Ports_PerResource__Type ;
}.
Definition SRS_Resources__list := (
 Nor SRS_Resources__maxNumberAperiodicSRS_PerBWP__Type SRS_Resources__maxNumberAperiodicSRS_PerBWP__cond ::
 Nor Z SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__cond ::
 Nor SRS_Resources__maxNumberPeriodicSRS_PerBWP__Type SRS_Resources__maxNumberPeriodicSRS_PerBWP__cond ::
 Nor Z SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__cond ::
 Nor SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Type SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__cond ::
 Nor Z SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__cond ::
 Nor SRS_Resources__maxNumberSRS_Ports_PerResource__Type SRS_Resources__maxNumberSRS_Ports_PerResource__cond ::
 nil).
Definition SRS_Resources__cond z := 
  SRS_Resources__maxNumberAperiodicSRS_PerBWP__cond (SRS_Resources__maxNumberAperiodicSRS_PerBWP z) /\
  SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__cond (SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot z) /\
  SRS_Resources__maxNumberPeriodicSRS_PerBWP__cond (SRS_Resources__maxNumberPeriodicSRS_PerBWP z) /\
  SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__cond (SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot z) /\
  SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__cond (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP z) /\
  SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__cond (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot z) /\
  SRS_Resources__maxNumberSRS_Ports_PerResource__cond (SRS_Resources__maxNumberSRS_Ports_PerResource z) /\
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
Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP__Format : T_Format SRS_Resources__maxNumberAperiodicSRS_PerBWP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resources__maxNumberAperiodicSRS_PerBWP__nat__Format SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1 SRS_Resources__maxNumberAperiodicSRS_PerBWP__F2 SRS_Resources__maxNumberAperiodicSRS_PerBWP__F1F2 SRS_Resources__maxNumberAperiodicSRS_PerBWP__F2F1.

Opaque SRS_Resources__maxNumberAperiodicSRS_PerBWP__cond SRS_Resources__maxNumberAperiodicSRS_PerBWP__Format.

Definition SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__Format : T_Format Z SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__cond :=
 ranged_int_format (1) (6) SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__helper1 SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__helper2.

Opaque SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__cond SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__Format.

Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP__Format : T_Format SRS_Resources__maxNumberPeriodicSRS_PerBWP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resources__maxNumberPeriodicSRS_PerBWP__nat__Format SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1 SRS_Resources__maxNumberPeriodicSRS_PerBWP__F2 SRS_Resources__maxNumberPeriodicSRS_PerBWP__F1F2 SRS_Resources__maxNumberPeriodicSRS_PerBWP__F2F1.

Opaque SRS_Resources__maxNumberPeriodicSRS_PerBWP__cond SRS_Resources__maxNumberPeriodicSRS_PerBWP__Format.

Definition SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__Format : T_Format Z SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__cond :=
 ranged_int_format (1) (6) SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__helper1 SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__helper2.

Opaque SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__cond SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__Format.

Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Format : T_Format SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__nat__Format SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1 SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F2 SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F1F2 SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__F2F1.

Opaque SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__cond SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Format.

Definition SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__Format : T_Format Z SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__cond :=
 ranged_int_format (1) (6) SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__helper1 SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__helper2.

Opaque SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__cond SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__Format.

Definition SRS_Resources__maxNumberSRS_Ports_PerResource__Format : T_Format SRS_Resources__maxNumberSRS_Ports_PerResource__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resources__maxNumberSRS_Ports_PerResource__nat__Format SRS_Resources__maxNumberSRS_Ports_PerResource__F1 SRS_Resources__maxNumberSRS_Ports_PerResource__F2 SRS_Resources__maxNumberSRS_Ports_PerResource__F1F2 SRS_Resources__maxNumberSRS_Ports_PerResource__F2F1.

Opaque SRS_Resources__maxNumberSRS_Ports_PerResource__cond SRS_Resources__maxNumberSRS_Ports_PerResource__Format.


Definition SRS_Resources__Format_Type := Eval cbn in seq_format_prod SRS_Resources__list.
Definition SRS_Resources__Format_list : SRS_Resources__Format_Type :=
  (SRS_Resources__maxNumberAperiodicSRS_PerBWP__Format, (SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot__Format, (SRS_Resources__maxNumberPeriodicSRS_PerBWP__Format, (SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot__Format, (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP__Format, (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot__Format, (SRS_Resources__maxNumberSRS_Ports_PerResource__Format, unit_format))))))).
Definition SRS_Resources__list__Format := (*Eval compute in *) seq_format SRS_Resources__list SRS_Resources__Format_list.
Definition SRS_Resources__F1 z :=
  (SRS_Resources__maxNumberAperiodicSRS_PerBWP z, (SRS_Resources__maxNumberAperiodicSRS_PerBWP_PerSlot z, (SRS_Resources__maxNumberPeriodicSRS_PerBWP z, (SRS_Resources__maxNumberPeriodicSRS_PerBWP_PerSlot z, (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP z, (SRS_Resources__maxNumberSemiPersistentSRS_PerBWP_PerSlot z, (SRS_Resources__maxNumberSRS_Ports_PerResource z, tt))))))).
Definition SRS_Resources__F2 (y : seq_type SRS_Resources__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__SRS_Resources__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma SRS_Resources__F1F2_cond (z : SRS_Resources__Type)
  : SRS_Resources__cond z ->
  (seq_cond SRS_Resources__list (SRS_Resources__F1 z)).
intro H. unfold SRS_Resources__cond in H. simpl. auto. Qed.
Lemma SRS_Resources__F1F2_cond2 (z : SRS_Resources__Type)
 : SRS_Resources__F2 (SRS_Resources__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resources__F2F1_cond (y : seq_type SRS_Resources__list)
  : seq_cond SRS_Resources__list y ->
 (SRS_Resources__cond (SRS_Resources__F2 y)) /\  SRS_Resources__F1 (SRS_Resources__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resources__cond. simpl in *. auto.
 - simpl. unfold SRS_Resources__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resources__Format : T_Format SRS_Resources__Type SRS_Resources__cond :=
        proj2_format  SRS_Resources__cond SRS_Resources__list__Format
    SRS_Resources__F1 SRS_Resources__F2 SRS_Resources__F1F2_cond  SRS_Resources__F1F2_cond2 SRS_Resources__F2F1_cond.
Opaque SRS_Resources__cond SRS_Resources__Format.

