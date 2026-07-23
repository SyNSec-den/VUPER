Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SchedulingRequestResourceId.

Opaque SchedulingRequestResourceId__cond SchedulingRequestResourceId__Format.

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl2__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl2__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl2__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl2__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl4__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl4__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl4__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl4__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl5__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl5__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl5__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl5__cond := (fun z => (0 <= z <= 4)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl8__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl8__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl8__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl8__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl8__cond := (fun z => (0 <= z <= 7)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl10__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl16__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl20__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl40__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl80__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl160__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl320__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__sl640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingRequestResourceConfig__periodicityAndOffset__sl640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl640__Type := Z.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl640__cond := (fun z => (0 <= z <= 639)%Z).

Inductive SchedulingRequestResourceConfig__periodicityAndOffset__Type : Set :=
  | SchedulingRequestResourceConfig__periodicityAndOffset__sym2 : unit -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sym6or7 : unit -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl1 : unit -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl2 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl4 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl5 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl8 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl10 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl16 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl20 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl40 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl80 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl160 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl320 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl640 : Z -> SchedulingRequestResourceConfig__periodicityAndOffset__Type
.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl2__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl4__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl5__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl8__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl10__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl16__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl20__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl40__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl80__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl160__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl320__cond ::
typ_cons Z SchedulingRequestResourceConfig__periodicityAndOffset__sl640__cond ::
 nil).
Definition SchedulingRequestResourceConfig__periodicityAndOffset__cond (c : SchedulingRequestResourceConfig__periodicityAndOffset__Type) := 
  match c with
  | SchedulingRequestResourceConfig__periodicityAndOffset__sym2 t => (fun _ => True) t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sym6or7 t => (fun _ => True) t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl1 t => (fun _ => True) t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl2 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl2__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl4 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl4__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl5 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl5__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl8 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl8__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl10 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl10__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl16 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl16__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl20 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl20__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl40 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl40__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl80 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl80__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl160 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl160__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl320 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl320__cond t 
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl640 t => SchedulingRequestResourceConfig__periodicityAndOffset__sl640__cond t 
  end.

Lemma SchedulingRequestResourceConfig__periodicityAndOffset__len_helper1 : to_bit_sz (length SchedulingRequestResourceConfig__periodicityAndOffset__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__len_helper2 : 2 <= length2 SchedulingRequestResourceConfig__periodicityAndOffset__list.
 simpl. lia. Qed.
Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Record SchedulingRequestResourceConfig__Type : Set :=
  make__SchedulingRequestResourceConfig__Type {
    SchedulingRequestResourceConfig__schedulingRequestResourceId : SchedulingRequestResourceId__Type ;
    SchedulingRequestResourceConfig__schedulingRequestID : SchedulingRequestId__Type ;
    SchedulingRequestResourceConfig__periodicityAndOffset : option SchedulingRequestResourceConfig__periodicityAndOffset__Type ;
    SchedulingRequestResourceConfig__resource : option PUCCH_ResourceId__Type ;
}.
Definition SchedulingRequestResourceConfig__list := (
 Nor SchedulingRequestResourceId__Type SchedulingRequestResourceId__cond ::
 Nor SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt SchedulingRequestResourceConfig__periodicityAndOffset__Type SchedulingRequestResourceConfig__periodicityAndOffset__cond ::
 Opt PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 nil).
Definition SchedulingRequestResourceConfig__cond z := 
  SchedulingRequestResourceId__cond (SchedulingRequestResourceConfig__schedulingRequestResourceId z) /\
  SchedulingRequestId__cond (SchedulingRequestResourceConfig__schedulingRequestID z) /\
  opt_cond SchedulingRequestResourceConfig__periodicityAndOffset__cond (SchedulingRequestResourceConfig__periodicityAndOffset z) /\
  opt_cond PUCCH_ResourceId__cond (SchedulingRequestResourceConfig__resource z) /\
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
Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl2__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl2__cond :=
 ranged_int_format (0) (1) SchedulingRequestResourceConfig__periodicityAndOffset__sl2__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl2__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl2__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl2__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl4__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl4__cond :=
 ranged_int_format (0) (3) SchedulingRequestResourceConfig__periodicityAndOffset__sl4__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl4__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl4__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl4__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl5__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl5__cond :=
 ranged_int_format (0) (4) SchedulingRequestResourceConfig__periodicityAndOffset__sl5__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl5__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl5__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl5__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl8__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl8__cond :=
 ranged_int_format (0) (7) SchedulingRequestResourceConfig__periodicityAndOffset__sl8__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl8__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl8__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl8__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl10__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl10__cond :=
 ranged_int_format (0) (9) SchedulingRequestResourceConfig__periodicityAndOffset__sl10__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl10__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl10__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl10__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl16__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl16__cond :=
 ranged_int_format (0) (15) SchedulingRequestResourceConfig__periodicityAndOffset__sl16__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl16__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl16__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl16__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl20__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl20__cond :=
 ranged_int_format (0) (19) SchedulingRequestResourceConfig__periodicityAndOffset__sl20__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl20__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl20__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl20__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl40__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl40__cond :=
 ranged_int_format (0) (39) SchedulingRequestResourceConfig__periodicityAndOffset__sl40__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl40__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl40__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl40__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl80__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl80__cond :=
 ranged_int_format (0) (79) SchedulingRequestResourceConfig__periodicityAndOffset__sl80__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl80__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl80__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl80__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl160__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl160__cond :=
 ranged_int_format (0) (159) SchedulingRequestResourceConfig__periodicityAndOffset__sl160__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl160__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl160__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl160__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl320__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl320__cond :=
 ranged_int_format (0) (319) SchedulingRequestResourceConfig__periodicityAndOffset__sl320__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl320__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl320__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl320__Format.

Definition SchedulingRequestResourceConfig__periodicityAndOffset__sl640__Format : T_Format Z SchedulingRequestResourceConfig__periodicityAndOffset__sl640__cond :=
 ranged_int_format (0) (639) SchedulingRequestResourceConfig__periodicityAndOffset__sl640__helper1 SchedulingRequestResourceConfig__periodicityAndOffset__sl640__helper2.

Opaque SchedulingRequestResourceConfig__periodicityAndOffset__sl640__cond SchedulingRequestResourceConfig__periodicityAndOffset__sl640__Format.


Definition SchedulingRequestResourceConfig__periodicityAndOffset__Format_Type := Eval cbn in get_formats SchedulingRequestResourceConfig__periodicityAndOffset__list.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__Format_list : SchedulingRequestResourceConfig__periodicityAndOffset__Format_Type :=
  (unit__Format, (unit__Format, (unit__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl2__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl4__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl5__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl8__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl10__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl16__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl20__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl40__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl80__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl160__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl320__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__sl640__Format, unit__Format))))))))))))))).
Definition SchedulingRequestResourceConfig__periodicityAndOffset__list__Format := Eval compute in choice_format SchedulingRequestResourceConfig__periodicityAndOffset__list SchedulingRequestResourceConfig__periodicityAndOffset__len_helper1 SchedulingRequestResourceConfig__periodicityAndOffset__len_helper2  SchedulingRequestResourceConfig__periodicityAndOffset__Format_list.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__F1 (z : SchedulingRequestResourceConfig__periodicityAndOffset__Type) : (choice SchedulingRequestResourceConfig__periodicityAndOffset__list) :=
  match z with
   | SchedulingRequestResourceConfig__periodicityAndOffset__sym2 t => existT _ 0 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sym6or7 t => existT _ 1 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl1 t => existT _ 2 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl2 t => existT _ 3 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl4 t => existT _ 4 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl5 t => existT _ 5 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl8 t => existT _ 6 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl10 t => existT _ 7 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl16 t => existT _ 8 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl20 t => existT _ 9 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl40 t => existT _ 10 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl80 t => existT _ 11 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl160 t => existT _ 12 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl320 t => existT _ 13 t
  | SchedulingRequestResourceConfig__periodicityAndOffset__sl640 t => existT _ 14 t
  end.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__g := (fun n => typ_set (get_nth_typ SchedulingRequestResourceConfig__periodicityAndOffset__list n)).
Definition SchedulingRequestResourceConfig__periodicityAndOffset__F2 (y : choice SchedulingRequestResourceConfig__periodicityAndOffset__list) : SchedulingRequestResourceConfig__periodicityAndOffset__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SchedulingRequestResourceConfig__periodicityAndOffset__g n -> SchedulingRequestResourceConfig__periodicityAndOffset__Type) with
    | 0 => fun (t : unit) => SchedulingRequestResourceConfig__periodicityAndOffset__sym2 t 
    | 1 => fun (t : unit) => SchedulingRequestResourceConfig__periodicityAndOffset__sym6or7 t 
    | 2 => fun (t : unit) => SchedulingRequestResourceConfig__periodicityAndOffset__sl1 t 
    | 3 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl2 t 
    | 4 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl4 t 
    | 5 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl5 t 
    | 6 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl8 t 
    | 7 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl10 t 
    | 8 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl16 t 
    | 9 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl20 t 
    | 10 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl40 t 
    | 11 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl80 t 
    | 12 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl160 t 
    | 13 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl320 t 
    | 14 => fun (t : Z) => SchedulingRequestResourceConfig__periodicityAndOffset__sl640 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))) => (fun (x' : nat) (t'' : SchedulingRequestResourceConfig__periodicityAndOffset__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ SchedulingRequestResourceConfig__periodicityAndOffset__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SchedulingRequestResourceConfig__periodicityAndOffset__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))) in match t' return SchedulingRequestResourceConfig__periodicityAndOffset__Type with end) n0
           end t0).

Lemma SchedulingRequestResourceConfig__periodicityAndOffset__helper2 :  forall (y : SchedulingRequestResourceConfig__periodicityAndOffset__Type), SchedulingRequestResourceConfig__periodicityAndOffset__cond y -> choice_cond SchedulingRequestResourceConfig__periodicityAndOffset__list (SchedulingRequestResourceConfig__periodicityAndOffset__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SchedulingRequestResourceConfig__periodicityAndOffset__helper3 :  forall (y : SchedulingRequestResourceConfig__periodicityAndOffset__Type), SchedulingRequestResourceConfig__periodicityAndOffset__F2 (SchedulingRequestResourceConfig__periodicityAndOffset__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SchedulingRequestResourceConfig__periodicityAndOffset__helper4 : (forall b : choice SchedulingRequestResourceConfig__periodicityAndOffset__list, choice_cond SchedulingRequestResourceConfig__periodicityAndOffset__list b -> SchedulingRequestResourceConfig__periodicityAndOffset__cond (SchedulingRequestResourceConfig__periodicityAndOffset__F2 b) /\ SchedulingRequestResourceConfig__periodicityAndOffset__F1 (SchedulingRequestResourceConfig__periodicityAndOffset__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SchedulingRequestResourceConfig__periodicityAndOffset__F1 SchedulingRequestResourceConfig__periodicityAndOffset__F2.
Definition SchedulingRequestResourceConfig__periodicityAndOffset__Format : T_Format SchedulingRequestResourceConfig__periodicityAndOffset__Type SchedulingRequestResourceConfig__periodicityAndOffset__cond :=
  (* Eval compute in *) proj2_format SchedulingRequestResourceConfig__periodicityAndOffset__cond SchedulingRequestResourceConfig__periodicityAndOffset__list__Format SchedulingRequestResourceConfig__periodicityAndOffset__F1 SchedulingRequestResourceConfig__periodicityAndOffset__F2 SchedulingRequestResourceConfig__periodicityAndOffset__helper2 SchedulingRequestResourceConfig__periodicityAndOffset__helper3 SchedulingRequestResourceConfig__periodicityAndOffset__helper4.
Opaque SchedulingRequestResourceConfig__periodicityAndOffset__cond SchedulingRequestResourceConfig__periodicityAndOffset__Format.


Definition SchedulingRequestResourceConfig__Format_Type := Eval cbn in seq_format_prod SchedulingRequestResourceConfig__list.
Definition SchedulingRequestResourceConfig__Format_list : SchedulingRequestResourceConfig__Format_Type :=
  (SchedulingRequestResourceId__Format, (SchedulingRequestId__Format, (SchedulingRequestResourceConfig__periodicityAndOffset__Format, (PUCCH_ResourceId__Format, unit_format)))).
Definition SchedulingRequestResourceConfig__list__Format := (*Eval compute in *) seq_format SchedulingRequestResourceConfig__list SchedulingRequestResourceConfig__Format_list.
Definition SchedulingRequestResourceConfig__F1 z :=
  (SchedulingRequestResourceConfig__schedulingRequestResourceId z, (SchedulingRequestResourceConfig__schedulingRequestID z, (SchedulingRequestResourceConfig__periodicityAndOffset z, (SchedulingRequestResourceConfig__resource z, tt)))).
Definition SchedulingRequestResourceConfig__F2 (y : seq_type SchedulingRequestResourceConfig__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SchedulingRequestResourceConfig__Type i0 i1 i2 i3
  end.
Lemma SchedulingRequestResourceConfig__F1F2_cond (z : SchedulingRequestResourceConfig__Type)
  : SchedulingRequestResourceConfig__cond z ->
  (seq_cond SchedulingRequestResourceConfig__list (SchedulingRequestResourceConfig__F1 z)).
intro H. unfold SchedulingRequestResourceConfig__cond in H. simpl. auto. Qed.
Lemma SchedulingRequestResourceConfig__F1F2_cond2 (z : SchedulingRequestResourceConfig__Type)
 : SchedulingRequestResourceConfig__F2 (SchedulingRequestResourceConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingRequestResourceConfig__F2F1_cond (y : seq_type SchedulingRequestResourceConfig__list)
  : seq_cond SchedulingRequestResourceConfig__list y ->
 (SchedulingRequestResourceConfig__cond (SchedulingRequestResourceConfig__F2 y)) /\  SchedulingRequestResourceConfig__F1 (SchedulingRequestResourceConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingRequestResourceConfig__cond. simpl in *. auto.
 - simpl. unfold SchedulingRequestResourceConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingRequestResourceConfig__Format : T_Format SchedulingRequestResourceConfig__Type SchedulingRequestResourceConfig__cond :=
        proj2_format  SchedulingRequestResourceConfig__cond SchedulingRequestResourceConfig__list__Format
    SchedulingRequestResourceConfig__F1 SchedulingRequestResourceConfig__F2 SchedulingRequestResourceConfig__F1F2_cond  SchedulingRequestResourceConfig__F1F2_cond2 SchedulingRequestResourceConfig__F2F1_cond.
Opaque SchedulingRequestResourceConfig__cond SchedulingRequestResourceConfig__Format.

