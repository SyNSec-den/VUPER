Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Type : Set :=
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf0
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf10
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf20
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf50
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf100
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf200
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf500
 | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf1000
.
Definition MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__cond := (fun (_ : MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Type) => True).
Lemma MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__nat__helper.

Definition MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1 t :=
  match t with
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf0 => 0
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf10 => 1
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf20 => 2
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf50 => 3
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf100 => 4
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf200 => 5
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf500 => 6
  | MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf1000 => 7
  end.
Definition MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F2 n :=
  match n with
  | 0 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf0
  | 1 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf10
  | 2 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf20
  | 3 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf50
  | 4 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf100
  | 5 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf200
  | 6 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf500
  | 7 => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf1000
  | _ => MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__sf0
  end.
Lemma MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1F2 : forall x : MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Type, (MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1 x <= 7) /\ MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F2 (MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F2F1 : forall (y : nat) (H : y <= 7), MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1 (MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MPE_Config_FR2_r17__mpe_Threshold_r17__Type : Set :=
 | MPE_Config_FR2_r17__mpe_Threshold_r17__dB3
 | MPE_Config_FR2_r17__mpe_Threshold_r17__dB6
 | MPE_Config_FR2_r17__mpe_Threshold_r17__dB9
 | MPE_Config_FR2_r17__mpe_Threshold_r17__dB12
.
Definition MPE_Config_FR2_r17__mpe_Threshold_r17__cond := (fun (_ : MPE_Config_FR2_r17__mpe_Threshold_r17__Type) => True).
Lemma MPE_Config_FR2_r17__mpe_Threshold_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MPE_Config_FR2_r17__mpe_Threshold_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MPE_Config_FR2_r17__mpe_Threshold_r17__nat__helper.

Definition MPE_Config_FR2_r17__mpe_Threshold_r17__F1 t :=
  match t with
  | MPE_Config_FR2_r17__mpe_Threshold_r17__dB3 => 0
  | MPE_Config_FR2_r17__mpe_Threshold_r17__dB6 => 1
  | MPE_Config_FR2_r17__mpe_Threshold_r17__dB9 => 2
  | MPE_Config_FR2_r17__mpe_Threshold_r17__dB12 => 3
  end.
Definition MPE_Config_FR2_r17__mpe_Threshold_r17__F2 n :=
  match n with
  | 0 => MPE_Config_FR2_r17__mpe_Threshold_r17__dB3
  | 1 => MPE_Config_FR2_r17__mpe_Threshold_r17__dB6
  | 2 => MPE_Config_FR2_r17__mpe_Threshold_r17__dB9
  | 3 => MPE_Config_FR2_r17__mpe_Threshold_r17__dB12
  | _ => MPE_Config_FR2_r17__mpe_Threshold_r17__dB3
  end.
Lemma MPE_Config_FR2_r17__mpe_Threshold_r17__F1F2 : forall x : MPE_Config_FR2_r17__mpe_Threshold_r17__Type, (MPE_Config_FR2_r17__mpe_Threshold_r17__F1 x <= 3) /\ MPE_Config_FR2_r17__mpe_Threshold_r17__F2 (MPE_Config_FR2_r17__mpe_Threshold_r17__F1 x) = x. imp_solve. Qed.
Lemma MPE_Config_FR2_r17__mpe_Threshold_r17__F2F1 : forall (y : nat) (H : y <= 3), MPE_Config_FR2_r17__mpe_Threshold_r17__F1 (MPE_Config_FR2_r17__mpe_Threshold_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MPE_Config_FR2_r17__numberOfN_r17__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma MPE_Config_FR2_r17__numberOfN_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MPE_Config_FR2_r17__numberOfN_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MPE_Config_FR2_r17__numberOfN_r17__Type := Z.
Definition MPE_Config_FR2_r17__numberOfN_r17__cond := (fun z => (1 <= z <= 4)%Z).
Record MPE_Config_FR2_r17__Type : Set :=
  make__MPE_Config_FR2_r17__Type {
    MPE_Config_FR2_r17__mpe_ProhibitTimer_r17 : MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Type ;
    MPE_Config_FR2_r17__mpe_Threshold_r17 : MPE_Config_FR2_r17__mpe_Threshold_r17__Type ;
    MPE_Config_FR2_r17__numberOfN_r17 : Z ;
}.
Definition MPE_Config_FR2_r17__root_list : list seq_elem := (
 Nor MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Type MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__cond ::
 Nor MPE_Config_FR2_r17__mpe_Threshold_r17__Type MPE_Config_FR2_r17__mpe_Threshold_r17__cond ::
 Nor Z MPE_Config_FR2_r17__numberOfN_r17__cond ::
 nil).
Definition MPE_Config_FR2_r17__ext_list : list typ := (
  nil).
Definition MPE_Config_FR2_r17__cond (z : MPE_Config_FR2_r17__Type) := 
(  MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__cond (MPE_Config_FR2_r17__mpe_ProhibitTimer_r17 z) /\
  MPE_Config_FR2_r17__mpe_Threshold_r17__cond (MPE_Config_FR2_r17__mpe_Threshold_r17 z) /\
  MPE_Config_FR2_r17__numberOfN_r17__cond (MPE_Config_FR2_r17__numberOfN_r17 z) /\
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
Definition MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Format : T_Format MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__nat__Format MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1 MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F2 MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F1F2 MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__F2F1.

Opaque MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__cond MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Format.

Definition MPE_Config_FR2_r17__mpe_Threshold_r17__Format : T_Format MPE_Config_FR2_r17__mpe_Threshold_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MPE_Config_FR2_r17__mpe_Threshold_r17__nat__Format MPE_Config_FR2_r17__mpe_Threshold_r17__F1 MPE_Config_FR2_r17__mpe_Threshold_r17__F2 MPE_Config_FR2_r17__mpe_Threshold_r17__F1F2 MPE_Config_FR2_r17__mpe_Threshold_r17__F2F1.

Opaque MPE_Config_FR2_r17__mpe_Threshold_r17__cond MPE_Config_FR2_r17__mpe_Threshold_r17__Format.

Definition MPE_Config_FR2_r17__numberOfN_r17__Format : T_Format Z MPE_Config_FR2_r17__numberOfN_r17__cond :=
 ranged_int_format (1) (4) MPE_Config_FR2_r17__numberOfN_r17__helper1 MPE_Config_FR2_r17__numberOfN_r17__helper2.

Opaque MPE_Config_FR2_r17__numberOfN_r17__cond MPE_Config_FR2_r17__numberOfN_r17__Format.


Definition MPE_Config_FR2_r17__root_Format_Type := Eval cbn in seq_format_prod MPE_Config_FR2_r17__root_list.
Definition MPE_Config_FR2_r17__root_Format_list : MPE_Config_FR2_r17__root_Format_Type :=
  (MPE_Config_FR2_r17__mpe_ProhibitTimer_r17__Format, (MPE_Config_FR2_r17__mpe_Threshold_r17__Format, (MPE_Config_FR2_r17__numberOfN_r17__Format, unit_format))).

Definition MPE_Config_FR2_r17__ext_Format_Type := Eval cbn in get_formats MPE_Config_FR2_r17__ext_list.
Definition MPE_Config_FR2_r17__ext_Format_list : MPE_Config_FR2_r17__ext_Format_Type :=
  unit__Format.

Definition MPE_Config_FR2_r17__list_type : Set := (seq_type MPE_Config_FR2_r17__root_list) * (seq_ext_type MPE_Config_FR2_r17__ext_list).
Definition MPE_Config_FR2_r17__list_cond (z : MPE_Config_FR2_r17__list_type) : Prop :=
        (seq_cond MPE_Config_FR2_r17__root_list (fst z)) /\ (seq_ext_cond MPE_Config_FR2_r17__ext_list (snd z)).
Definition MPE_Config_FR2_r17__list_format : T_Format MPE_Config_FR2_r17__list_type MPE_Config_FR2_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MPE_Config_FR2_r17__root_list MPE_Config_FR2_r17__root_Format_list MPE_Config_FR2_r17__ext_list MPE_Config_FR2_r17__ext_Format_list.

Opaque MPE_Config_FR2_r17__list_format.
Definition MPE_Config_FR2_r17__F1 (z : MPE_Config_FR2_r17__Type) : MPE_Config_FR2_r17__list_type :=
  (((MPE_Config_FR2_r17__mpe_ProhibitTimer_r17 z, (MPE_Config_FR2_r17__mpe_Threshold_r17 z, (MPE_Config_FR2_r17__numberOfN_r17 z, tt)))), (
tt)).
Definition MPE_Config_FR2_r17__F2 (y : MPE_Config_FR2_r17__list_type) : MPE_Config_FR2_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__MPE_Config_FR2_r17__Type j0 j1 j2
  end.
Definition MPE_Config_FR2_r17__helper1 : (forall a : MPE_Config_FR2_r17__Type, MPE_Config_FR2_r17__cond a -> MPE_Config_FR2_r17__list_cond (MPE_Config_FR2_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MPE_Config_FR2_r17__helper2 : (forall a : MPE_Config_FR2_r17__Type, MPE_Config_FR2_r17__F2 (MPE_Config_FR2_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MPE_Config_FR2_r17__helper3 : (forall b : MPE_Config_FR2_r17__list_type, MPE_Config_FR2_r17__list_cond b -> MPE_Config_FR2_r17__cond (MPE_Config_FR2_r17__F2 b) /\ MPE_Config_FR2_r17__F1 (MPE_Config_FR2_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MPE_Config_FR2_r17__cond, MPE_Config_FR2_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MPE_Config_FR2_r17__Format : T_Format MPE_Config_FR2_r17__Type MPE_Config_FR2_r17__cond :=
 proj2_format MPE_Config_FR2_r17__cond MPE_Config_FR2_r17__list_format  MPE_Config_FR2_r17__F1 MPE_Config_FR2_r17__F2 MPE_Config_FR2_r17__helper1 MPE_Config_FR2_r17__helper2 MPE_Config_FR2_r17__helper3.

Opaque MPE_Config_FR2_r17__cond MPE_Config_FR2_r17__Format.

