Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BSR_Config__periodicBSR_Timer__Type : Set :=
 | BSR_Config__periodicBSR_Timer__sf1
 | BSR_Config__periodicBSR_Timer__sf5
 | BSR_Config__periodicBSR_Timer__sf10
 | BSR_Config__periodicBSR_Timer__sf16
 | BSR_Config__periodicBSR_Timer__sf20
 | BSR_Config__periodicBSR_Timer__sf32
 | BSR_Config__periodicBSR_Timer__sf40
 | BSR_Config__periodicBSR_Timer__sf64
 | BSR_Config__periodicBSR_Timer__sf80
 | BSR_Config__periodicBSR_Timer__sf128
 | BSR_Config__periodicBSR_Timer__sf160
 | BSR_Config__periodicBSR_Timer__sf320
 | BSR_Config__periodicBSR_Timer__sf640
 | BSR_Config__periodicBSR_Timer__sf1280
 | BSR_Config__periodicBSR_Timer__sf2560
 | BSR_Config__periodicBSR_Timer__infinity
.
Definition BSR_Config__periodicBSR_Timer__cond := (fun (_ : BSR_Config__periodicBSR_Timer__Type) => True).
Lemma BSR_Config__periodicBSR_Timer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BSR_Config__periodicBSR_Timer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 BSR_Config__periodicBSR_Timer__nat__helper.

Definition BSR_Config__periodicBSR_Timer__F1 t :=
  match t with
  | BSR_Config__periodicBSR_Timer__sf1 => 0
  | BSR_Config__periodicBSR_Timer__sf5 => 1
  | BSR_Config__periodicBSR_Timer__sf10 => 2
  | BSR_Config__periodicBSR_Timer__sf16 => 3
  | BSR_Config__periodicBSR_Timer__sf20 => 4
  | BSR_Config__periodicBSR_Timer__sf32 => 5
  | BSR_Config__periodicBSR_Timer__sf40 => 6
  | BSR_Config__periodicBSR_Timer__sf64 => 7
  | BSR_Config__periodicBSR_Timer__sf80 => 8
  | BSR_Config__periodicBSR_Timer__sf128 => 9
  | BSR_Config__periodicBSR_Timer__sf160 => 10
  | BSR_Config__periodicBSR_Timer__sf320 => 11
  | BSR_Config__periodicBSR_Timer__sf640 => 12
  | BSR_Config__periodicBSR_Timer__sf1280 => 13
  | BSR_Config__periodicBSR_Timer__sf2560 => 14
  | BSR_Config__periodicBSR_Timer__infinity => 15
  end.
Definition BSR_Config__periodicBSR_Timer__F2 n :=
  match n with
  | 0 => BSR_Config__periodicBSR_Timer__sf1
  | 1 => BSR_Config__periodicBSR_Timer__sf5
  | 2 => BSR_Config__periodicBSR_Timer__sf10
  | 3 => BSR_Config__periodicBSR_Timer__sf16
  | 4 => BSR_Config__periodicBSR_Timer__sf20
  | 5 => BSR_Config__periodicBSR_Timer__sf32
  | 6 => BSR_Config__periodicBSR_Timer__sf40
  | 7 => BSR_Config__periodicBSR_Timer__sf64
  | 8 => BSR_Config__periodicBSR_Timer__sf80
  | 9 => BSR_Config__periodicBSR_Timer__sf128
  | 10 => BSR_Config__periodicBSR_Timer__sf160
  | 11 => BSR_Config__periodicBSR_Timer__sf320
  | 12 => BSR_Config__periodicBSR_Timer__sf640
  | 13 => BSR_Config__periodicBSR_Timer__sf1280
  | 14 => BSR_Config__periodicBSR_Timer__sf2560
  | 15 => BSR_Config__periodicBSR_Timer__infinity
  | _ => BSR_Config__periodicBSR_Timer__sf1
  end.
Lemma BSR_Config__periodicBSR_Timer__F1F2 : forall x : BSR_Config__periodicBSR_Timer__Type, (BSR_Config__periodicBSR_Timer__F1 x <= 15) /\ BSR_Config__periodicBSR_Timer__F2 (BSR_Config__periodicBSR_Timer__F1 x) = x. imp_solve. Qed.
Lemma BSR_Config__periodicBSR_Timer__F2F1 : forall (y : nat) (H : y <= 15), BSR_Config__periodicBSR_Timer__F1 (BSR_Config__periodicBSR_Timer__F2 y) = y. enum_solve H y. Qed.

Inductive BSR_Config__retxBSR_Timer__Type : Set :=
 | BSR_Config__retxBSR_Timer__sf10
 | BSR_Config__retxBSR_Timer__sf20
 | BSR_Config__retxBSR_Timer__sf40
 | BSR_Config__retxBSR_Timer__sf80
 | BSR_Config__retxBSR_Timer__sf160
 | BSR_Config__retxBSR_Timer__sf320
 | BSR_Config__retxBSR_Timer__sf640
 | BSR_Config__retxBSR_Timer__sf1280
 | BSR_Config__retxBSR_Timer__sf2560
 | BSR_Config__retxBSR_Timer__sf5120
 | BSR_Config__retxBSR_Timer__sf10240
 | BSR_Config__retxBSR_Timer__spare5
 | BSR_Config__retxBSR_Timer__spare4
 | BSR_Config__retxBSR_Timer__spare3
 | BSR_Config__retxBSR_Timer__spare2
 | BSR_Config__retxBSR_Timer__spare1
.
Definition BSR_Config__retxBSR_Timer__cond := (fun (_ : BSR_Config__retxBSR_Timer__Type) => True).
Lemma BSR_Config__retxBSR_Timer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BSR_Config__retxBSR_Timer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 BSR_Config__retxBSR_Timer__nat__helper.

Definition BSR_Config__retxBSR_Timer__F1 t :=
  match t with
  | BSR_Config__retxBSR_Timer__sf10 => 0
  | BSR_Config__retxBSR_Timer__sf20 => 1
  | BSR_Config__retxBSR_Timer__sf40 => 2
  | BSR_Config__retxBSR_Timer__sf80 => 3
  | BSR_Config__retxBSR_Timer__sf160 => 4
  | BSR_Config__retxBSR_Timer__sf320 => 5
  | BSR_Config__retxBSR_Timer__sf640 => 6
  | BSR_Config__retxBSR_Timer__sf1280 => 7
  | BSR_Config__retxBSR_Timer__sf2560 => 8
  | BSR_Config__retxBSR_Timer__sf5120 => 9
  | BSR_Config__retxBSR_Timer__sf10240 => 10
  | BSR_Config__retxBSR_Timer__spare5 => 11
  | BSR_Config__retxBSR_Timer__spare4 => 12
  | BSR_Config__retxBSR_Timer__spare3 => 13
  | BSR_Config__retxBSR_Timer__spare2 => 14
  | BSR_Config__retxBSR_Timer__spare1 => 15
  end.
Definition BSR_Config__retxBSR_Timer__F2 n :=
  match n with
  | 0 => BSR_Config__retxBSR_Timer__sf10
  | 1 => BSR_Config__retxBSR_Timer__sf20
  | 2 => BSR_Config__retxBSR_Timer__sf40
  | 3 => BSR_Config__retxBSR_Timer__sf80
  | 4 => BSR_Config__retxBSR_Timer__sf160
  | 5 => BSR_Config__retxBSR_Timer__sf320
  | 6 => BSR_Config__retxBSR_Timer__sf640
  | 7 => BSR_Config__retxBSR_Timer__sf1280
  | 8 => BSR_Config__retxBSR_Timer__sf2560
  | 9 => BSR_Config__retxBSR_Timer__sf5120
  | 10 => BSR_Config__retxBSR_Timer__sf10240
  | 11 => BSR_Config__retxBSR_Timer__spare5
  | 12 => BSR_Config__retxBSR_Timer__spare4
  | 13 => BSR_Config__retxBSR_Timer__spare3
  | 14 => BSR_Config__retxBSR_Timer__spare2
  | 15 => BSR_Config__retxBSR_Timer__spare1
  | _ => BSR_Config__retxBSR_Timer__sf10
  end.
Lemma BSR_Config__retxBSR_Timer__F1F2 : forall x : BSR_Config__retxBSR_Timer__Type, (BSR_Config__retxBSR_Timer__F1 x <= 15) /\ BSR_Config__retxBSR_Timer__F2 (BSR_Config__retxBSR_Timer__F1 x) = x. imp_solve. Qed.
Lemma BSR_Config__retxBSR_Timer__F2F1 : forall (y : nat) (H : y <= 15), BSR_Config__retxBSR_Timer__F1 (BSR_Config__retxBSR_Timer__F2 y) = y. enum_solve H y. Qed.

Inductive BSR_Config__logicalChannelSR_DelayTimer__Type : Set :=
 | BSR_Config__logicalChannelSR_DelayTimer__sf20
 | BSR_Config__logicalChannelSR_DelayTimer__sf40
 | BSR_Config__logicalChannelSR_DelayTimer__sf64
 | BSR_Config__logicalChannelSR_DelayTimer__sf128
 | BSR_Config__logicalChannelSR_DelayTimer__sf512
 | BSR_Config__logicalChannelSR_DelayTimer__sf1024
 | BSR_Config__logicalChannelSR_DelayTimer__sf2560
 | BSR_Config__logicalChannelSR_DelayTimer__spare1
.
Definition BSR_Config__logicalChannelSR_DelayTimer__cond := (fun (_ : BSR_Config__logicalChannelSR_DelayTimer__Type) => True).
Lemma BSR_Config__logicalChannelSR_DelayTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BSR_Config__logicalChannelSR_DelayTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BSR_Config__logicalChannelSR_DelayTimer__nat__helper.

Definition BSR_Config__logicalChannelSR_DelayTimer__F1 t :=
  match t with
  | BSR_Config__logicalChannelSR_DelayTimer__sf20 => 0
  | BSR_Config__logicalChannelSR_DelayTimer__sf40 => 1
  | BSR_Config__logicalChannelSR_DelayTimer__sf64 => 2
  | BSR_Config__logicalChannelSR_DelayTimer__sf128 => 3
  | BSR_Config__logicalChannelSR_DelayTimer__sf512 => 4
  | BSR_Config__logicalChannelSR_DelayTimer__sf1024 => 5
  | BSR_Config__logicalChannelSR_DelayTimer__sf2560 => 6
  | BSR_Config__logicalChannelSR_DelayTimer__spare1 => 7
  end.
Definition BSR_Config__logicalChannelSR_DelayTimer__F2 n :=
  match n with
  | 0 => BSR_Config__logicalChannelSR_DelayTimer__sf20
  | 1 => BSR_Config__logicalChannelSR_DelayTimer__sf40
  | 2 => BSR_Config__logicalChannelSR_DelayTimer__sf64
  | 3 => BSR_Config__logicalChannelSR_DelayTimer__sf128
  | 4 => BSR_Config__logicalChannelSR_DelayTimer__sf512
  | 5 => BSR_Config__logicalChannelSR_DelayTimer__sf1024
  | 6 => BSR_Config__logicalChannelSR_DelayTimer__sf2560
  | 7 => BSR_Config__logicalChannelSR_DelayTimer__spare1
  | _ => BSR_Config__logicalChannelSR_DelayTimer__sf20
  end.
Lemma BSR_Config__logicalChannelSR_DelayTimer__F1F2 : forall x : BSR_Config__logicalChannelSR_DelayTimer__Type, (BSR_Config__logicalChannelSR_DelayTimer__F1 x <= 7) /\ BSR_Config__logicalChannelSR_DelayTimer__F2 (BSR_Config__logicalChannelSR_DelayTimer__F1 x) = x. imp_solve. Qed.
Lemma BSR_Config__logicalChannelSR_DelayTimer__F2F1 : forall (y : nat) (H : y <= 7), BSR_Config__logicalChannelSR_DelayTimer__F1 (BSR_Config__logicalChannelSR_DelayTimer__F2 y) = y. enum_solve H y. Qed.

Record BSR_Config__Type : Set :=
  make__BSR_Config__Type {
    BSR_Config__periodicBSR_Timer : BSR_Config__periodicBSR_Timer__Type ;
    BSR_Config__retxBSR_Timer : BSR_Config__retxBSR_Timer__Type ;
    BSR_Config__logicalChannelSR_DelayTimer : option BSR_Config__logicalChannelSR_DelayTimer__Type ;
}.
Definition BSR_Config__root_list : list seq_elem := (
 Nor BSR_Config__periodicBSR_Timer__Type BSR_Config__periodicBSR_Timer__cond ::
 Nor BSR_Config__retxBSR_Timer__Type BSR_Config__retxBSR_Timer__cond ::
 Opt BSR_Config__logicalChannelSR_DelayTimer__Type BSR_Config__logicalChannelSR_DelayTimer__cond ::
 nil).
Definition BSR_Config__ext_list : list typ := (
  nil).
Definition BSR_Config__cond (z : BSR_Config__Type) := 
(  BSR_Config__periodicBSR_Timer__cond (BSR_Config__periodicBSR_Timer z) /\
  BSR_Config__retxBSR_Timer__cond (BSR_Config__retxBSR_Timer z) /\
  opt_cond BSR_Config__logicalChannelSR_DelayTimer__cond (BSR_Config__logicalChannelSR_DelayTimer z) /\
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
Definition BSR_Config__periodicBSR_Timer__Format : T_Format BSR_Config__periodicBSR_Timer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BSR_Config__periodicBSR_Timer__nat__Format BSR_Config__periodicBSR_Timer__F1 BSR_Config__periodicBSR_Timer__F2 BSR_Config__periodicBSR_Timer__F1F2 BSR_Config__periodicBSR_Timer__F2F1.

Opaque BSR_Config__periodicBSR_Timer__cond BSR_Config__periodicBSR_Timer__Format.

Definition BSR_Config__retxBSR_Timer__Format : T_Format BSR_Config__retxBSR_Timer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BSR_Config__retxBSR_Timer__nat__Format BSR_Config__retxBSR_Timer__F1 BSR_Config__retxBSR_Timer__F2 BSR_Config__retxBSR_Timer__F1F2 BSR_Config__retxBSR_Timer__F2F1.

Opaque BSR_Config__retxBSR_Timer__cond BSR_Config__retxBSR_Timer__Format.

Definition BSR_Config__logicalChannelSR_DelayTimer__Format : T_Format BSR_Config__logicalChannelSR_DelayTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BSR_Config__logicalChannelSR_DelayTimer__nat__Format BSR_Config__logicalChannelSR_DelayTimer__F1 BSR_Config__logicalChannelSR_DelayTimer__F2 BSR_Config__logicalChannelSR_DelayTimer__F1F2 BSR_Config__logicalChannelSR_DelayTimer__F2F1.

Opaque BSR_Config__logicalChannelSR_DelayTimer__cond BSR_Config__logicalChannelSR_DelayTimer__Format.


Definition BSR_Config__root_Format_Type := Eval cbn in seq_format_prod BSR_Config__root_list.
Definition BSR_Config__root_Format_list : BSR_Config__root_Format_Type :=
  (BSR_Config__periodicBSR_Timer__Format, (BSR_Config__retxBSR_Timer__Format, (BSR_Config__logicalChannelSR_DelayTimer__Format, unit_format))).

Definition BSR_Config__ext_Format_Type := Eval cbn in get_formats BSR_Config__ext_list.
Definition BSR_Config__ext_Format_list : BSR_Config__ext_Format_Type :=
  unit__Format.

Definition BSR_Config__list_type : Set := (seq_type BSR_Config__root_list) * (seq_ext_type BSR_Config__ext_list).
Definition BSR_Config__list_cond (z : BSR_Config__list_type) : Prop :=
        (seq_cond BSR_Config__root_list (fst z)) /\ (seq_ext_cond BSR_Config__ext_list (snd z)).
Definition BSR_Config__list_format : T_Format BSR_Config__list_type BSR_Config__list_cond :=
 (* Eval compute in *) seq_ext_format BSR_Config__root_list BSR_Config__root_Format_list BSR_Config__ext_list BSR_Config__ext_Format_list.

Opaque BSR_Config__list_format.
Definition BSR_Config__F1 (z : BSR_Config__Type) : BSR_Config__list_type :=
  (((BSR_Config__periodicBSR_Timer z, (BSR_Config__retxBSR_Timer z, (BSR_Config__logicalChannelSR_DelayTimer z, tt)))), (
tt)).
Definition BSR_Config__F2 (y : BSR_Config__list_type) : BSR_Config__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__BSR_Config__Type j0 j1 j2
  end.
Definition BSR_Config__helper1 : (forall a : BSR_Config__Type, BSR_Config__cond a -> BSR_Config__list_cond (BSR_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BSR_Config__helper2 : (forall a : BSR_Config__Type, BSR_Config__F2 (BSR_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BSR_Config__helper3 : (forall b : BSR_Config__list_type, BSR_Config__list_cond b -> BSR_Config__cond (BSR_Config__F2 b) /\ BSR_Config__F1 (BSR_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BSR_Config__cond, BSR_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BSR_Config__Format : T_Format BSR_Config__Type BSR_Config__cond :=
 proj2_format BSR_Config__cond BSR_Config__list_format  BSR_Config__F1 BSR_Config__F2 BSR_Config__helper1 BSR_Config__helper2 BSR_Config__helper3.

Opaque BSR_Config__cond BSR_Config__Format.

