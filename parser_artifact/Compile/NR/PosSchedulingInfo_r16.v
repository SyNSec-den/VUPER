Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PosSchedulingInfo_r16__offsetToSI_Used_r16__Type : Set :=
 | PosSchedulingInfo_r16__offsetToSI_Used_r16__true
.
Definition PosSchedulingInfo_r16__offsetToSI_Used_r16__cond := (fun (_ : PosSchedulingInfo_r16__offsetToSI_Used_r16__Type) => True).
Lemma PosSchedulingInfo_r16__offsetToSI_Used_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosSchedulingInfo_r16__offsetToSI_Used_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PosSchedulingInfo_r16__offsetToSI_Used_r16__nat__helper.

Definition PosSchedulingInfo_r16__offsetToSI_Used_r16__F1 t :=
  match t with
  | PosSchedulingInfo_r16__offsetToSI_Used_r16__true => 0
  end.
Definition PosSchedulingInfo_r16__offsetToSI_Used_r16__F2 n :=
  match n with
  | 0 => PosSchedulingInfo_r16__offsetToSI_Used_r16__true
  | _ => PosSchedulingInfo_r16__offsetToSI_Used_r16__true
  end.
Lemma PosSchedulingInfo_r16__offsetToSI_Used_r16__F1F2 : forall x : PosSchedulingInfo_r16__offsetToSI_Used_r16__Type, (PosSchedulingInfo_r16__offsetToSI_Used_r16__F1 x <= 0) /\ PosSchedulingInfo_r16__offsetToSI_Used_r16__F2 (PosSchedulingInfo_r16__offsetToSI_Used_r16__F1 x) = x. imp_solve. Qed.
Lemma PosSchedulingInfo_r16__offsetToSI_Used_r16__F2F1 : forall (y : nat) (H : y <= 0), PosSchedulingInfo_r16__offsetToSI_Used_r16__F1 (PosSchedulingInfo_r16__offsetToSI_Used_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PosSchedulingInfo_r16__posSI_Periodicity_r16__Type : Set :=
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf8
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf16
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf32
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf64
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf128
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf256
 | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf512
.
Definition PosSchedulingInfo_r16__posSI_Periodicity_r16__cond := (fun (_ : PosSchedulingInfo_r16__posSI_Periodicity_r16__Type) => True).
Lemma PosSchedulingInfo_r16__posSI_Periodicity_r16__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosSchedulingInfo_r16__posSI_Periodicity_r16__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 PosSchedulingInfo_r16__posSI_Periodicity_r16__nat__helper.

Definition PosSchedulingInfo_r16__posSI_Periodicity_r16__F1 t :=
  match t with
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf8 => 0
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf16 => 1
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf32 => 2
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf64 => 3
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf128 => 4
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf256 => 5
  | PosSchedulingInfo_r16__posSI_Periodicity_r16__rf512 => 6
  end.
Definition PosSchedulingInfo_r16__posSI_Periodicity_r16__F2 n :=
  match n with
  | 0 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf8
  | 1 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf16
  | 2 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf32
  | 3 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf64
  | 4 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf128
  | 5 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf256
  | 6 => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf512
  | _ => PosSchedulingInfo_r16__posSI_Periodicity_r16__rf8
  end.
Lemma PosSchedulingInfo_r16__posSI_Periodicity_r16__F1F2 : forall x : PosSchedulingInfo_r16__posSI_Periodicity_r16__Type, (PosSchedulingInfo_r16__posSI_Periodicity_r16__F1 x <= 6) /\ PosSchedulingInfo_r16__posSI_Periodicity_r16__F2 (PosSchedulingInfo_r16__posSI_Periodicity_r16__F1 x) = x. imp_solve. Qed.
Lemma PosSchedulingInfo_r16__posSI_Periodicity_r16__F2F1 : forall (y : nat) (H : y <= 6), PosSchedulingInfo_r16__posSI_Periodicity_r16__F1 (PosSchedulingInfo_r16__posSI_Periodicity_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Type : Set :=
 | PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__broadcasting
 | PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__notBroadcasting
.
Definition PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__cond := (fun (_ : PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Type) => True).
Lemma PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__nat__helper.

Definition PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1 t :=
  match t with
  | PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__broadcasting => 0
  | PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__notBroadcasting => 1
  end.
Definition PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F2 n :=
  match n with
  | 0 => PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__broadcasting
  | 1 => PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__notBroadcasting
  | _ => PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__broadcasting
  end.
Lemma PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1F2 : forall x : PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Type, (PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1 x <= 1) /\ PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F2 (PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1 x) = x. imp_solve. Qed.
Lemma PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F2F1 : forall (y : nat) (H : y <= 1), PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1 (PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PosSIB_MappingInfo_r16.

Opaque PosSIB_MappingInfo_r16__cond PosSIB_MappingInfo_r16__Format.

Record PosSchedulingInfo_r16__Type : Set :=
  make__PosSchedulingInfo_r16__Type {
    PosSchedulingInfo_r16__offsetToSI_Used_r16 : option PosSchedulingInfo_r16__offsetToSI_Used_r16__Type ;
    PosSchedulingInfo_r16__posSI_Periodicity_r16 : PosSchedulingInfo_r16__posSI_Periodicity_r16__Type ;
    PosSchedulingInfo_r16__posSI_BroadcastStatus_r16 : PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Type ;
    PosSchedulingInfo_r16__posSIB_MappingInfo_r16 : PosSIB_MappingInfo_r16__Type ;
}.
Definition PosSchedulingInfo_r16__root_list : list seq_elem := (
 Opt PosSchedulingInfo_r16__offsetToSI_Used_r16__Type PosSchedulingInfo_r16__offsetToSI_Used_r16__cond ::
 Nor PosSchedulingInfo_r16__posSI_Periodicity_r16__Type PosSchedulingInfo_r16__posSI_Periodicity_r16__cond ::
 Nor PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Type PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__cond ::
 Nor PosSIB_MappingInfo_r16__Type PosSIB_MappingInfo_r16__cond ::
 nil).
Definition PosSchedulingInfo_r16__ext_list : list typ := (
  nil).
Definition PosSchedulingInfo_r16__cond (z : PosSchedulingInfo_r16__Type) := 
(  opt_cond PosSchedulingInfo_r16__offsetToSI_Used_r16__cond (PosSchedulingInfo_r16__offsetToSI_Used_r16 z) /\
  PosSchedulingInfo_r16__posSI_Periodicity_r16__cond (PosSchedulingInfo_r16__posSI_Periodicity_r16 z) /\
  PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__cond (PosSchedulingInfo_r16__posSI_BroadcastStatus_r16 z) /\
  PosSIB_MappingInfo_r16__cond (PosSchedulingInfo_r16__posSIB_MappingInfo_r16 z) /\
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
Definition PosSchedulingInfo_r16__offsetToSI_Used_r16__Format : T_Format PosSchedulingInfo_r16__offsetToSI_Used_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosSchedulingInfo_r16__offsetToSI_Used_r16__nat__Format PosSchedulingInfo_r16__offsetToSI_Used_r16__F1 PosSchedulingInfo_r16__offsetToSI_Used_r16__F2 PosSchedulingInfo_r16__offsetToSI_Used_r16__F1F2 PosSchedulingInfo_r16__offsetToSI_Used_r16__F2F1.

Opaque PosSchedulingInfo_r16__offsetToSI_Used_r16__cond PosSchedulingInfo_r16__offsetToSI_Used_r16__Format.

Definition PosSchedulingInfo_r16__posSI_Periodicity_r16__Format : T_Format PosSchedulingInfo_r16__posSI_Periodicity_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosSchedulingInfo_r16__posSI_Periodicity_r16__nat__Format PosSchedulingInfo_r16__posSI_Periodicity_r16__F1 PosSchedulingInfo_r16__posSI_Periodicity_r16__F2 PosSchedulingInfo_r16__posSI_Periodicity_r16__F1F2 PosSchedulingInfo_r16__posSI_Periodicity_r16__F2F1.

Opaque PosSchedulingInfo_r16__posSI_Periodicity_r16__cond PosSchedulingInfo_r16__posSI_Periodicity_r16__Format.

Definition PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Format : T_Format PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__nat__Format PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1 PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F2 PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F1F2 PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__F2F1.

Opaque PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__cond PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Format.


Definition PosSchedulingInfo_r16__root_Format_Type := Eval cbn in seq_format_prod PosSchedulingInfo_r16__root_list.
Definition PosSchedulingInfo_r16__root_Format_list : PosSchedulingInfo_r16__root_Format_Type :=
  (PosSchedulingInfo_r16__offsetToSI_Used_r16__Format, (PosSchedulingInfo_r16__posSI_Periodicity_r16__Format, (PosSchedulingInfo_r16__posSI_BroadcastStatus_r16__Format, (PosSIB_MappingInfo_r16__Format, unit_format)))).

Definition PosSchedulingInfo_r16__ext_Format_Type := Eval cbn in get_formats PosSchedulingInfo_r16__ext_list.
Definition PosSchedulingInfo_r16__ext_Format_list : PosSchedulingInfo_r16__ext_Format_Type :=
  unit__Format.

Definition PosSchedulingInfo_r16__list_type : Set := (seq_type PosSchedulingInfo_r16__root_list) * (seq_ext_type PosSchedulingInfo_r16__ext_list).
Definition PosSchedulingInfo_r16__list_cond (z : PosSchedulingInfo_r16__list_type) : Prop :=
        (seq_cond PosSchedulingInfo_r16__root_list (fst z)) /\ (seq_ext_cond PosSchedulingInfo_r16__ext_list (snd z)).
Definition PosSchedulingInfo_r16__list_format : T_Format PosSchedulingInfo_r16__list_type PosSchedulingInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PosSchedulingInfo_r16__root_list PosSchedulingInfo_r16__root_Format_list PosSchedulingInfo_r16__ext_list PosSchedulingInfo_r16__ext_Format_list.

Opaque PosSchedulingInfo_r16__list_format.
Definition PosSchedulingInfo_r16__F1 (z : PosSchedulingInfo_r16__Type) : PosSchedulingInfo_r16__list_type :=
  (((PosSchedulingInfo_r16__offsetToSI_Used_r16 z, (PosSchedulingInfo_r16__posSI_Periodicity_r16 z, (PosSchedulingInfo_r16__posSI_BroadcastStatus_r16 z, (PosSchedulingInfo_r16__posSIB_MappingInfo_r16 z, tt))))), (
tt)).
Definition PosSchedulingInfo_r16__F2 (y : PosSchedulingInfo_r16__list_type) : PosSchedulingInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__PosSchedulingInfo_r16__Type j0 j1 j2 j3
  end.
Definition PosSchedulingInfo_r16__helper1 : (forall a : PosSchedulingInfo_r16__Type, PosSchedulingInfo_r16__cond a -> PosSchedulingInfo_r16__list_cond (PosSchedulingInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PosSchedulingInfo_r16__helper2 : (forall a : PosSchedulingInfo_r16__Type, PosSchedulingInfo_r16__F2 (PosSchedulingInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PosSchedulingInfo_r16__helper3 : (forall b : PosSchedulingInfo_r16__list_type, PosSchedulingInfo_r16__list_cond b -> PosSchedulingInfo_r16__cond (PosSchedulingInfo_r16__F2 b) /\ PosSchedulingInfo_r16__F1 (PosSchedulingInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PosSchedulingInfo_r16__cond, PosSchedulingInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PosSchedulingInfo_r16__Format : T_Format PosSchedulingInfo_r16__Type PosSchedulingInfo_r16__cond :=
 proj2_format PosSchedulingInfo_r16__cond PosSchedulingInfo_r16__list_format  PosSchedulingInfo_r16__F1 PosSchedulingInfo_r16__F2 PosSchedulingInfo_r16__helper1 PosSchedulingInfo_r16__helper2 PosSchedulingInfo_r16__helper3.

Opaque PosSchedulingInfo_r16__cond PosSchedulingInfo_r16__Format.

