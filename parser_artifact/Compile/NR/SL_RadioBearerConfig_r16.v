Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SLRB_Uu_ConfigIndex_r16.

Opaque SLRB_Uu_ConfigIndex_r16__cond SLRB_Uu_ConfigIndex_r16__Format.

Require Import NR.SL_SDAP_Config_r16.

Opaque SL_SDAP_Config_r16__cond SL_SDAP_Config_r16__Format.

Require Import NR.SL_PDCP_Config_r16.

Opaque SL_PDCP_Config_r16__cond SL_PDCP_Config_r16__Format.

Inductive SL_RadioBearerConfig_r16__sl_TransRange_r16__Type : Set :=
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m20
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m50
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m80
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m100
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m120
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m150
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m180
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m200
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m220
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m250
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m270
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m300
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m350
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m370
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m400
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m420
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m450
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m480
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m500
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m550
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m600
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m700
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__m1000
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare9
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare8
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare7
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare6
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare5
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare4
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare3
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare2
 | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare1
.
Definition SL_RadioBearerConfig_r16__sl_TransRange_r16__cond := (fun (_ : SL_RadioBearerConfig_r16__sl_TransRange_r16__Type) => True).
Lemma SL_RadioBearerConfig_r16__sl_TransRange_r16__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_RadioBearerConfig_r16__sl_TransRange_r16__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_RadioBearerConfig_r16__sl_TransRange_r16__nat__helper.

Definition SL_RadioBearerConfig_r16__sl_TransRange_r16__F1 t :=
  match t with
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m20 => 0
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m50 => 1
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m80 => 2
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m100 => 3
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m120 => 4
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m150 => 5
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m180 => 6
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m200 => 7
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m220 => 8
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m250 => 9
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m270 => 10
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m300 => 11
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m350 => 12
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m370 => 13
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m400 => 14
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m420 => 15
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m450 => 16
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m480 => 17
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m500 => 18
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m550 => 19
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m600 => 20
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m700 => 21
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__m1000 => 22
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare9 => 23
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare8 => 24
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare7 => 25
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare6 => 26
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare5 => 27
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare4 => 28
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare3 => 29
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare2 => 30
  | SL_RadioBearerConfig_r16__sl_TransRange_r16__spare1 => 31
  end.
Definition SL_RadioBearerConfig_r16__sl_TransRange_r16__F2 n :=
  match n with
  | 0 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m20
  | 1 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m50
  | 2 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m80
  | 3 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m100
  | 4 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m120
  | 5 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m150
  | 6 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m180
  | 7 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m200
  | 8 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m220
  | 9 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m250
  | 10 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m270
  | 11 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m300
  | 12 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m350
  | 13 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m370
  | 14 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m400
  | 15 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m420
  | 16 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m450
  | 17 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m480
  | 18 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m500
  | 19 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m550
  | 20 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m600
  | 21 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m700
  | 22 => SL_RadioBearerConfig_r16__sl_TransRange_r16__m1000
  | 23 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare9
  | 24 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare8
  | 25 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare7
  | 26 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare6
  | 27 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare5
  | 28 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare4
  | 29 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare3
  | 30 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare2
  | 31 => SL_RadioBearerConfig_r16__sl_TransRange_r16__spare1
  | _ => SL_RadioBearerConfig_r16__sl_TransRange_r16__m20
  end.
Lemma SL_RadioBearerConfig_r16__sl_TransRange_r16__F1F2 : forall x : SL_RadioBearerConfig_r16__sl_TransRange_r16__Type, (SL_RadioBearerConfig_r16__sl_TransRange_r16__F1 x <= 31) /\ SL_RadioBearerConfig_r16__sl_TransRange_r16__F2 (SL_RadioBearerConfig_r16__sl_TransRange_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_RadioBearerConfig_r16__sl_TransRange_r16__F2F1 : forall (y : nat) (H : y <= 31), SL_RadioBearerConfig_r16__sl_TransRange_r16__F1 (SL_RadioBearerConfig_r16__sl_TransRange_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_RadioBearerConfig_r16__Type : Set :=
  make__SL_RadioBearerConfig_r16__Type {
    SL_RadioBearerConfig_r16__slrb_Uu_ConfigIndex_r16 : SLRB_Uu_ConfigIndex_r16__Type ;
    SL_RadioBearerConfig_r16__sl_SDAP_Config_r16 : option SL_SDAP_Config_r16__Type ;
    SL_RadioBearerConfig_r16__sl_PDCP_Config_r16 : option SL_PDCP_Config_r16__Type ;
    SL_RadioBearerConfig_r16__sl_TransRange_r16 : option SL_RadioBearerConfig_r16__sl_TransRange_r16__Type ;
}.
Definition SL_RadioBearerConfig_r16__root_list : list seq_elem := (
 Nor SLRB_Uu_ConfigIndex_r16__Type SLRB_Uu_ConfigIndex_r16__cond ::
 Opt SL_SDAP_Config_r16__Type SL_SDAP_Config_r16__cond ::
 Opt SL_PDCP_Config_r16__Type SL_PDCP_Config_r16__cond ::
 Opt SL_RadioBearerConfig_r16__sl_TransRange_r16__Type SL_RadioBearerConfig_r16__sl_TransRange_r16__cond ::
 nil).
Definition SL_RadioBearerConfig_r16__ext_list : list typ := (
  nil).
Definition SL_RadioBearerConfig_r16__cond (z : SL_RadioBearerConfig_r16__Type) := 
(  SLRB_Uu_ConfigIndex_r16__cond (SL_RadioBearerConfig_r16__slrb_Uu_ConfigIndex_r16 z) /\
  opt_cond SL_SDAP_Config_r16__cond (SL_RadioBearerConfig_r16__sl_SDAP_Config_r16 z) /\
  opt_cond SL_PDCP_Config_r16__cond (SL_RadioBearerConfig_r16__sl_PDCP_Config_r16 z) /\
  opt_cond SL_RadioBearerConfig_r16__sl_TransRange_r16__cond (SL_RadioBearerConfig_r16__sl_TransRange_r16 z) /\
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
Definition SL_RadioBearerConfig_r16__sl_TransRange_r16__Format : T_Format SL_RadioBearerConfig_r16__sl_TransRange_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_RadioBearerConfig_r16__sl_TransRange_r16__nat__Format SL_RadioBearerConfig_r16__sl_TransRange_r16__F1 SL_RadioBearerConfig_r16__sl_TransRange_r16__F2 SL_RadioBearerConfig_r16__sl_TransRange_r16__F1F2 SL_RadioBearerConfig_r16__sl_TransRange_r16__F2F1.

Opaque SL_RadioBearerConfig_r16__sl_TransRange_r16__cond SL_RadioBearerConfig_r16__sl_TransRange_r16__Format.


Definition SL_RadioBearerConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_RadioBearerConfig_r16__root_list.
Definition SL_RadioBearerConfig_r16__root_Format_list : SL_RadioBearerConfig_r16__root_Format_Type :=
  (SLRB_Uu_ConfigIndex_r16__Format, (SL_SDAP_Config_r16__Format, (SL_PDCP_Config_r16__Format, (SL_RadioBearerConfig_r16__sl_TransRange_r16__Format, unit_format)))).

Definition SL_RadioBearerConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_RadioBearerConfig_r16__ext_list.
Definition SL_RadioBearerConfig_r16__ext_Format_list : SL_RadioBearerConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_RadioBearerConfig_r16__list_type : Set := (seq_type SL_RadioBearerConfig_r16__root_list) * (seq_ext_type SL_RadioBearerConfig_r16__ext_list).
Definition SL_RadioBearerConfig_r16__list_cond (z : SL_RadioBearerConfig_r16__list_type) : Prop :=
        (seq_cond SL_RadioBearerConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_RadioBearerConfig_r16__ext_list (snd z)).
Definition SL_RadioBearerConfig_r16__list_format : T_Format SL_RadioBearerConfig_r16__list_type SL_RadioBearerConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_RadioBearerConfig_r16__root_list SL_RadioBearerConfig_r16__root_Format_list SL_RadioBearerConfig_r16__ext_list SL_RadioBearerConfig_r16__ext_Format_list.

Opaque SL_RadioBearerConfig_r16__list_format.
Definition SL_RadioBearerConfig_r16__F1 (z : SL_RadioBearerConfig_r16__Type) : SL_RadioBearerConfig_r16__list_type :=
  (((SL_RadioBearerConfig_r16__slrb_Uu_ConfigIndex_r16 z, (SL_RadioBearerConfig_r16__sl_SDAP_Config_r16 z, (SL_RadioBearerConfig_r16__sl_PDCP_Config_r16 z, (SL_RadioBearerConfig_r16__sl_TransRange_r16 z, tt))))), (
tt)).
Definition SL_RadioBearerConfig_r16__F2 (y : SL_RadioBearerConfig_r16__list_type) : SL_RadioBearerConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SL_RadioBearerConfig_r16__Type j0 j1 j2 j3
  end.
Definition SL_RadioBearerConfig_r16__helper1 : (forall a : SL_RadioBearerConfig_r16__Type, SL_RadioBearerConfig_r16__cond a -> SL_RadioBearerConfig_r16__list_cond (SL_RadioBearerConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_RadioBearerConfig_r16__helper2 : (forall a : SL_RadioBearerConfig_r16__Type, SL_RadioBearerConfig_r16__F2 (SL_RadioBearerConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_RadioBearerConfig_r16__helper3 : (forall b : SL_RadioBearerConfig_r16__list_type, SL_RadioBearerConfig_r16__list_cond b -> SL_RadioBearerConfig_r16__cond (SL_RadioBearerConfig_r16__F2 b) /\ SL_RadioBearerConfig_r16__F1 (SL_RadioBearerConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_RadioBearerConfig_r16__cond, SL_RadioBearerConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_RadioBearerConfig_r16__Format : T_Format SL_RadioBearerConfig_r16__Type SL_RadioBearerConfig_r16__cond :=
 proj2_format SL_RadioBearerConfig_r16__cond SL_RadioBearerConfig_r16__list_format  SL_RadioBearerConfig_r16__F1 SL_RadioBearerConfig_r16__F2 SL_RadioBearerConfig_r16__helper1 SL_RadioBearerConfig_r16__helper2 SL_RadioBearerConfig_r16__helper3.

Opaque SL_RadioBearerConfig_r16__cond SL_RadioBearerConfig_r16__Format.

