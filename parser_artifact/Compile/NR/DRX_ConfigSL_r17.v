Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__helper1 : (0 <= 56)%Z.  lia. Qed.
Lemma DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__helper2 : to_bit_sz (Z.to_nat (56 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (56 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__Type := Z.
Definition DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__cond := (fun z => (0 <= z <= 56)%Z).
Inductive DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Type : Set :=
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl0
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl1
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl2
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl4
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl6
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl8
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl16
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl24
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl33
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl40
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl64
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl80
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl96
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl112
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl128
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl160
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl320
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare15
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare14
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare13
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare12
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare11
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare10
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare9
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare8
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare7
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare6
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare5
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare4
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare3
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare2
 | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare1
.
Definition DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__cond := (fun (_ : DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Type) => True).
Lemma DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__nat__helper.

Definition DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1 t :=
  match t with
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl0 => 0
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl1 => 1
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl2 => 2
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl4 => 3
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl6 => 4
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl8 => 5
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl16 => 6
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl24 => 7
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl33 => 8
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl40 => 9
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl64 => 10
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl80 => 11
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl96 => 12
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl112 => 13
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl128 => 14
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl160 => 15
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl320 => 16
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare15 => 17
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare14 => 18
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare13 => 19
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare12 => 20
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare11 => 21
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare10 => 22
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare9 => 23
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare8 => 24
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare7 => 25
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare6 => 26
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare5 => 27
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare4 => 28
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare3 => 29
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare2 => 30
  | DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare1 => 31
  end.
Definition DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F2 n :=
  match n with
  | 0 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl0
  | 1 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl1
  | 2 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl2
  | 3 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl4
  | 4 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl6
  | 5 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl8
  | 6 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl16
  | 7 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl24
  | 8 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl33
  | 9 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl40
  | 10 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl64
  | 11 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl80
  | 12 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl96
  | 13 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl112
  | 14 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl128
  | 15 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl160
  | 16 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl320
  | 17 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare15
  | 18 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare14
  | 19 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare13
  | 20 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare12
  | 21 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare11
  | 22 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare10
  | 23 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare9
  | 24 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare8
  | 25 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare7
  | 26 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare6
  | 27 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare5
  | 28 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare4
  | 29 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare3
  | 30 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare2
  | 31 => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__spare1
  | _ => DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__sl0
  end.
Lemma DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1F2 : forall x : DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Type, (DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1 x <= 31) /\ DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F2 (DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1 x) = x. imp_solve. Qed.
Lemma DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F2F1 : forall (y : nat) (H : y <= 31), DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1 (DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F2 y) = y. enum_solve H y. Qed.

Record DRX_ConfigSL_r17__Type : Set :=
  make__DRX_ConfigSL_r17__Type {
    DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17 : Z ;
    DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17 : DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Type ;
}.
Definition DRX_ConfigSL_r17__list := (
 Nor Z DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__cond ::
 Nor DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Type DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__cond ::
 nil).
Definition DRX_ConfigSL_r17__cond z := 
  DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__cond (DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17 z) /\
  DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__cond (DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17 z) /\
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
Definition DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__Format : T_Format Z DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__cond :=
 ranged_int_format (0) (56) DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__helper1 DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__helper2.

Opaque DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__cond DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__Format.

Definition DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Format : T_Format DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__nat__Format DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1 DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F2 DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F1F2 DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__F2F1.

Opaque DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__cond DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Format.


Definition DRX_ConfigSL_r17__Format_Type := Eval cbn in seq_format_prod DRX_ConfigSL_r17__list.
Definition DRX_ConfigSL_r17__Format_list : DRX_ConfigSL_r17__Format_Type :=
  (DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17__Format, (DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17__Format, unit_format)).
Definition DRX_ConfigSL_r17__list__Format := (*Eval compute in *) seq_format DRX_ConfigSL_r17__list DRX_ConfigSL_r17__Format_list.
Definition DRX_ConfigSL_r17__F1 z :=
  (DRX_ConfigSL_r17__drx_HARQ_RTT_TimerSL_r17 z, (DRX_ConfigSL_r17__drx_RetransmissionTimerSL_r17 z, tt)).
Definition DRX_ConfigSL_r17__F2 (y : seq_type DRX_ConfigSL_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DRX_ConfigSL_r17__Type i0 i1
  end.
Lemma DRX_ConfigSL_r17__F1F2_cond (z : DRX_ConfigSL_r17__Type)
  : DRX_ConfigSL_r17__cond z ->
  (seq_cond DRX_ConfigSL_r17__list (DRX_ConfigSL_r17__F1 z)).
intro H. unfold DRX_ConfigSL_r17__cond in H. simpl. auto. Qed.
Lemma DRX_ConfigSL_r17__F1F2_cond2 (z : DRX_ConfigSL_r17__Type)
 : DRX_ConfigSL_r17__F2 (DRX_ConfigSL_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_ConfigSL_r17__F2F1_cond (y : seq_type DRX_ConfigSL_r17__list)
  : seq_cond DRX_ConfigSL_r17__list y ->
 (DRX_ConfigSL_r17__cond (DRX_ConfigSL_r17__F2 y)) /\  DRX_ConfigSL_r17__F1 (DRX_ConfigSL_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_ConfigSL_r17__cond. simpl in *. auto.
 - simpl. unfold DRX_ConfigSL_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_ConfigSL_r17__Format : T_Format DRX_ConfigSL_r17__Type DRX_ConfigSL_r17__cond :=
        proj2_format  DRX_ConfigSL_r17__cond DRX_ConfigSL_r17__list__Format
    DRX_ConfigSL_r17__F1 DRX_ConfigSL_r17__F2 DRX_ConfigSL_r17__F1F2_cond  DRX_ConfigSL_r17__F1F2_cond2 DRX_ConfigSL_r17__F2F1_cond.
Opaque DRX_ConfigSL_r17__cond DRX_ConfigSL_r17__Format.

