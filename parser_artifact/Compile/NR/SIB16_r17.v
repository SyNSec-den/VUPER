Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqPriorityListSlicing_r17.

Opaque FreqPriorityListSlicing_r17__cond FreqPriorityListSlicing_r17__Format.

Record SIB16_r17__Type : Set :=
  make__SIB16_r17__Type {
    SIB16_r17__freqPriorityListSlicing_r17 : option FreqPriorityListSlicing_r17__Type ;
    SIB16_r17__lateNonCriticalExtension : option octet_string ;
}.
Definition SIB16_r17__root_list : list seq_elem := (
 Opt FreqPriorityListSlicing_r17__Type FreqPriorityListSlicing_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB16_r17__ext_list : list typ := (
  nil).
Definition SIB16_r17__cond (z : SIB16_r17__Type) := 
(  opt_cond FreqPriorityListSlicing_r17__cond (SIB16_r17__freqPriorityListSlicing_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB16_r17__lateNonCriticalExtension z) /\
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

Definition SIB16_r17__root_Format_Type := Eval cbn in seq_format_prod SIB16_r17__root_list.
Definition SIB16_r17__root_Format_list : SIB16_r17__root_Format_Type :=
  (FreqPriorityListSlicing_r17__Format, (octet_string_nc__Format, unit_format)).

Definition SIB16_r17__ext_Format_Type := Eval cbn in get_formats SIB16_r17__ext_list.
Definition SIB16_r17__ext_Format_list : SIB16_r17__ext_Format_Type :=
  unit__Format.

Definition SIB16_r17__list_type : Set := (seq_type SIB16_r17__root_list) * (seq_ext_type SIB16_r17__ext_list).
Definition SIB16_r17__list_cond (z : SIB16_r17__list_type) : Prop :=
        (seq_cond SIB16_r17__root_list (fst z)) /\ (seq_ext_cond SIB16_r17__ext_list (snd z)).
Definition SIB16_r17__list_format : T_Format SIB16_r17__list_type SIB16_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SIB16_r17__root_list SIB16_r17__root_Format_list SIB16_r17__ext_list SIB16_r17__ext_Format_list.

Opaque SIB16_r17__list_format.
Definition SIB16_r17__F1 (z : SIB16_r17__Type) : SIB16_r17__list_type :=
  (((SIB16_r17__freqPriorityListSlicing_r17 z, (SIB16_r17__lateNonCriticalExtension z, tt))), (
tt)).
Definition SIB16_r17__F2 (y : SIB16_r17__list_type) : SIB16_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__SIB16_r17__Type j0 j1
  end.
Definition SIB16_r17__helper1 : (forall a : SIB16_r17__Type, SIB16_r17__cond a -> SIB16_r17__list_cond (SIB16_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB16_r17__helper2 : (forall a : SIB16_r17__Type, SIB16_r17__F2 (SIB16_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB16_r17__helper3 : (forall b : SIB16_r17__list_type, SIB16_r17__list_cond b -> SIB16_r17__cond (SIB16_r17__F2 b) /\ SIB16_r17__F1 (SIB16_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB16_r17__cond, SIB16_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB16_r17__Format : T_Format SIB16_r17__Type SIB16_r17__cond :=
 proj2_format SIB16_r17__cond SIB16_r17__list_format  SIB16_r17__F1 SIB16_r17__F2 SIB16_r17__helper1 SIB16_r17__helper2 SIB16_r17__helper3.

Opaque SIB16_r17__cond SIB16_r17__Format.

