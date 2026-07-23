Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NextHopChainingCount.

Opaque NextHopChainingCount__cond NextHopChainingCount__Format.

Record MasterKeyUpdate__Type : Set :=
  make__MasterKeyUpdate__Type {
    MasterKeyUpdate__keySetChangeIndicator : bool ;
    MasterKeyUpdate__nextHopChainingCount : NextHopChainingCount__Type ;
    MasterKeyUpdate__nas_Container : option octet_string ;
}.
Definition MasterKeyUpdate__root_list : list seq_elem := (
 Nor bool (fun _ => True) ::
 Nor NextHopChainingCount__Type NextHopChainingCount__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition MasterKeyUpdate__ext_list : list typ := (
  nil).
Definition MasterKeyUpdate__cond (z : MasterKeyUpdate__Type) := 
(  (fun _ => True) (MasterKeyUpdate__keySetChangeIndicator z) /\
  NextHopChainingCount__cond (MasterKeyUpdate__nextHopChainingCount z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MasterKeyUpdate__nas_Container z) /\
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

Definition MasterKeyUpdate__root_Format_Type := Eval cbn in seq_format_prod MasterKeyUpdate__root_list.
Definition MasterKeyUpdate__root_Format_list : MasterKeyUpdate__root_Format_Type :=
  (bool__Format, (NextHopChainingCount__Format, (octet_string_nc__Format, unit_format))).

Definition MasterKeyUpdate__ext_Format_Type := Eval cbn in get_formats MasterKeyUpdate__ext_list.
Definition MasterKeyUpdate__ext_Format_list : MasterKeyUpdate__ext_Format_Type :=
  unit__Format.

Definition MasterKeyUpdate__list_type : Set := (seq_type MasterKeyUpdate__root_list) * (seq_ext_type MasterKeyUpdate__ext_list).
Definition MasterKeyUpdate__list_cond (z : MasterKeyUpdate__list_type) : Prop :=
        (seq_cond MasterKeyUpdate__root_list (fst z)) /\ (seq_ext_cond MasterKeyUpdate__ext_list (snd z)).
Definition MasterKeyUpdate__list_format : T_Format MasterKeyUpdate__list_type MasterKeyUpdate__list_cond :=
 (* Eval compute in *) seq_ext_format MasterKeyUpdate__root_list MasterKeyUpdate__root_Format_list MasterKeyUpdate__ext_list MasterKeyUpdate__ext_Format_list.

Opaque MasterKeyUpdate__list_format.
Definition MasterKeyUpdate__F1 (z : MasterKeyUpdate__Type) : MasterKeyUpdate__list_type :=
  (((MasterKeyUpdate__keySetChangeIndicator z, (MasterKeyUpdate__nextHopChainingCount z, (MasterKeyUpdate__nas_Container z, tt)))), (
tt)).
Definition MasterKeyUpdate__F2 (y : MasterKeyUpdate__list_type) : MasterKeyUpdate__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__MasterKeyUpdate__Type j0 j1 j2
  end.
Definition MasterKeyUpdate__helper1 : (forall a : MasterKeyUpdate__Type, MasterKeyUpdate__cond a -> MasterKeyUpdate__list_cond (MasterKeyUpdate__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MasterKeyUpdate__helper2 : (forall a : MasterKeyUpdate__Type, MasterKeyUpdate__F2 (MasterKeyUpdate__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MasterKeyUpdate__helper3 : (forall b : MasterKeyUpdate__list_type, MasterKeyUpdate__list_cond b -> MasterKeyUpdate__cond (MasterKeyUpdate__F2 b) /\ MasterKeyUpdate__F1 (MasterKeyUpdate__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MasterKeyUpdate__cond, MasterKeyUpdate__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MasterKeyUpdate__Format : T_Format MasterKeyUpdate__Type MasterKeyUpdate__cond :=
 proj2_format MasterKeyUpdate__cond MasterKeyUpdate__list_format  MasterKeyUpdate__F1 MasterKeyUpdate__F2 MasterKeyUpdate__helper1 MasterKeyUpdate__helper2 MasterKeyUpdate__helper3.

Opaque MasterKeyUpdate__cond MasterKeyUpdate__Format.

