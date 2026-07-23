Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.GIN_Element_r17.

Opaque GIN_Element_r17__cond GIN_Element_r17__Format.

Definition SIB18_r17__gin_ElementList_r17__Type := list GIN_Element_r17__Type.

Lemma SIB18_r17__gin_ElementList_r17__helper1 : (0 <= 1 <= maxGIN_r17)%Z. unfold maxGIN_r17.
 lia. Qed.
Lemma SIB18_r17__gin_ElementList_r17__helper2 : to_bit_sz (Z.to_nat (maxGIN_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxGIN_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SIB18_r17__gin_ElementList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB18_r17__gin_ElementList_r17__cond (z : SIB18_r17__gin_ElementList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxGIN_r17)%Z /\ (list_and GIN_Element_r17__cond z) .

Require Import NR.GINs_PerSNPN_r17.

Opaque GINs_PerSNPN_r17__cond GINs_PerSNPN_r17__Format.

Definition SIB18_r17__gins_PerSNPN_List_r17__Type := list GINs_PerSNPN_r17__Type.

Lemma SIB18_r17__gins_PerSNPN_List_r17__helper1 : (0 <= 1 <= maxNPN_r16)%Z. unfold maxNPN_r16.
 lia. Qed.
Lemma SIB18_r17__gins_PerSNPN_List_r17__helper2 : to_bit_sz (Z.to_nat (maxNPN_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNPN_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SIB18_r17__gins_PerSNPN_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB18_r17__gins_PerSNPN_List_r17__cond (z : SIB18_r17__gins_PerSNPN_List_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNPN_r16)%Z /\ (list_and GINs_PerSNPN_r17__cond z) .

Record SIB18_r17__Type : Set :=
  make__SIB18_r17__Type {
    SIB18_r17__gin_ElementList_r17 : option SIB18_r17__gin_ElementList_r17__Type ;
    SIB18_r17__gins_PerSNPN_List_r17 : option SIB18_r17__gins_PerSNPN_List_r17__Type ;
    SIB18_r17__lateNonCriticalExtension : option octet_string ;
}.
Definition SIB18_r17__root_list : list seq_elem := (
 Opt SIB18_r17__gin_ElementList_r17__Type SIB18_r17__gin_ElementList_r17__cond ::
 Opt SIB18_r17__gins_PerSNPN_List_r17__Type SIB18_r17__gins_PerSNPN_List_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB18_r17__ext_list : list typ := (
  nil).
Definition SIB18_r17__cond (z : SIB18_r17__Type) := 
(  opt_cond SIB18_r17__gin_ElementList_r17__cond (SIB18_r17__gin_ElementList_r17 z) /\
  opt_cond SIB18_r17__gins_PerSNPN_List_r17__cond (SIB18_r17__gins_PerSNPN_List_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB18_r17__lateNonCriticalExtension z) /\
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
Definition SIB18_r17__gin_ElementList_r17__Format : T_Format SIB18_r17__gin_ElementList_r17__Type SIB18_r17__gin_ElementList_r17__cond := seq_of_format GIN_Element_r17__Format 1 maxGIN_r17 SIB18_r17__gin_ElementList_r17__helper1 SIB18_r17__gin_ElementList_r17__helper2.

Opaque SIB18_r17__gin_ElementList_r17__cond SIB18_r17__gin_ElementList_r17__Format.

Definition SIB18_r17__gins_PerSNPN_List_r17__Format : T_Format SIB18_r17__gins_PerSNPN_List_r17__Type SIB18_r17__gins_PerSNPN_List_r17__cond := seq_of_format GINs_PerSNPN_r17__Format 1 maxNPN_r16 SIB18_r17__gins_PerSNPN_List_r17__helper1 SIB18_r17__gins_PerSNPN_List_r17__helper2.

Opaque SIB18_r17__gins_PerSNPN_List_r17__cond SIB18_r17__gins_PerSNPN_List_r17__Format.


Definition SIB18_r17__root_Format_Type := Eval cbn in seq_format_prod SIB18_r17__root_list.
Definition SIB18_r17__root_Format_list : SIB18_r17__root_Format_Type :=
  (SIB18_r17__gin_ElementList_r17__Format, (SIB18_r17__gins_PerSNPN_List_r17__Format, (octet_string_nc__Format, unit_format))).

Definition SIB18_r17__ext_Format_Type := Eval cbn in get_formats SIB18_r17__ext_list.
Definition SIB18_r17__ext_Format_list : SIB18_r17__ext_Format_Type :=
  unit__Format.

Definition SIB18_r17__list_type : Set := (seq_type SIB18_r17__root_list) * (seq_ext_type SIB18_r17__ext_list).
Definition SIB18_r17__list_cond (z : SIB18_r17__list_type) : Prop :=
        (seq_cond SIB18_r17__root_list (fst z)) /\ (seq_ext_cond SIB18_r17__ext_list (snd z)).
Definition SIB18_r17__list_format : T_Format SIB18_r17__list_type SIB18_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SIB18_r17__root_list SIB18_r17__root_Format_list SIB18_r17__ext_list SIB18_r17__ext_Format_list.

Opaque SIB18_r17__list_format.
Definition SIB18_r17__F1 (z : SIB18_r17__Type) : SIB18_r17__list_type :=
  (((SIB18_r17__gin_ElementList_r17 z, (SIB18_r17__gins_PerSNPN_List_r17 z, (SIB18_r17__lateNonCriticalExtension z, tt)))), (
tt)).
Definition SIB18_r17__F2 (y : SIB18_r17__list_type) : SIB18_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__SIB18_r17__Type j0 j1 j2
  end.
Definition SIB18_r17__helper1 : (forall a : SIB18_r17__Type, SIB18_r17__cond a -> SIB18_r17__list_cond (SIB18_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB18_r17__helper2 : (forall a : SIB18_r17__Type, SIB18_r17__F2 (SIB18_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB18_r17__helper3 : (forall b : SIB18_r17__list_type, SIB18_r17__list_cond b -> SIB18_r17__cond (SIB18_r17__F2 b) /\ SIB18_r17__F1 (SIB18_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB18_r17__cond, SIB18_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB18_r17__Format : T_Format SIB18_r17__Type SIB18_r17__cond :=
 proj2_format SIB18_r17__cond SIB18_r17__list_format  SIB18_r17__F1 SIB18_r17__F2 SIB18_r17__helper1 SIB18_r17__helper2 SIB18_r17__helper3.

Opaque SIB18_r17__cond SIB18_r17__Format.

