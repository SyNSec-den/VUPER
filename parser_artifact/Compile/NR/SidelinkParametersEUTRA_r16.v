Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandSidelinkEUTRA_r16.

Opaque BandSidelinkEUTRA_r16__cond BandSidelinkEUTRA_r16__Format.

Definition SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Type := list BandSidelinkEUTRA_r16__Type.

Lemma SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__helper1 : (0 <= 1 <= maxBandsEUTRA)%Z. unfold maxBandsEUTRA.
 lia. Qed.
Lemma SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__helper2 : to_bit_sz (Z.to_nat (maxBandsEUTRA - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBandsEUTRA - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__cond (z : SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBandsEUTRA)%Z /\ (list_and BandSidelinkEUTRA_r16__cond z) .

Record SidelinkParametersEUTRA_r16__Type : Set :=
  make__SidelinkParametersEUTRA_r16__Type {
    SidelinkParametersEUTRA_r16__sl_ParametersEUTRA1_r16 : option octet_string ;
    SidelinkParametersEUTRA_r16__sl_ParametersEUTRA2_r16 : option octet_string ;
    SidelinkParametersEUTRA_r16__sl_ParametersEUTRA3_r16 : option octet_string ;
    SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16 : option SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Type ;
}.
Definition SidelinkParametersEUTRA_r16__root_list : list seq_elem := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Type SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__cond ::
 nil).
Definition SidelinkParametersEUTRA_r16__ext_list : list typ := (
  nil).
Definition SidelinkParametersEUTRA_r16__cond (z : SidelinkParametersEUTRA_r16__Type) := 
(  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SidelinkParametersEUTRA_r16__sl_ParametersEUTRA1_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SidelinkParametersEUTRA_r16__sl_ParametersEUTRA2_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SidelinkParametersEUTRA_r16__sl_ParametersEUTRA3_r16 z) /\
  opt_cond SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__cond (SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16 z) /\
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
Definition SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Format : T_Format SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Type SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__cond := seq_of_format BandSidelinkEUTRA_r16__Format 1 maxBandsEUTRA SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__helper1 SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__helper2.

Opaque SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__cond SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Format.


Definition SidelinkParametersEUTRA_r16__root_Format_Type := Eval cbn in seq_format_prod SidelinkParametersEUTRA_r16__root_list.
Definition SidelinkParametersEUTRA_r16__root_Format_list : SidelinkParametersEUTRA_r16__root_Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, (SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16__Format, unit_format)))).

Definition SidelinkParametersEUTRA_r16__ext_Format_Type := Eval cbn in get_formats SidelinkParametersEUTRA_r16__ext_list.
Definition SidelinkParametersEUTRA_r16__ext_Format_list : SidelinkParametersEUTRA_r16__ext_Format_Type :=
  unit__Format.

Definition SidelinkParametersEUTRA_r16__list_type : Set := (seq_type SidelinkParametersEUTRA_r16__root_list) * (seq_ext_type SidelinkParametersEUTRA_r16__ext_list).
Definition SidelinkParametersEUTRA_r16__list_cond (z : SidelinkParametersEUTRA_r16__list_type) : Prop :=
        (seq_cond SidelinkParametersEUTRA_r16__root_list (fst z)) /\ (seq_ext_cond SidelinkParametersEUTRA_r16__ext_list (snd z)).
Definition SidelinkParametersEUTRA_r16__list_format : T_Format SidelinkParametersEUTRA_r16__list_type SidelinkParametersEUTRA_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SidelinkParametersEUTRA_r16__root_list SidelinkParametersEUTRA_r16__root_Format_list SidelinkParametersEUTRA_r16__ext_list SidelinkParametersEUTRA_r16__ext_Format_list.

Opaque SidelinkParametersEUTRA_r16__list_format.
Definition SidelinkParametersEUTRA_r16__F1 (z : SidelinkParametersEUTRA_r16__Type) : SidelinkParametersEUTRA_r16__list_type :=
  (((SidelinkParametersEUTRA_r16__sl_ParametersEUTRA1_r16 z, (SidelinkParametersEUTRA_r16__sl_ParametersEUTRA2_r16 z, (SidelinkParametersEUTRA_r16__sl_ParametersEUTRA3_r16 z, (SidelinkParametersEUTRA_r16__supportedBandListSidelinkEUTRA_r16 z, tt))))), (
tt)).
Definition SidelinkParametersEUTRA_r16__F2 (y : SidelinkParametersEUTRA_r16__list_type) : SidelinkParametersEUTRA_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SidelinkParametersEUTRA_r16__Type j0 j1 j2 j3
  end.
Definition SidelinkParametersEUTRA_r16__helper1 : (forall a : SidelinkParametersEUTRA_r16__Type, SidelinkParametersEUTRA_r16__cond a -> SidelinkParametersEUTRA_r16__list_cond (SidelinkParametersEUTRA_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SidelinkParametersEUTRA_r16__helper2 : (forall a : SidelinkParametersEUTRA_r16__Type, SidelinkParametersEUTRA_r16__F2 (SidelinkParametersEUTRA_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SidelinkParametersEUTRA_r16__helper3 : (forall b : SidelinkParametersEUTRA_r16__list_type, SidelinkParametersEUTRA_r16__list_cond b -> SidelinkParametersEUTRA_r16__cond (SidelinkParametersEUTRA_r16__F2 b) /\ SidelinkParametersEUTRA_r16__F1 (SidelinkParametersEUTRA_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SidelinkParametersEUTRA_r16__cond, SidelinkParametersEUTRA_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SidelinkParametersEUTRA_r16__Format : T_Format SidelinkParametersEUTRA_r16__Type SidelinkParametersEUTRA_r16__cond :=
 proj2_format SidelinkParametersEUTRA_r16__cond SidelinkParametersEUTRA_r16__list_format  SidelinkParametersEUTRA_r16__F1 SidelinkParametersEUTRA_r16__F2 SidelinkParametersEUTRA_r16__helper1 SidelinkParametersEUTRA_r16__helper2 SidelinkParametersEUTRA_r16__helper3.

Opaque SidelinkParametersEUTRA_r16__cond SidelinkParametersEUTRA_r16__Format.

