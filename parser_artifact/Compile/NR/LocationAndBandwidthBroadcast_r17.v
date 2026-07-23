Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma LocationAndBandwidthBroadcast_r17__locationAndBandwidth__helper1 : (0 <= 37949)%Z.  lia. Qed.
Lemma LocationAndBandwidthBroadcast_r17__locationAndBandwidth__helper2 : to_bit_sz (Z.to_nat (37949 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (37949 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply LocationAndBandwidthBroadcast_r17__locationAndBandwidth__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LocationAndBandwidthBroadcast_r17__locationAndBandwidth__Type := Z.
Definition LocationAndBandwidthBroadcast_r17__locationAndBandwidth__cond := (fun z => (0 <= z <= 37949)%Z).

Inductive LocationAndBandwidthBroadcast_r17__Type : Set :=
  | LocationAndBandwidthBroadcast_r17__sameAsSib1ConfiguredLocationAndBW : unit -> LocationAndBandwidthBroadcast_r17__Type
  | LocationAndBandwidthBroadcast_r17__locationAndBandwidth : Z -> LocationAndBandwidthBroadcast_r17__Type
.
Definition LocationAndBandwidthBroadcast_r17__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons Z LocationAndBandwidthBroadcast_r17__locationAndBandwidth__cond ::
 nil).
Definition LocationAndBandwidthBroadcast_r17__cond (c : LocationAndBandwidthBroadcast_r17__Type) := 
  match c with
  | LocationAndBandwidthBroadcast_r17__sameAsSib1ConfiguredLocationAndBW t => (fun _ => True) t 
  | LocationAndBandwidthBroadcast_r17__locationAndBandwidth t => LocationAndBandwidthBroadcast_r17__locationAndBandwidth__cond t 
  end.

Lemma LocationAndBandwidthBroadcast_r17__len_helper1 : to_bit_sz (length LocationAndBandwidthBroadcast_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma LocationAndBandwidthBroadcast_r17__len_helper2 : 2 <= length2 LocationAndBandwidthBroadcast_r17__list.
 simpl. lia. Qed.

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
Definition LocationAndBandwidthBroadcast_r17__locationAndBandwidth__Format : T_Format Z LocationAndBandwidthBroadcast_r17__locationAndBandwidth__cond :=
 ranged_int_format (0) (37949) LocationAndBandwidthBroadcast_r17__locationAndBandwidth__helper1 LocationAndBandwidthBroadcast_r17__locationAndBandwidth__helper2.

Opaque LocationAndBandwidthBroadcast_r17__locationAndBandwidth__cond LocationAndBandwidthBroadcast_r17__locationAndBandwidth__Format.


Definition LocationAndBandwidthBroadcast_r17__Format_Type := Eval cbn in get_formats LocationAndBandwidthBroadcast_r17__list.
Definition LocationAndBandwidthBroadcast_r17__Format_list : LocationAndBandwidthBroadcast_r17__Format_Type :=
  (unit__Format, (LocationAndBandwidthBroadcast_r17__locationAndBandwidth__Format, unit__Format)).
Definition LocationAndBandwidthBroadcast_r17__list__Format := Eval compute in choice_format LocationAndBandwidthBroadcast_r17__list LocationAndBandwidthBroadcast_r17__len_helper1 LocationAndBandwidthBroadcast_r17__len_helper2  LocationAndBandwidthBroadcast_r17__Format_list.
Definition LocationAndBandwidthBroadcast_r17__F1 (z : LocationAndBandwidthBroadcast_r17__Type) : (choice LocationAndBandwidthBroadcast_r17__list) :=
  match z with
   | LocationAndBandwidthBroadcast_r17__sameAsSib1ConfiguredLocationAndBW t => existT _ 0 t
  | LocationAndBandwidthBroadcast_r17__locationAndBandwidth t => existT _ 1 t
  end.
Definition LocationAndBandwidthBroadcast_r17__g := (fun n => typ_set (get_nth_typ LocationAndBandwidthBroadcast_r17__list n)).
Definition LocationAndBandwidthBroadcast_r17__F2 (y : choice LocationAndBandwidthBroadcast_r17__list) : LocationAndBandwidthBroadcast_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (LocationAndBandwidthBroadcast_r17__g n -> LocationAndBandwidthBroadcast_r17__Type) with
    | 0 => fun (t : unit) => LocationAndBandwidthBroadcast_r17__sameAsSib1ConfiguredLocationAndBW t 
    | 1 => fun (t : Z) => LocationAndBandwidthBroadcast_r17__locationAndBandwidth t 
 | (S (S n0)) => (fun (x' : nat) (t'' : LocationAndBandwidthBroadcast_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ LocationAndBandwidthBroadcast_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len LocationAndBandwidthBroadcast_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return LocationAndBandwidthBroadcast_r17__Type with end) n0
           end t0).

Lemma LocationAndBandwidthBroadcast_r17__helper2 :  forall (y : LocationAndBandwidthBroadcast_r17__Type), LocationAndBandwidthBroadcast_r17__cond y -> choice_cond LocationAndBandwidthBroadcast_r17__list (LocationAndBandwidthBroadcast_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma LocationAndBandwidthBroadcast_r17__helper3 :  forall (y : LocationAndBandwidthBroadcast_r17__Type), LocationAndBandwidthBroadcast_r17__F2 (LocationAndBandwidthBroadcast_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma LocationAndBandwidthBroadcast_r17__helper4 : (forall b : choice LocationAndBandwidthBroadcast_r17__list, choice_cond LocationAndBandwidthBroadcast_r17__list b -> LocationAndBandwidthBroadcast_r17__cond (LocationAndBandwidthBroadcast_r17__F2 b) /\ LocationAndBandwidthBroadcast_r17__F1 (LocationAndBandwidthBroadcast_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length LocationAndBandwidthBroadcast_r17__F1 LocationAndBandwidthBroadcast_r17__F2.
Definition LocationAndBandwidthBroadcast_r17__Format : T_Format LocationAndBandwidthBroadcast_r17__Type LocationAndBandwidthBroadcast_r17__cond :=
  (* Eval compute in *) proj2_format LocationAndBandwidthBroadcast_r17__cond LocationAndBandwidthBroadcast_r17__list__Format LocationAndBandwidthBroadcast_r17__F1 LocationAndBandwidthBroadcast_r17__F2 LocationAndBandwidthBroadcast_r17__helper2 LocationAndBandwidthBroadcast_r17__helper3 LocationAndBandwidthBroadcast_r17__helper4.
Opaque LocationAndBandwidthBroadcast_r17__cond LocationAndBandwidthBroadcast_r17__Format.

