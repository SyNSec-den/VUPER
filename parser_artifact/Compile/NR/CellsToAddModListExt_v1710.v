Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CellsToAddModExt_v1710.

Opaque CellsToAddModExt_v1710__cond CellsToAddModExt_v1710__Format.

Definition CellsToAddModListExt_v1710__Type := list CellsToAddModExt_v1710__Type.

Lemma CellsToAddModListExt_v1710__helper1 : (0 <= 1 <= maxNrofCellMeas)%Z. unfold maxNrofCellMeas.
 lia. Qed.
Lemma CellsToAddModListExt_v1710__helper2 : to_bit_sz (Z.to_nat (maxNrofCellMeas - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCellMeas - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellsToAddModListExt_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellsToAddModListExt_v1710__cond (z : CellsToAddModListExt_v1710__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCellMeas)%Z /\ (list_and CellsToAddModExt_v1710__cond z) .


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
Definition CellsToAddModListExt_v1710__Format : T_Format CellsToAddModListExt_v1710__Type CellsToAddModListExt_v1710__cond := seq_of_format CellsToAddModExt_v1710__Format 1 maxNrofCellMeas CellsToAddModListExt_v1710__helper1 CellsToAddModListExt_v1710__helper2.

Opaque CellsToAddModListExt_v1710__cond CellsToAddModListExt_v1710__Format.

