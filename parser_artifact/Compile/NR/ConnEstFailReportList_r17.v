Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ConnEstFailReport_r16.

Opaque ConnEstFailReport_r16__cond ConnEstFailReport_r16__Format.

Definition ConnEstFailReportList_r17__Type := list ConnEstFailReport_r16__Type.

Lemma ConnEstFailReportList_r17__helper1 : (0 <= 1 <= maxCEFReport_r17)%Z. unfold maxCEFReport_r17.
 lia. Qed.
Lemma ConnEstFailReportList_r17__helper2 : to_bit_sz (Z.to_nat (maxCEFReport_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCEFReport_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConnEstFailReportList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConnEstFailReportList_r17__cond (z : ConnEstFailReportList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxCEFReport_r17)%Z /\ (list_and ConnEstFailReport_r16__cond z) .


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
Definition ConnEstFailReportList_r17__Format : T_Format ConnEstFailReportList_r17__Type ConnEstFailReportList_r17__cond := seq_of_format ConnEstFailReport_r16__Format 1 maxCEFReport_r17 ConnEstFailReportList_r17__helper1 ConnEstFailReportList_r17__helper2.

Opaque ConnEstFailReportList_r17__cond ConnEstFailReportList_r17__Format.

