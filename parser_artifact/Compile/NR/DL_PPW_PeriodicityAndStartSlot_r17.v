Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__cond := (fun z => (0 <= z <= 3)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__cond := (fun z => (0 <= z <= 4)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__cond := (fun z => (0 <= z <= 7)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__cond := (fun z => (0 <= z <= 10239)%Z).

Inductive DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type : Set :=
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type
.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list : list typ := (
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__cond ::
 nil).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type) := 
  match c with
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__cond t 
  end.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__len_helper1 : to_bit_sz (length DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__len_helper2 : 2 <= length2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list.
 simpl. lia. Qed.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Type : Set := Empty_set.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Type) := True.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Type : Set := DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type + DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Type.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__cond :=
  sum_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__cond.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__cond := (fun z => (0 <= z <= 7)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__cond := (fun z => (0 <= z <= 20479)%Z).

Inductive DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type : Set :=
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type
.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list : list typ := (
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__cond ::
 nil).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type) := 
  match c with
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__cond t 
  end.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__len_helper1 : to_bit_sz (length DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__len_helper2 : 2 <= length2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list.
 simpl. lia. Qed.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Type : Set := Empty_set.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Type) := True.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Type : Set := DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type + DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Type.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__cond :=
  sum_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__cond.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__cond := (fun z => (0 <= z <= 255)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__cond := (fun z => (0 <= z <= 20479)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__helper1 : (0 <= 40959)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__helper2 : to_bit_sz (Z.to_nat (40959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__cond := (fun z => (0 <= z <= 40959)%Z).

Inductive DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type : Set :=
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type
.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list : list typ := (
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__cond ::
 nil).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type) := 
  match c with
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__cond t 
  end.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__len_helper1 : to_bit_sz (length DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__len_helper2 : 2 <= length2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list.
 simpl. lia. Qed.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Type : Set := Empty_set.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Type) := True.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Type : Set := DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type + DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Type.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__cond :=
  sum_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__cond.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__cond := (fun z => (0 <= z <= 255)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__helper1 : (0 <= 511)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__helper2 : to_bit_sz (Z.to_nat (511 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (511 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__cond := (fun z => (0 <= z <= 511)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__cond := (fun z => (0 <= z <= 20479)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__helper1 : (0 <= 40959)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__helper2 : to_bit_sz (Z.to_nat (40959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__cond := (fun z => (0 <= z <= 40959)%Z).
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__helper1 : (0 <= 81919)%Z.  lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__helper2 : to_bit_sz (Z.to_nat (81919 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (81919 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__Type := Z.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__cond := (fun z => (0 <= z <= 81919)%Z).

Inductive DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type : Set :=
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920 : Z -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type
.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list : list typ := (
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__cond ::
typ_cons Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__cond ::
 nil).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type) := 
  match c with
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__cond t 
  end.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__len_helper1 : to_bit_sz (length DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__len_helper2 : 2 <= length2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list.
 simpl. lia. Qed.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Type : Set := Empty_set.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Type) := True.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Type : Set := DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type + DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Type.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__cond :=
  sum_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__cond.

Inductive DL_PPW_PeriodicityAndStartSlot_r17__root__Type : Set :=
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15 : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Type -> DL_PPW_PeriodicityAndStartSlot_r17__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30 : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Type -> DL_PPW_PeriodicityAndStartSlot_r17__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60 : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Type -> DL_PPW_PeriodicityAndStartSlot_r17__root__Type
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120 : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Type -> DL_PPW_PeriodicityAndStartSlot_r17__root__Type
.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__list : list typ := (
typ_cons DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__cond ::
typ_cons DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__cond ::
typ_cons DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__cond ::
typ_cons DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__cond ::
 nil).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__root__Type) := 
  match c with
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__cond t 
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120 t => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__cond t 
  end.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__len_helper1 : to_bit_sz (length DL_PPW_PeriodicityAndStartSlot_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__len_helper2 : 2 <= length2 DL_PPW_PeriodicityAndStartSlot_r17__root__list.
 simpl. lia. Qed.

Definition DL_PPW_PeriodicityAndStartSlot_r17__ext__Type : Set := Empty_set.
Definition DL_PPW_PeriodicityAndStartSlot_r17__ext__cond (c : DL_PPW_PeriodicityAndStartSlot_r17__ext__Type) := True.
Definition DL_PPW_PeriodicityAndStartSlot_r17__Type : Set := DL_PPW_PeriodicityAndStartSlot_r17__root__Type + DL_PPW_PeriodicityAndStartSlot_r17__ext__Type.
Definition DL_PPW_PeriodicityAndStartSlot_r17__cond :=
  sum_cond DL_PPW_PeriodicityAndStartSlot_r17__root__cond DL_PPW_PeriodicityAndStartSlot_r17__ext__cond.

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
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__cond :=
 ranged_int_format (0) (3) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__cond :=
 ranged_int_format (0) (4) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__cond :=
 ranged_int_format (0) (7) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__cond :=
 ranged_int_format (0) (9) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__cond :=
 ranged_int_format (0) (15) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__cond :=
 ranged_int_format (0) (19) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__cond :=
 ranged_int_format (0) (31) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__cond :=
 ranged_int_format (0) (39) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__cond :=
 ranged_int_format (0) (63) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__cond :=
 ranged_int_format (0) (79) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__cond :=
 ranged_int_format (0) (159) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__cond :=
 ranged_int_format (0) (319) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__cond :=
 ranged_int_format (0) (639) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__cond :=
 ranged_int_format (0) (1279) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__cond :=
 ranged_int_format (0) (2559) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__cond :=
 ranged_int_format (0) (5119) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__cond :=
 ranged_int_format (0) (10239) DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__Format.


Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format_Type := Eval cbn in get_formats DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format_list : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format_Type :=
  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240__Format, unit__Format))))))))))))))))).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list__Format := Eval compute in choice_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__len_helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__len_helper2  DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format_list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F1 (z : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type) : (choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list) :=
  match z with
   | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4 t => existT _ 0 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5 t => existT _ 1 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8 t => existT _ 2 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10 t => existT _ 3 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16 t => existT _ 4 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20 t => existT _ 5 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32 t => existT _ 6 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40 t => existT _ 7 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64 t => existT _ 8 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80 t => existT _ 9 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160 t => existT _ 10 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320 t => existT _ 11 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640 t => existT _ 12 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280 t => existT _ 13 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560 t => existT _ 14 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120 t => existT _ 15 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240 t => existT _ 16 t
  end.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__g := (fun n => typ_set (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list n)).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F2 (y : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list) : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__g n -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type) with
    | 0 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n4 t 
    | 1 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5 t 
    | 2 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n8 t 
    | 3 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10 t 
    | 4 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n16 t 
    | 5 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n20 t 
    | 6 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n32 t 
    | 7 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n40 t 
    | 8 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n64 t 
    | 9 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n80 t 
    | 10 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n160 t 
    | 11 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n320 t 
    | 12 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n640 t 
    | 13 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n1280 t 
    | 14 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n2560 t 
    | 15 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n5120 t 
    | 16 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__n10240 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type with end) n0
           end t0).

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__helper2 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond y -> choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__helper3 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F2 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__helper4 : (forall b : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list, choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list b -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F2 b) /\ DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F1 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F2.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond :=
  (* Eval compute in *) proj2_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__list__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__F2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__helper2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__helper3 DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__helper4.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__cond := empty_format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__cond := sum_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__root__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__ext__Format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__cond :=
 ranged_int_format (0) (7) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__cond :=
 ranged_int_format (0) (9) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__cond :=
 ranged_int_format (0) (15) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__cond :=
 ranged_int_format (0) (19) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__cond :=
 ranged_int_format (0) (31) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__cond :=
 ranged_int_format (0) (39) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__cond :=
 ranged_int_format (0) (63) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__cond :=
 ranged_int_format (0) (79) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__cond :=
 ranged_int_format (0) (127) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__cond :=
 ranged_int_format (0) (159) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__cond :=
 ranged_int_format (0) (319) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__cond :=
 ranged_int_format (0) (639) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__cond :=
 ranged_int_format (0) (1279) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__cond :=
 ranged_int_format (0) (2559) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__cond :=
 ranged_int_format (0) (5119) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__cond :=
 ranged_int_format (0) (10239) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__cond :=
 ranged_int_format (0) (20479) DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__Format.


Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format_Type := Eval cbn in get_formats DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format_list : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format_Type :=
  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480__Format, unit__Format))))))))))))))))).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list__Format := Eval compute in choice_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__len_helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__len_helper2  DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format_list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F1 (z : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type) : (choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list) :=
  match z with
   | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8 t => existT _ 0 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10 t => existT _ 1 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16 t => existT _ 2 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20 t => existT _ 3 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32 t => existT _ 4 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40 t => existT _ 5 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64 t => existT _ 6 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80 t => existT _ 7 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128 t => existT _ 8 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160 t => existT _ 9 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320 t => existT _ 10 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640 t => existT _ 11 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280 t => existT _ 12 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560 t => existT _ 13 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120 t => existT _ 14 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240 t => existT _ 15 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480 t => existT _ 16 t
  end.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__g := (fun n => typ_set (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list n)).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F2 (y : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list) : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__g n -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type) with
    | 0 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n8 t 
    | 1 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10 t 
    | 2 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n16 t 
    | 3 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20 t 
    | 4 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n32 t 
    | 5 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n40 t 
    | 6 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n64 t 
    | 7 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n80 t 
    | 8 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n128 t 
    | 9 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n160 t 
    | 10 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n320 t 
    | 11 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n640 t 
    | 12 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n1280 t 
    | 13 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n2560 t 
    | 14 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n5120 t 
    | 15 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n10240 t 
    | 16 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__n20480 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type with end) n0
           end t0).

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__helper2 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond y -> choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__helper3 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F2 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__helper4 : (forall b : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list, choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list b -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F2 b) /\ DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F1 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F2.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond :=
  (* Eval compute in *) proj2_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__list__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__F2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__helper2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__helper3 DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__helper4.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__cond := empty_format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__cond := sum_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__root__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__ext__Format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__cond :=
 ranged_int_format (0) (15) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__cond :=
 ranged_int_format (0) (19) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__cond :=
 ranged_int_format (0) (31) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__cond :=
 ranged_int_format (0) (39) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__cond :=
 ranged_int_format (0) (63) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__cond :=
 ranged_int_format (0) (79) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__cond :=
 ranged_int_format (0) (127) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__cond :=
 ranged_int_format (0) (159) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__cond :=
 ranged_int_format (0) (255) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__cond :=
 ranged_int_format (0) (319) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__cond :=
 ranged_int_format (0) (639) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__cond :=
 ranged_int_format (0) (1279) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__cond :=
 ranged_int_format (0) (2559) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__cond :=
 ranged_int_format (0) (5119) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__cond :=
 ranged_int_format (0) (10239) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__cond :=
 ranged_int_format (0) (20479) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__cond :=
 ranged_int_format (0) (40959) DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__Format.


Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format_Type := Eval cbn in get_formats DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format_list : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format_Type :=
  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960__Format, unit__Format))))))))))))))))).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list__Format := Eval compute in choice_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__len_helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__len_helper2  DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format_list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F1 (z : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type) : (choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list) :=
  match z with
   | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16 t => existT _ 0 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20 t => existT _ 1 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32 t => existT _ 2 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40 t => existT _ 3 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64 t => existT _ 4 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80 t => existT _ 5 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128 t => existT _ 6 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160 t => existT _ 7 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256 t => existT _ 8 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320 t => existT _ 9 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640 t => existT _ 10 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280 t => existT _ 11 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560 t => existT _ 12 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120 t => existT _ 13 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240 t => existT _ 14 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480 t => existT _ 15 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960 t => existT _ 16 t
  end.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__g := (fun n => typ_set (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list n)).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F2 (y : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list) : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__g n -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type) with
    | 0 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n16 t 
    | 1 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20 t 
    | 2 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n32 t 
    | 3 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40 t 
    | 4 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n64 t 
    | 5 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n80 t 
    | 6 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n128 t 
    | 7 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n160 t 
    | 8 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n256 t 
    | 9 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n320 t 
    | 10 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n640 t 
    | 11 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n1280 t 
    | 12 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n2560 t 
    | 13 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n5120 t 
    | 14 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n10240 t 
    | 15 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n20480 t 
    | 16 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__n40960 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type with end) n0
           end t0).

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__helper2 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond y -> choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__helper3 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F2 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__helper4 : (forall b : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list, choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list b -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F2 b) /\ DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F1 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F2.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond :=
  (* Eval compute in *) proj2_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__list__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__F2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__helper2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__helper3 DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__helper4.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__cond := empty_format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__cond := sum_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__root__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__ext__Format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__cond :=
 ranged_int_format (0) (31) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__cond :=
 ranged_int_format (0) (39) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__cond :=
 ranged_int_format (0) (63) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__cond :=
 ranged_int_format (0) (79) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__cond :=
 ranged_int_format (0) (127) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__cond :=
 ranged_int_format (0) (159) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__cond :=
 ranged_int_format (0) (255) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__cond :=
 ranged_int_format (0) (319) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__cond :=
 ranged_int_format (0) (511) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__cond :=
 ranged_int_format (0) (639) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__cond :=
 ranged_int_format (0) (1279) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__cond :=
 ranged_int_format (0) (2559) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__cond :=
 ranged_int_format (0) (5119) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__cond :=
 ranged_int_format (0) (10239) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__cond :=
 ranged_int_format (0) (20479) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__cond :=
 ranged_int_format (0) (40959) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__Format : T_Format Z DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__cond :=
 ranged_int_format (0) (81919) DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__helper2.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__Format.


Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format_Type := Eval cbn in get_formats DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format_list : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format_Type :=
  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920__Format, unit__Format))))))))))))))))).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list__Format := Eval compute in choice_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__len_helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__len_helper2  DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format_list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F1 (z : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type) : (choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list) :=
  match z with
   | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32 t => existT _ 0 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40 t => existT _ 1 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64 t => existT _ 2 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80 t => existT _ 3 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128 t => existT _ 4 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160 t => existT _ 5 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256 t => existT _ 6 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320 t => existT _ 7 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512 t => existT _ 8 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640 t => existT _ 9 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280 t => existT _ 10 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560 t => existT _ 11 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120 t => existT _ 12 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240 t => existT _ 13 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480 t => existT _ 14 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960 t => existT _ 15 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920 t => existT _ 16 t
  end.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__g := (fun n => typ_set (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list n)).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F2 (y : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list) : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__g n -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type) with
    | 0 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n32 t 
    | 1 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40 t 
    | 2 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n64 t 
    | 3 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n80 t 
    | 4 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n128 t 
    | 5 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n160 t 
    | 6 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n256 t 
    | 7 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n320 t 
    | 8 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n512 t 
    | 9 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n640 t 
    | 10 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n1280 t 
    | 11 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n2560 t 
    | 12 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n5120 t 
    | 13 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n10240 t 
    | 14 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n20480 t 
    | 15 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n40960 t 
    | 16 => fun (t : Z) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__n81920 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type with end) n0
           end t0).

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__helper2 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond y -> choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__helper3 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F2 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__helper4 : (forall b : choice DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list, choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list b -> DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F2 b) /\ DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F1 (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F2.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond :=
  (* Eval compute in *) proj2_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__list__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__F2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__helper2 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__helper3 DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__helper4.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__cond := empty_format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Type DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__cond := sum_format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__root__Format DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__ext__Format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__cond DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Format.


Definition DL_PPW_PeriodicityAndStartSlot_r17__root__Format_Type := Eval cbn in get_formats DL_PPW_PeriodicityAndStartSlot_r17__root__list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__Format_list : DL_PPW_PeriodicityAndStartSlot_r17__root__Format_Type :=
  (DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Format, (DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Format, unit__Format)))).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__list__Format := Eval compute in choice_format DL_PPW_PeriodicityAndStartSlot_r17__root__list DL_PPW_PeriodicityAndStartSlot_r17__root__len_helper1 DL_PPW_PeriodicityAndStartSlot_r17__root__len_helper2  DL_PPW_PeriodicityAndStartSlot_r17__root__Format_list.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__F1 (z : DL_PPW_PeriodicityAndStartSlot_r17__root__Type) : (choice DL_PPW_PeriodicityAndStartSlot_r17__root__list) :=
  match z with
   | DL_PPW_PeriodicityAndStartSlot_r17__root__scs15 t => existT _ 0 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs30 t => existT _ 1 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs60 t => existT _ 2 t
  | DL_PPW_PeriodicityAndStartSlot_r17__root__scs120 t => existT _ 3 t
  end.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__g := (fun n => typ_set (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__list n)).
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__F2 (y : choice DL_PPW_PeriodicityAndStartSlot_r17__root__list) : DL_PPW_PeriodicityAndStartSlot_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_PPW_PeriodicityAndStartSlot_r17__root__g n -> DL_PPW_PeriodicityAndStartSlot_r17__root__Type) with
    | 0 => fun (t : DL_PPW_PeriodicityAndStartSlot_r17__root__scs15__Type) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs15 t 
    | 1 => fun (t : DL_PPW_PeriodicityAndStartSlot_r17__root__scs30__Type) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs30 t 
    | 2 => fun (t : DL_PPW_PeriodicityAndStartSlot_r17__root__scs60__Type) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs60 t 
    | 3 => fun (t : DL_PPW_PeriodicityAndStartSlot_r17__root__scs120__Type) => DL_PPW_PeriodicityAndStartSlot_r17__root__scs120 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : DL_PPW_PeriodicityAndStartSlot_r17__root__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ DL_PPW_PeriodicityAndStartSlot_r17__root__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_PPW_PeriodicityAndStartSlot_r17__root__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return DL_PPW_PeriodicityAndStartSlot_r17__root__Type with end) n0
           end t0).

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__helper2 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__cond y -> choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__list (DL_PPW_PeriodicityAndStartSlot_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__helper3 :  forall (y : DL_PPW_PeriodicityAndStartSlot_r17__root__Type), DL_PPW_PeriodicityAndStartSlot_r17__root__F2 (DL_PPW_PeriodicityAndStartSlot_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_PPW_PeriodicityAndStartSlot_r17__root__helper4 : (forall b : choice DL_PPW_PeriodicityAndStartSlot_r17__root__list, choice_cond DL_PPW_PeriodicityAndStartSlot_r17__root__list b -> DL_PPW_PeriodicityAndStartSlot_r17__root__cond (DL_PPW_PeriodicityAndStartSlot_r17__root__F2 b) /\ DL_PPW_PeriodicityAndStartSlot_r17__root__F1 (DL_PPW_PeriodicityAndStartSlot_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_PPW_PeriodicityAndStartSlot_r17__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__F2.
Definition DL_PPW_PeriodicityAndStartSlot_r17__root__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__root__Type DL_PPW_PeriodicityAndStartSlot_r17__root__cond :=
  (* Eval compute in *) proj2_format DL_PPW_PeriodicityAndStartSlot_r17__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__list__Format DL_PPW_PeriodicityAndStartSlot_r17__root__F1 DL_PPW_PeriodicityAndStartSlot_r17__root__F2 DL_PPW_PeriodicityAndStartSlot_r17__root__helper2 DL_PPW_PeriodicityAndStartSlot_r17__root__helper3 DL_PPW_PeriodicityAndStartSlot_r17__root__helper4.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__root__cond DL_PPW_PeriodicityAndStartSlot_r17__root__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__ext__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__ext__Type DL_PPW_PeriodicityAndStartSlot_r17__ext__cond := empty_format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__ext__cond DL_PPW_PeriodicityAndStartSlot_r17__ext__Format.

Definition DL_PPW_PeriodicityAndStartSlot_r17__Format : T_Format DL_PPW_PeriodicityAndStartSlot_r17__Type DL_PPW_PeriodicityAndStartSlot_r17__cond := sum_format DL_PPW_PeriodicityAndStartSlot_r17__root__Format DL_PPW_PeriodicityAndStartSlot_r17__ext__Format.
Opaque DL_PPW_PeriodicityAndStartSlot_r17__cond DL_PPW_PeriodicityAndStartSlot_r17__Format.

