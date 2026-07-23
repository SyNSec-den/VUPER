Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Lemma DRX_Info__drx_LongCycleStartOffset__ms10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms10__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms20__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms32__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms40__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms60__helper1 : (0 <= 59)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms60__helper2 : to_bit_sz (Z.to_nat (59 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (59 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms60__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms60__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms60__cond := (fun z => (0 <= z <= 59)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms64__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms70__helper1 : (0 <= 69)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms70__helper2 : to_bit_sz (Z.to_nat (69 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (69 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms70__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms70__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms70__cond := (fun z => (0 <= z <= 69)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms80__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms128__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms160__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms256__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms256__cond := (fun z => (0 <= z <= 255)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms320__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms512__helper1 : (0 <= 511)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms512__helper2 : to_bit_sz (Z.to_nat (511 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (511 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms512__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms512__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms512__cond := (fun z => (0 <= z <= 511)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms640__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms1024__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms1024__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms1024__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms1024__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms1024__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms1280__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms2048__helper1 : (0 <= 2047)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms2048__helper2 : to_bit_sz (Z.to_nat (2047 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2047 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms2048__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms2048__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms2048__cond := (fun z => (0 <= z <= 2047)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms2560__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms5120__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma DRX_Info__drx_LongCycleStartOffset__ms10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__ms10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__drx_LongCycleStartOffset__ms10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__drx_LongCycleStartOffset__ms10240__Type := Z.
Definition DRX_Info__drx_LongCycleStartOffset__ms10240__cond := (fun z => (0 <= z <= 10239)%Z).

Inductive DRX_Info__drx_LongCycleStartOffset__Type : Set :=
  | DRX_Info__drx_LongCycleStartOffset__ms10 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms20 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms32 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms40 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms60 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms64 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms70 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms80 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms128 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms160 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms256 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms320 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms512 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms640 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms1024 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms1280 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms2048 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms2560 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms5120 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
  | DRX_Info__drx_LongCycleStartOffset__ms10240 : Z -> DRX_Info__drx_LongCycleStartOffset__Type
.
Definition DRX_Info__drx_LongCycleStartOffset__list : list typ := (
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms10__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms20__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms32__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms40__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms60__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms64__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms70__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms80__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms128__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms160__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms256__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms320__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms512__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms640__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms1024__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms1280__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms2048__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms2560__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms5120__cond ::
typ_cons Z DRX_Info__drx_LongCycleStartOffset__ms10240__cond ::
 nil).
Definition DRX_Info__drx_LongCycleStartOffset__cond (c : DRX_Info__drx_LongCycleStartOffset__Type) := 
  match c with
  | DRX_Info__drx_LongCycleStartOffset__ms10 t => DRX_Info__drx_LongCycleStartOffset__ms10__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms20 t => DRX_Info__drx_LongCycleStartOffset__ms20__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms32 t => DRX_Info__drx_LongCycleStartOffset__ms32__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms40 t => DRX_Info__drx_LongCycleStartOffset__ms40__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms60 t => DRX_Info__drx_LongCycleStartOffset__ms60__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms64 t => DRX_Info__drx_LongCycleStartOffset__ms64__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms70 t => DRX_Info__drx_LongCycleStartOffset__ms70__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms80 t => DRX_Info__drx_LongCycleStartOffset__ms80__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms128 t => DRX_Info__drx_LongCycleStartOffset__ms128__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms160 t => DRX_Info__drx_LongCycleStartOffset__ms160__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms256 t => DRX_Info__drx_LongCycleStartOffset__ms256__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms320 t => DRX_Info__drx_LongCycleStartOffset__ms320__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms512 t => DRX_Info__drx_LongCycleStartOffset__ms512__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms640 t => DRX_Info__drx_LongCycleStartOffset__ms640__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms1024 t => DRX_Info__drx_LongCycleStartOffset__ms1024__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms1280 t => DRX_Info__drx_LongCycleStartOffset__ms1280__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms2048 t => DRX_Info__drx_LongCycleStartOffset__ms2048__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms2560 t => DRX_Info__drx_LongCycleStartOffset__ms2560__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms5120 t => DRX_Info__drx_LongCycleStartOffset__ms5120__cond t 
  | DRX_Info__drx_LongCycleStartOffset__ms10240 t => DRX_Info__drx_LongCycleStartOffset__ms10240__cond t 
  end.

Lemma DRX_Info__drx_LongCycleStartOffset__len_helper1 : to_bit_sz (length DRX_Info__drx_LongCycleStartOffset__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DRX_Info__drx_LongCycleStartOffset__len_helper2 : 2 <= length2 DRX_Info__drx_LongCycleStartOffset__list.
 simpl. lia. Qed.
Inductive DRX_Info__shortDRX__drx_ShortCycle__Type : Set :=
 | DRX_Info__shortDRX__drx_ShortCycle__ms2
 | DRX_Info__shortDRX__drx_ShortCycle__ms3
 | DRX_Info__shortDRX__drx_ShortCycle__ms4
 | DRX_Info__shortDRX__drx_ShortCycle__ms5
 | DRX_Info__shortDRX__drx_ShortCycle__ms6
 | DRX_Info__shortDRX__drx_ShortCycle__ms7
 | DRX_Info__shortDRX__drx_ShortCycle__ms8
 | DRX_Info__shortDRX__drx_ShortCycle__ms10
 | DRX_Info__shortDRX__drx_ShortCycle__ms14
 | DRX_Info__shortDRX__drx_ShortCycle__ms16
 | DRX_Info__shortDRX__drx_ShortCycle__ms20
 | DRX_Info__shortDRX__drx_ShortCycle__ms30
 | DRX_Info__shortDRX__drx_ShortCycle__ms32
 | DRX_Info__shortDRX__drx_ShortCycle__ms35
 | DRX_Info__shortDRX__drx_ShortCycle__ms40
 | DRX_Info__shortDRX__drx_ShortCycle__ms64
 | DRX_Info__shortDRX__drx_ShortCycle__ms80
 | DRX_Info__shortDRX__drx_ShortCycle__ms128
 | DRX_Info__shortDRX__drx_ShortCycle__ms160
 | DRX_Info__shortDRX__drx_ShortCycle__ms256
 | DRX_Info__shortDRX__drx_ShortCycle__ms320
 | DRX_Info__shortDRX__drx_ShortCycle__ms512
 | DRX_Info__shortDRX__drx_ShortCycle__ms640
 | DRX_Info__shortDRX__drx_ShortCycle__spare9
 | DRX_Info__shortDRX__drx_ShortCycle__spare8
 | DRX_Info__shortDRX__drx_ShortCycle__spare7
 | DRX_Info__shortDRX__drx_ShortCycle__spare6
 | DRX_Info__shortDRX__drx_ShortCycle__spare5
 | DRX_Info__shortDRX__drx_ShortCycle__spare4
 | DRX_Info__shortDRX__drx_ShortCycle__spare3
 | DRX_Info__shortDRX__drx_ShortCycle__spare2
 | DRX_Info__shortDRX__drx_ShortCycle__spare1
.
Definition DRX_Info__shortDRX__drx_ShortCycle__cond := (fun (_ : DRX_Info__shortDRX__drx_ShortCycle__Type) => True).
Lemma DRX_Info__shortDRX__drx_ShortCycle__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_Info__shortDRX__drx_ShortCycle__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_Info__shortDRX__drx_ShortCycle__nat__helper.

Definition DRX_Info__shortDRX__drx_ShortCycle__F1 t :=
  match t with
  | DRX_Info__shortDRX__drx_ShortCycle__ms2 => 0
  | DRX_Info__shortDRX__drx_ShortCycle__ms3 => 1
  | DRX_Info__shortDRX__drx_ShortCycle__ms4 => 2
  | DRX_Info__shortDRX__drx_ShortCycle__ms5 => 3
  | DRX_Info__shortDRX__drx_ShortCycle__ms6 => 4
  | DRX_Info__shortDRX__drx_ShortCycle__ms7 => 5
  | DRX_Info__shortDRX__drx_ShortCycle__ms8 => 6
  | DRX_Info__shortDRX__drx_ShortCycle__ms10 => 7
  | DRX_Info__shortDRX__drx_ShortCycle__ms14 => 8
  | DRX_Info__shortDRX__drx_ShortCycle__ms16 => 9
  | DRX_Info__shortDRX__drx_ShortCycle__ms20 => 10
  | DRX_Info__shortDRX__drx_ShortCycle__ms30 => 11
  | DRX_Info__shortDRX__drx_ShortCycle__ms32 => 12
  | DRX_Info__shortDRX__drx_ShortCycle__ms35 => 13
  | DRX_Info__shortDRX__drx_ShortCycle__ms40 => 14
  | DRX_Info__shortDRX__drx_ShortCycle__ms64 => 15
  | DRX_Info__shortDRX__drx_ShortCycle__ms80 => 16
  | DRX_Info__shortDRX__drx_ShortCycle__ms128 => 17
  | DRX_Info__shortDRX__drx_ShortCycle__ms160 => 18
  | DRX_Info__shortDRX__drx_ShortCycle__ms256 => 19
  | DRX_Info__shortDRX__drx_ShortCycle__ms320 => 20
  | DRX_Info__shortDRX__drx_ShortCycle__ms512 => 21
  | DRX_Info__shortDRX__drx_ShortCycle__ms640 => 22
  | DRX_Info__shortDRX__drx_ShortCycle__spare9 => 23
  | DRX_Info__shortDRX__drx_ShortCycle__spare8 => 24
  | DRX_Info__shortDRX__drx_ShortCycle__spare7 => 25
  | DRX_Info__shortDRX__drx_ShortCycle__spare6 => 26
  | DRX_Info__shortDRX__drx_ShortCycle__spare5 => 27
  | DRX_Info__shortDRX__drx_ShortCycle__spare4 => 28
  | DRX_Info__shortDRX__drx_ShortCycle__spare3 => 29
  | DRX_Info__shortDRX__drx_ShortCycle__spare2 => 30
  | DRX_Info__shortDRX__drx_ShortCycle__spare1 => 31
  end.
Definition DRX_Info__shortDRX__drx_ShortCycle__F2 n :=
  match n with
  | 0 => DRX_Info__shortDRX__drx_ShortCycle__ms2
  | 1 => DRX_Info__shortDRX__drx_ShortCycle__ms3
  | 2 => DRX_Info__shortDRX__drx_ShortCycle__ms4
  | 3 => DRX_Info__shortDRX__drx_ShortCycle__ms5
  | 4 => DRX_Info__shortDRX__drx_ShortCycle__ms6
  | 5 => DRX_Info__shortDRX__drx_ShortCycle__ms7
  | 6 => DRX_Info__shortDRX__drx_ShortCycle__ms8
  | 7 => DRX_Info__shortDRX__drx_ShortCycle__ms10
  | 8 => DRX_Info__shortDRX__drx_ShortCycle__ms14
  | 9 => DRX_Info__shortDRX__drx_ShortCycle__ms16
  | 10 => DRX_Info__shortDRX__drx_ShortCycle__ms20
  | 11 => DRX_Info__shortDRX__drx_ShortCycle__ms30
  | 12 => DRX_Info__shortDRX__drx_ShortCycle__ms32
  | 13 => DRX_Info__shortDRX__drx_ShortCycle__ms35
  | 14 => DRX_Info__shortDRX__drx_ShortCycle__ms40
  | 15 => DRX_Info__shortDRX__drx_ShortCycle__ms64
  | 16 => DRX_Info__shortDRX__drx_ShortCycle__ms80
  | 17 => DRX_Info__shortDRX__drx_ShortCycle__ms128
  | 18 => DRX_Info__shortDRX__drx_ShortCycle__ms160
  | 19 => DRX_Info__shortDRX__drx_ShortCycle__ms256
  | 20 => DRX_Info__shortDRX__drx_ShortCycle__ms320
  | 21 => DRX_Info__shortDRX__drx_ShortCycle__ms512
  | 22 => DRX_Info__shortDRX__drx_ShortCycle__ms640
  | 23 => DRX_Info__shortDRX__drx_ShortCycle__spare9
  | 24 => DRX_Info__shortDRX__drx_ShortCycle__spare8
  | 25 => DRX_Info__shortDRX__drx_ShortCycle__spare7
  | 26 => DRX_Info__shortDRX__drx_ShortCycle__spare6
  | 27 => DRX_Info__shortDRX__drx_ShortCycle__spare5
  | 28 => DRX_Info__shortDRX__drx_ShortCycle__spare4
  | 29 => DRX_Info__shortDRX__drx_ShortCycle__spare3
  | 30 => DRX_Info__shortDRX__drx_ShortCycle__spare2
  | 31 => DRX_Info__shortDRX__drx_ShortCycle__spare1
  | _ => DRX_Info__shortDRX__drx_ShortCycle__ms2
  end.
Lemma DRX_Info__shortDRX__drx_ShortCycle__F1F2 : forall x : DRX_Info__shortDRX__drx_ShortCycle__Type, (DRX_Info__shortDRX__drx_ShortCycle__F1 x <= 31) /\ DRX_Info__shortDRX__drx_ShortCycle__F2 (DRX_Info__shortDRX__drx_ShortCycle__F1 x) = x. imp_solve. Qed.
Lemma DRX_Info__shortDRX__drx_ShortCycle__F2F1 : forall (y : nat) (H : y <= 31), DRX_Info__shortDRX__drx_ShortCycle__F1 (DRX_Info__shortDRX__drx_ShortCycle__F2 y) = y. enum_solve H y. Qed.

Lemma DRX_Info__shortDRX__drx_ShortCycleTimer__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma DRX_Info__shortDRX__drx_ShortCycleTimer__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Info__shortDRX__drx_ShortCycleTimer__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Info__shortDRX__drx_ShortCycleTimer__Type := Z.
Definition DRX_Info__shortDRX__drx_ShortCycleTimer__cond := (fun z => (1 <= z <= 16)%Z).
Record DRX_Info__shortDRX__Type : Set :=
  make__DRX_Info__shortDRX__Type {
    DRX_Info__shortDRX__drx_ShortCycle : DRX_Info__shortDRX__drx_ShortCycle__Type ;
    DRX_Info__shortDRX__drx_ShortCycleTimer : Z ;
}.
Definition DRX_Info__shortDRX__list := (
 Nor DRX_Info__shortDRX__drx_ShortCycle__Type DRX_Info__shortDRX__drx_ShortCycle__cond ::
 Nor Z DRX_Info__shortDRX__drx_ShortCycleTimer__cond ::
 nil).
Definition DRX_Info__shortDRX__cond z := 
  DRX_Info__shortDRX__drx_ShortCycle__cond (DRX_Info__shortDRX__drx_ShortCycle z) /\
  DRX_Info__shortDRX__drx_ShortCycleTimer__cond (DRX_Info__shortDRX__drx_ShortCycleTimer z) /\
  True.

Record DRX_Info__Type : Set :=
  make__DRX_Info__Type {
    DRX_Info__drx_LongCycleStartOffset : DRX_Info__drx_LongCycleStartOffset__Type ;
    DRX_Info__shortDRX : option DRX_Info__shortDRX__Type ;
}.
Definition DRX_Info__list := (
 Nor DRX_Info__drx_LongCycleStartOffset__Type DRX_Info__drx_LongCycleStartOffset__cond ::
 Opt DRX_Info__shortDRX__Type DRX_Info__shortDRX__cond ::
 nil).
Definition DRX_Info__cond z := 
  DRX_Info__drx_LongCycleStartOffset__cond (DRX_Info__drx_LongCycleStartOffset z) /\
  opt_cond DRX_Info__shortDRX__cond (DRX_Info__shortDRX z) /\
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
Definition DRX_Info__drx_LongCycleStartOffset__ms10__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms10__cond :=
 ranged_int_format (0) (9) DRX_Info__drx_LongCycleStartOffset__ms10__helper1 DRX_Info__drx_LongCycleStartOffset__ms10__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms10__cond DRX_Info__drx_LongCycleStartOffset__ms10__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms20__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms20__cond :=
 ranged_int_format (0) (19) DRX_Info__drx_LongCycleStartOffset__ms20__helper1 DRX_Info__drx_LongCycleStartOffset__ms20__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms20__cond DRX_Info__drx_LongCycleStartOffset__ms20__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms32__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms32__cond :=
 ranged_int_format (0) (31) DRX_Info__drx_LongCycleStartOffset__ms32__helper1 DRX_Info__drx_LongCycleStartOffset__ms32__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms32__cond DRX_Info__drx_LongCycleStartOffset__ms32__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms40__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms40__cond :=
 ranged_int_format (0) (39) DRX_Info__drx_LongCycleStartOffset__ms40__helper1 DRX_Info__drx_LongCycleStartOffset__ms40__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms40__cond DRX_Info__drx_LongCycleStartOffset__ms40__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms60__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms60__cond :=
 ranged_int_format (0) (59) DRX_Info__drx_LongCycleStartOffset__ms60__helper1 DRX_Info__drx_LongCycleStartOffset__ms60__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms60__cond DRX_Info__drx_LongCycleStartOffset__ms60__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms64__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms64__cond :=
 ranged_int_format (0) (63) DRX_Info__drx_LongCycleStartOffset__ms64__helper1 DRX_Info__drx_LongCycleStartOffset__ms64__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms64__cond DRX_Info__drx_LongCycleStartOffset__ms64__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms70__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms70__cond :=
 ranged_int_format (0) (69) DRX_Info__drx_LongCycleStartOffset__ms70__helper1 DRX_Info__drx_LongCycleStartOffset__ms70__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms70__cond DRX_Info__drx_LongCycleStartOffset__ms70__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms80__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms80__cond :=
 ranged_int_format (0) (79) DRX_Info__drx_LongCycleStartOffset__ms80__helper1 DRX_Info__drx_LongCycleStartOffset__ms80__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms80__cond DRX_Info__drx_LongCycleStartOffset__ms80__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms128__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms128__cond :=
 ranged_int_format (0) (127) DRX_Info__drx_LongCycleStartOffset__ms128__helper1 DRX_Info__drx_LongCycleStartOffset__ms128__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms128__cond DRX_Info__drx_LongCycleStartOffset__ms128__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms160__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms160__cond :=
 ranged_int_format (0) (159) DRX_Info__drx_LongCycleStartOffset__ms160__helper1 DRX_Info__drx_LongCycleStartOffset__ms160__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms160__cond DRX_Info__drx_LongCycleStartOffset__ms160__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms256__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms256__cond :=
 ranged_int_format (0) (255) DRX_Info__drx_LongCycleStartOffset__ms256__helper1 DRX_Info__drx_LongCycleStartOffset__ms256__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms256__cond DRX_Info__drx_LongCycleStartOffset__ms256__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms320__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms320__cond :=
 ranged_int_format (0) (319) DRX_Info__drx_LongCycleStartOffset__ms320__helper1 DRX_Info__drx_LongCycleStartOffset__ms320__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms320__cond DRX_Info__drx_LongCycleStartOffset__ms320__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms512__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms512__cond :=
 ranged_int_format (0) (511) DRX_Info__drx_LongCycleStartOffset__ms512__helper1 DRX_Info__drx_LongCycleStartOffset__ms512__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms512__cond DRX_Info__drx_LongCycleStartOffset__ms512__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms640__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms640__cond :=
 ranged_int_format (0) (639) DRX_Info__drx_LongCycleStartOffset__ms640__helper1 DRX_Info__drx_LongCycleStartOffset__ms640__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms640__cond DRX_Info__drx_LongCycleStartOffset__ms640__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms1024__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms1024__cond :=
 ranged_int_format (0) (1023) DRX_Info__drx_LongCycleStartOffset__ms1024__helper1 DRX_Info__drx_LongCycleStartOffset__ms1024__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms1024__cond DRX_Info__drx_LongCycleStartOffset__ms1024__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms1280__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms1280__cond :=
 ranged_int_format (0) (1279) DRX_Info__drx_LongCycleStartOffset__ms1280__helper1 DRX_Info__drx_LongCycleStartOffset__ms1280__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms1280__cond DRX_Info__drx_LongCycleStartOffset__ms1280__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms2048__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms2048__cond :=
 ranged_int_format (0) (2047) DRX_Info__drx_LongCycleStartOffset__ms2048__helper1 DRX_Info__drx_LongCycleStartOffset__ms2048__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms2048__cond DRX_Info__drx_LongCycleStartOffset__ms2048__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms2560__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms2560__cond :=
 ranged_int_format (0) (2559) DRX_Info__drx_LongCycleStartOffset__ms2560__helper1 DRX_Info__drx_LongCycleStartOffset__ms2560__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms2560__cond DRX_Info__drx_LongCycleStartOffset__ms2560__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms5120__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms5120__cond :=
 ranged_int_format (0) (5119) DRX_Info__drx_LongCycleStartOffset__ms5120__helper1 DRX_Info__drx_LongCycleStartOffset__ms5120__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms5120__cond DRX_Info__drx_LongCycleStartOffset__ms5120__Format.

Definition DRX_Info__drx_LongCycleStartOffset__ms10240__Format : T_Format Z DRX_Info__drx_LongCycleStartOffset__ms10240__cond :=
 ranged_int_format (0) (10239) DRX_Info__drx_LongCycleStartOffset__ms10240__helper1 DRX_Info__drx_LongCycleStartOffset__ms10240__helper2.

Opaque DRX_Info__drx_LongCycleStartOffset__ms10240__cond DRX_Info__drx_LongCycleStartOffset__ms10240__Format.


Definition DRX_Info__drx_LongCycleStartOffset__Format_Type := Eval cbn in get_formats DRX_Info__drx_LongCycleStartOffset__list.
Definition DRX_Info__drx_LongCycleStartOffset__Format_list : DRX_Info__drx_LongCycleStartOffset__Format_Type :=
  (DRX_Info__drx_LongCycleStartOffset__ms10__Format, (DRX_Info__drx_LongCycleStartOffset__ms20__Format, (DRX_Info__drx_LongCycleStartOffset__ms32__Format, (DRX_Info__drx_LongCycleStartOffset__ms40__Format, (DRX_Info__drx_LongCycleStartOffset__ms60__Format, (DRX_Info__drx_LongCycleStartOffset__ms64__Format, (DRX_Info__drx_LongCycleStartOffset__ms70__Format, (DRX_Info__drx_LongCycleStartOffset__ms80__Format, (DRX_Info__drx_LongCycleStartOffset__ms128__Format, (DRX_Info__drx_LongCycleStartOffset__ms160__Format, (DRX_Info__drx_LongCycleStartOffset__ms256__Format, (DRX_Info__drx_LongCycleStartOffset__ms320__Format, (DRX_Info__drx_LongCycleStartOffset__ms512__Format, (DRX_Info__drx_LongCycleStartOffset__ms640__Format, (DRX_Info__drx_LongCycleStartOffset__ms1024__Format, (DRX_Info__drx_LongCycleStartOffset__ms1280__Format, (DRX_Info__drx_LongCycleStartOffset__ms2048__Format, (DRX_Info__drx_LongCycleStartOffset__ms2560__Format, (DRX_Info__drx_LongCycleStartOffset__ms5120__Format, (DRX_Info__drx_LongCycleStartOffset__ms10240__Format, unit__Format)))))))))))))))))))).
Definition DRX_Info__drx_LongCycleStartOffset__list__Format := Eval compute in choice_format DRX_Info__drx_LongCycleStartOffset__list DRX_Info__drx_LongCycleStartOffset__len_helper1 DRX_Info__drx_LongCycleStartOffset__len_helper2  DRX_Info__drx_LongCycleStartOffset__Format_list.
Definition DRX_Info__drx_LongCycleStartOffset__F1 (z : DRX_Info__drx_LongCycleStartOffset__Type) : (choice DRX_Info__drx_LongCycleStartOffset__list) :=
  match z with
   | DRX_Info__drx_LongCycleStartOffset__ms10 t => existT _ 0 t
  | DRX_Info__drx_LongCycleStartOffset__ms20 t => existT _ 1 t
  | DRX_Info__drx_LongCycleStartOffset__ms32 t => existT _ 2 t
  | DRX_Info__drx_LongCycleStartOffset__ms40 t => existT _ 3 t
  | DRX_Info__drx_LongCycleStartOffset__ms60 t => existT _ 4 t
  | DRX_Info__drx_LongCycleStartOffset__ms64 t => existT _ 5 t
  | DRX_Info__drx_LongCycleStartOffset__ms70 t => existT _ 6 t
  | DRX_Info__drx_LongCycleStartOffset__ms80 t => existT _ 7 t
  | DRX_Info__drx_LongCycleStartOffset__ms128 t => existT _ 8 t
  | DRX_Info__drx_LongCycleStartOffset__ms160 t => existT _ 9 t
  | DRX_Info__drx_LongCycleStartOffset__ms256 t => existT _ 10 t
  | DRX_Info__drx_LongCycleStartOffset__ms320 t => existT _ 11 t
  | DRX_Info__drx_LongCycleStartOffset__ms512 t => existT _ 12 t
  | DRX_Info__drx_LongCycleStartOffset__ms640 t => existT _ 13 t
  | DRX_Info__drx_LongCycleStartOffset__ms1024 t => existT _ 14 t
  | DRX_Info__drx_LongCycleStartOffset__ms1280 t => existT _ 15 t
  | DRX_Info__drx_LongCycleStartOffset__ms2048 t => existT _ 16 t
  | DRX_Info__drx_LongCycleStartOffset__ms2560 t => existT _ 17 t
  | DRX_Info__drx_LongCycleStartOffset__ms5120 t => existT _ 18 t
  | DRX_Info__drx_LongCycleStartOffset__ms10240 t => existT _ 19 t
  end.
Definition DRX_Info__drx_LongCycleStartOffset__g := (fun n => typ_set (get_nth_typ DRX_Info__drx_LongCycleStartOffset__list n)).
Definition DRX_Info__drx_LongCycleStartOffset__F2 (y : choice DRX_Info__drx_LongCycleStartOffset__list) : DRX_Info__drx_LongCycleStartOffset__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DRX_Info__drx_LongCycleStartOffset__g n -> DRX_Info__drx_LongCycleStartOffset__Type) with
    | 0 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms10 t 
    | 1 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms20 t 
    | 2 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms32 t 
    | 3 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms40 t 
    | 4 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms60 t 
    | 5 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms64 t 
    | 6 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms70 t 
    | 7 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms80 t 
    | 8 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms128 t 
    | 9 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms160 t 
    | 10 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms256 t 
    | 11 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms320 t 
    | 12 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms512 t 
    | 13 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms640 t 
    | 14 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms1024 t 
    | 15 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms1280 t 
    | 16 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms2048 t 
    | 17 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms2560 t 
    | 18 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms5120 t 
    | 19 => fun (t : Z) => DRX_Info__drx_LongCycleStartOffset__ms10240 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))))))) => (fun (x' : nat) (t'' : DRX_Info__drx_LongCycleStartOffset__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DRX_Info__drx_LongCycleStartOffset__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DRX_Info__drx_LongCycleStartOffset__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))))))) in match t' return DRX_Info__drx_LongCycleStartOffset__Type with end) n0
           end t0).

Lemma DRX_Info__drx_LongCycleStartOffset__helper2 :  forall (y : DRX_Info__drx_LongCycleStartOffset__Type), DRX_Info__drx_LongCycleStartOffset__cond y -> choice_cond DRX_Info__drx_LongCycleStartOffset__list (DRX_Info__drx_LongCycleStartOffset__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DRX_Info__drx_LongCycleStartOffset__helper3 :  forall (y : DRX_Info__drx_LongCycleStartOffset__Type), DRX_Info__drx_LongCycleStartOffset__F2 (DRX_Info__drx_LongCycleStartOffset__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DRX_Info__drx_LongCycleStartOffset__helper4 : (forall b : choice DRX_Info__drx_LongCycleStartOffset__list, choice_cond DRX_Info__drx_LongCycleStartOffset__list b -> DRX_Info__drx_LongCycleStartOffset__cond (DRX_Info__drx_LongCycleStartOffset__F2 b) /\ DRX_Info__drx_LongCycleStartOffset__F1 (DRX_Info__drx_LongCycleStartOffset__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DRX_Info__drx_LongCycleStartOffset__F1 DRX_Info__drx_LongCycleStartOffset__F2.
Definition DRX_Info__drx_LongCycleStartOffset__Format : T_Format DRX_Info__drx_LongCycleStartOffset__Type DRX_Info__drx_LongCycleStartOffset__cond :=
  (* Eval compute in *) proj2_format DRX_Info__drx_LongCycleStartOffset__cond DRX_Info__drx_LongCycleStartOffset__list__Format DRX_Info__drx_LongCycleStartOffset__F1 DRX_Info__drx_LongCycleStartOffset__F2 DRX_Info__drx_LongCycleStartOffset__helper2 DRX_Info__drx_LongCycleStartOffset__helper3 DRX_Info__drx_LongCycleStartOffset__helper4.
Opaque DRX_Info__drx_LongCycleStartOffset__cond DRX_Info__drx_LongCycleStartOffset__Format.

Definition DRX_Info__shortDRX__drx_ShortCycle__Format : T_Format DRX_Info__shortDRX__drx_ShortCycle__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_Info__shortDRX__drx_ShortCycle__nat__Format DRX_Info__shortDRX__drx_ShortCycle__F1 DRX_Info__shortDRX__drx_ShortCycle__F2 DRX_Info__shortDRX__drx_ShortCycle__F1F2 DRX_Info__shortDRX__drx_ShortCycle__F2F1.

Opaque DRX_Info__shortDRX__drx_ShortCycle__cond DRX_Info__shortDRX__drx_ShortCycle__Format.

Definition DRX_Info__shortDRX__drx_ShortCycleTimer__Format : T_Format Z DRX_Info__shortDRX__drx_ShortCycleTimer__cond :=
 ranged_int_format (1) (16) DRX_Info__shortDRX__drx_ShortCycleTimer__helper1 DRX_Info__shortDRX__drx_ShortCycleTimer__helper2.

Opaque DRX_Info__shortDRX__drx_ShortCycleTimer__cond DRX_Info__shortDRX__drx_ShortCycleTimer__Format.


Definition DRX_Info__shortDRX__Format_Type := Eval cbn in seq_format_prod DRX_Info__shortDRX__list.
Definition DRX_Info__shortDRX__Format_list : DRX_Info__shortDRX__Format_Type :=
  (DRX_Info__shortDRX__drx_ShortCycle__Format, (DRX_Info__shortDRX__drx_ShortCycleTimer__Format, unit_format)).
Definition DRX_Info__shortDRX__list__Format := (*Eval compute in *) seq_format DRX_Info__shortDRX__list DRX_Info__shortDRX__Format_list.
Definition DRX_Info__shortDRX__F1 z :=
  (DRX_Info__shortDRX__drx_ShortCycle z, (DRX_Info__shortDRX__drx_ShortCycleTimer z, tt)).
Definition DRX_Info__shortDRX__F2 (y : seq_type DRX_Info__shortDRX__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DRX_Info__shortDRX__Type i0 i1
  end.
Lemma DRX_Info__shortDRX__F1F2_cond (z : DRX_Info__shortDRX__Type)
  : DRX_Info__shortDRX__cond z ->
  (seq_cond DRX_Info__shortDRX__list (DRX_Info__shortDRX__F1 z)).
intro H. unfold DRX_Info__shortDRX__cond in H. simpl. auto. Qed.
Lemma DRX_Info__shortDRX__F1F2_cond2 (z : DRX_Info__shortDRX__Type)
 : DRX_Info__shortDRX__F2 (DRX_Info__shortDRX__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_Info__shortDRX__F2F1_cond (y : seq_type DRX_Info__shortDRX__list)
  : seq_cond DRX_Info__shortDRX__list y ->
 (DRX_Info__shortDRX__cond (DRX_Info__shortDRX__F2 y)) /\  DRX_Info__shortDRX__F1 (DRX_Info__shortDRX__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_Info__shortDRX__cond. simpl in *. auto.
 - simpl. unfold DRX_Info__shortDRX__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_Info__shortDRX__Format : T_Format DRX_Info__shortDRX__Type DRX_Info__shortDRX__cond :=
        proj2_format  DRX_Info__shortDRX__cond DRX_Info__shortDRX__list__Format
    DRX_Info__shortDRX__F1 DRX_Info__shortDRX__F2 DRX_Info__shortDRX__F1F2_cond  DRX_Info__shortDRX__F1F2_cond2 DRX_Info__shortDRX__F2F1_cond.
Opaque DRX_Info__shortDRX__cond DRX_Info__shortDRX__Format.


Definition DRX_Info__Format_Type := Eval cbn in seq_format_prod DRX_Info__list.
Definition DRX_Info__Format_list : DRX_Info__Format_Type :=
  (DRX_Info__drx_LongCycleStartOffset__Format, (DRX_Info__shortDRX__Format, unit_format)).
Definition DRX_Info__list__Format := (*Eval compute in *) seq_format DRX_Info__list DRX_Info__Format_list.
Definition DRX_Info__F1 z :=
  (DRX_Info__drx_LongCycleStartOffset z, (DRX_Info__shortDRX z, tt)).
Definition DRX_Info__F2 (y : seq_type DRX_Info__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DRX_Info__Type i0 i1
  end.
Lemma DRX_Info__F1F2_cond (z : DRX_Info__Type)
  : DRX_Info__cond z ->
  (seq_cond DRX_Info__list (DRX_Info__F1 z)).
intro H. unfold DRX_Info__cond in H. simpl. auto. Qed.
Lemma DRX_Info__F1F2_cond2 (z : DRX_Info__Type)
 : DRX_Info__F2 (DRX_Info__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_Info__F2F1_cond (y : seq_type DRX_Info__list)
  : seq_cond DRX_Info__list y ->
 (DRX_Info__cond (DRX_Info__F2 y)) /\  DRX_Info__F1 (DRX_Info__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_Info__cond. simpl in *. auto.
 - simpl. unfold DRX_Info__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_Info__Format : T_Format DRX_Info__Type DRX_Info__cond :=
        proj2_format  DRX_Info__cond DRX_Info__list__Format
    DRX_Info__F1 DRX_Info__F2 DRX_Info__F1F2_cond  DRX_Info__F1F2_cond2 DRX_Info__F2F1_cond.
Opaque DRX_Info__cond DRX_Info__Format.

