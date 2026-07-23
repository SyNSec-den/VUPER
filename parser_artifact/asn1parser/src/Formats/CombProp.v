Require Import
  ASN1Parser.tact
  ASN1Parser.AbsArray
  ASN1Parser.Array.BitRep
  ASN1Parser.Formats.Comb.

Require Import ProofIrrelevance
  Lia.

Lemma flg_add_to_same : forall f1 f2,
    flg_add f1 f2 = SameVer ->
    (f1 = SameVer /\ f2 = SameVer).
Proof.
  intros. destruct f1.
  - destruct f2; auto.
  - simpl in H.  inversion H.
Qed.


Lemma bind_parse_consist
  {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (ParA : Parse A Pa)
  (f : forall a : A, Pa a -> Flg -> Parse B Pb) :
  decode_consistent _ _ ParA ->
  (forall a pf_a flg, decode_consistent _ _ (f a pf_a flg)) ->
  decode_consistent _ _  (bind_parse ParA f). 
Proof.
  intros. unfold decode_consistent. intros.
  unfold bind_parse in H1. destruct_match_new. repeat destruct_let.
  eassert (G0 := H _ _ _ _ _ _ E).
  eassert (G1 := H0 _ _ _ _ _ _ _ _ _ H1).
  split_and. 
  split.
  - eapply BProp.le_pos_trans.
    + apply H4.
    + trivial.
  - intros. eapply EQ.equiv_b_split in H6; try apply H2; auto.
    destruct H6.  split_and. 
    unfold bind_parse.
    erewrite H5.
    + erewrite H3.
      * f_equal.
      * apply H10.
    + auto.
Qed.

Lemma return_parse_consist
  {A : Set} {P : A -> Prop} (a : {x : A | P x}) (flg : Flg) : 
  decode_consistent _ _ (return_parse a flg).
Proof.
  unfold decode_consistent. intros.
  unfold return_parse in H. inversion H. subst.
  split; try apply BProp.le_pos_refl.
  intros. unfold return_parse.  f_equal.
  f_equal.  f_equal.
  assert (G1 := EQ.equiv_b_eq_len H0).
  assert (G2 := EQ.equiv_b_implies_valid_pair H0).
  unfold BProp.pos_to_len in G1.
  unfold EQ.valid_pos_pair in G2. split_and.
  assert (BA.to_nat pos0 = BA.to_nat pos0').
  { Lia.lia. } 
  
  rewrite <- (BProp.of_to_nat pos0),   <- (BProp.of_to_nat pos0').
  rewrite H1; auto.
Qed.

(* Some other definitions *)

(* Proofs of correctness for basic 
   operations
 *)
Lemma proj_non_inter : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (encode : Serialize A' P2)
    (f : A -> A')
    (p1_dec : dec_P P1)
    (imp : forall a : A, P1 a -> P2 (f a)), 
    encode_non_inter _ _ encode ->
    encode_non_inter _ _ (proj_serialize encode f p1_dec).
Proof.
  intros. unfold encode_non_inter in *.
  intros.
  unfold proj_serialize in H0.
  destruct_match_dec. destruct_match.
  destruct p0, p0. inversion H0. subst.
  rewrite (proof_irrelevance _ p1 (imp a pf)) in E0.
  assert (G := H (f a) bf bf' pos pos' (imp a pf) E0).
  apply G. 
Qed.

Lemma proj_encode_consist : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (encode : Serialize A' P2)
    (f : A -> A')
    (p1_dec : dec_P P1),
    encode_consistent _ _ encode ->
    encode_consistent _ _ (proj_serialize encode f p1_dec).
Proof.
  intros. unfold encode_consistent in *.
  intros.
  unfold proj_serialize in H0, H1.
  destruct_match_dec. repeat destruct_match.
  destruct p0, p0, p1, p1.
  inversion H0. inversion H1. subst. 
  rewrite (proof_irrelevance _ p2 p3) in E0.
  apply (H (f a) bf bf' pos pos' bf0 bf0'
           pos0 pos0' p3 E1 E0).
Qed.

Lemma proj_decode_consist : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (decode : Parse A' P2)
    (f_inv : A' -> A)
    (imp_inv : forall a' : A', P2 a' -> P1 (f_inv a'))
    (p1_dec : dec_P P1),
    decode_consistent _ _ decode ->
    decode_consistent _ _ (proj_parse decode f_inv imp_inv).
Proof.
  intros. unfold decode_consistent in *.
  intros. unfold proj_parse in *. 
  destruct_enc.
  inversion H0. subst. 
  eassert (G := H x _ _ _ _ _ E).
  destruct G.  split; auto.
  intros. assert (G' := H2 _ _ _ H3).
  rewrite G'. rewrite (proof_irrelevance _ (imp_inv x p0) pf). auto.
Qed.

Lemma proj_correct_surj : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (p1_dec : dec_P P1)
    (f : A -> A')
    (f_inv : A' -> A)
    (imp : forall a : A, P1 a -> (P2 (f a) /\ f_inv (f a) = a))
    (imp_inv : forall b : A', P2 b -> (P1 (f_inv b) /\ f (f_inv b) = b))
    (serial : Serialize A' P2) (parse : Parse A' P2),
    format_correct_surj _ _ serial parse ->
    format_correct_surj _ _ (proj_serialize serial f p1_dec)
      (proj_parse parse f_inv (fun z p => proj1 (imp_inv z p))).
Proof.
  intros.

  unfold format_correct_surj in *.
  unfold proj_parse, proj_serialize.
  intros.  
  destruct_match_dec. destruct_match.
  destruct p0, p0.  inversion H0; subst.
  
  assert (G := H (f a) bf bf' pos pos' p1 E0). 
  rewrite G.
  
  assert (G1 := proj2 (imp a pf)). 
  repeat f_equal.

  apply subset_eq_compat. apply G1. 
Qed.

Lemma proj_correct_inj : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (p1_dec : dec_P P1)
    (f : A -> A')
    (f_inv : A' -> A)
    (imp : forall a : A, P1 a -> (P2 (f a) /\ f_inv (f a) = a))
    (imp_inv : forall b : A', P2 b -> (P1 (f_inv b) /\ f (f_inv b) = b))
    (serial : Serialize A' P2) (parse : Parse A' P2),
    format_correct_inj_same _ _  serial parse ->
    format_correct_inj_same _ _ (proj_serialize serial f p1_dec)
      (proj_parse parse f_inv (fun z p => proj1 (imp_inv z p))).
Proof.
  intros.  unfold format_correct_inj_same in *. intros.
  unfold proj_parse, proj_serialize in *.
  destruct_enc. inversion H0.  subst.
  assert (G := H _ _ _ _ _ E bf0 H1).
  destruct_match_dec_goal; try contradiction.
  destruct G. split_and.
  exists x0.
  rewrite (proj2 (imp_inv x p0)). 
  rewrite H3. split; auto.
  encode_eq.
Qed.

Lemma proj_correct_inj_diff :
  forall {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
         (p1_dec : dec_P P1)
         (f : A -> A')
         (f_inv : A' -> A)
         (imp : forall a : A, P1 a -> (P2 (f a) /\ f_inv (f a) = a))
         (imp_inv : forall b : A', P2 b -> (P1 (f_inv b) /\ f (f_inv b) = b))
         (serial : Serialize A' P2) (parse : Parse A' P2)
         (to_len : A' -> option nat),
    format_correct_inj_diff _ _  serial parse to_len ->
    format_correct_inj_diff _ _ (proj_serialize serial f p1_dec)
      (proj_parse parse f_inv (fun z p => proj1 (imp_inv z p)))
      (fun a => to_len (f a)).
Proof.
  intros. unfold format_correct_inj_diff in *.  intros.
  unfold proj_parse in H0.  unfold proj_serialize.
  destruct_enc.  inversion H0. subst. apply H in E.
  destruct E.  exists x0.  intros.  apply H1 in H2.
  destruct H2.
  { left.
    eassert (G := proj2 (imp_inv x p0)).
    rewrite G.  apply H2. }
  right.
    
  destruct_ex. split_and. 
  destruct_match_dec_goal.
  - assert (G := proj2 (imp_inv x p0)).
    rewrite G, H3. exists x1. exists x2.
    split.
    + encode_eq.
    + apply H4.
  - destruct (n pf). 
Qed.

Lemma proj_correct_to_len :
  forall {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
         (p1_dec : dec_P P1) (f : A -> A')
         (f_inv : A' -> A)
         (imp : forall a : A, P1 a -> (P2 (f a) /\ f_inv (f a) = a))
         (imp_inv : forall b : A', P2 b -> (P1 (f_inv b) /\ f (f_inv b) = b))
         (serial : Serialize A' P2)
         (parse : Parse A' P2)
         (to_len : A' -> option nat),
    format_to_len_correct _ _ serial parse to_len -> 
    format_to_len_correct _ _ (proj_serialize serial f p1_dec)
      (proj_parse parse f_inv (fun z p => proj1 (imp_inv z p)))
    (fun a : A => to_len (f a)).
Proof.
  intros. unfold format_to_len_correct in *. split_and. split. 
  - unfold proj_serialize. intros. destruct_match_dec_new. destruct_enc.
    inversion H. subst. apply H0 in E0.  auto.
  - unfold proj_parse. intros.  destruct_enc. inversion H. subst.
    apply H1 in E.

    assert (G := proj2 (imp_inv x p0)).
    rewrite G.  apply E. 
Qed.

(* Helper function *)
Lemma equiv_b_buffer_len_same : forall {bf bf' pos}, 
    EQ.equiv_b bf bf' pos (BProp.pos_end bf) pos (BProp.pos_end bf') ->
    (BProp.pos_end bf) = (BProp.pos_end bf').
Proof.
  intros.
  assert (lenE := EQ.equiv_b_eq_len H).
  unfold BProp.pos_to_len in lenE.
  assert (EP := EQ.equiv_b_implies_valid_pair H).
  destruct EP. destruct H0, H1.
  assert (endEq1 : BA.to_nat (BProp.pos_end bf) = BA.to_nat (BProp.pos_end bf')).
  { lia. }
  assert (endEq2 : BA.of_nat (BA.to_nat (BProp.pos_end bf)) =
                     BA.of_nat (BA.to_nat (BProp.pos_end bf'))).
  { f_equal. auto. }
  repeat rewrite BProp.of_to_nat in endEq2.
  auto.
Qed.

Lemma append_non_inter_proof_helper (bf b bf' : BA.Buffer) (pos p pos' : BA.Pos)
  : (EQ.equiv_b bf b BProp.pos_zero pos BProp.pos_zero pos /\
       EQ.equiv_b bf b p (BProp.pos_end bf) p (BProp.pos_end b) /\
       BProp.le_pos pos p) ->
    (EQ.equiv_b b bf' BProp.pos_zero p BProp.pos_zero p /\
       EQ.equiv_b b bf' pos' (BProp.pos_end b) pos' (BProp.pos_end bf') /\
       BProp.le_pos p pos') -> 
    EQ.equiv_b bf bf' BProp.pos_zero pos BProp.pos_zero pos /\
      EQ.equiv_b bf bf' pos' (BProp.pos_end bf) pos' (BProp.pos_end bf') /\
      BProp.le_pos pos pos'.
Proof.
  intros. 
  split_and. 
  split.
  (* basically, prove b - bf' are equal from 0 - pos
       then use transitivity, bf - b - bf'. 
   *)
  - eassert (E1 := EQ.equiv_b_same_pos H1
                     (BProp.pos_zero_le_all BProp.pos_zero)
                     H5
                     (BProp.pos_zero_le_all pos)).
    eapply ( EQ.equiv_b_trans ).
    + apply H2.
    + auto.
  - split. 
    (* Similar for the other side, prove bf - b are equal
       from pos' - end. Then use transitivity.
       Another problem, need to show le_pos pos' (pos_end bf').
     *) 
    + assert (Eq1 :=  equiv_b_buffer_len_same H0).
      assert (Eq2 :=  equiv_b_buffer_len_same H).
      rewrite <- Eq1 in H0.
      rewrite Eq2 in H. 

      rewrite <- Eq1.  rewrite Eq2. 

      assert (P_le : BProp.le_pos pos' (BProp.pos_end b)).
      { apply EQ.equiv_b_implies_valid_pair in H0.
        split_and. unfold EQ.valid_pos_pair in *. 
        unfold BProp.le_pos. lia.   }
      
      eassert (E2 := EQ.equiv_b_same_pos H H3
                       (BProp.le_pos_refl (BProp.pos_end b))
                       P_le).
      eapply EQ.equiv_b_trans.
      * apply E2.
      * auto. 
    + eapply (BProp.le_pos_trans).
      * apply H5.
      * auto. 
Qed.

(* Now for the sigma part.  *)
Lemma sigma_non_inter :
  forall {A A' : Set} {P1 : A -> Prop}
    (P2 : A -> A' -> Prop)
    (ser : Serialize A P1)
    (pser2 : forall (a : A), P1 a -> Serialize A' (P2 a)),
    encode_non_inter _ _ ser ->
    (forall a pf, encode_non_inter _ _ (pser2 a pf)) ->
    encode_non_inter _ _ (sigma_serialize ser P2 pser2).
Proof.
  intros. unfold encode_non_inter in *. 
  (* the current situation is that 
             
            bf 
            b        (encode fst a) pos - p
            bf'      (encode snd a) p   - pos'

       So anything outside these two positions should not
       change. 
   *)
  intros.
  unfold sigma_serialize in H1.
  destruct_match. destruct p, p. destruct_match.
  repeat destruct_let. inversion H1. subst.

  (* First from bf to b *)
  assert (G0 := H (fst a) bf b pos p p0 E). 
  (* From b to bf' *)
  assert (G1 := H0 (fst a) p0 (snd a) b bf' p pos' p2 E0).
  eapply append_non_inter_proof_helper.
  - apply G0.
  - auto.
Qed.

Lemma equiv_b_le_zero : forall b bf' pos p0,
    BA.to_nat pos <= BA.to_nat p0 ->
    EQ.equiv_b b bf' BProp.pos_zero p0 BProp.pos_zero p0 ->
    EQ.equiv_b b bf' pos p0 pos p0.
Proof.
  intros.
  eapply EQ.equiv_b_le; try apply H0; 
    unfold BProp.le_pos; try lia;
    rewrite BProp.pos_zero_equals_zero; apply PeanoNat.Nat.le_0_l.
Qed.

Lemma encode_consist_proof_helper (b bf' b0 bf0' : BA.Buffer)
  (pos p pos' pos0 p0 pos0' : BA.Pos) : 

  EQ.equiv_b bf' bf0' p pos' p0 pos0' -> 
  EQ.equiv_b b bf' BProp.pos_zero p BProp.pos_zero p ->
  EQ.equiv_b b0 bf0' BProp.pos_zero p0 BProp.pos_zero p0 ->
  EQ.equiv_b b b0 pos p pos0 p0 -> 
  EQ.equiv_b bf' bf0' pos pos' pos0 pos0'.
Proof.
  intros.
  destruct (EQ.equiv_b_implies_valid_pair H2).
  unfold EQ.valid_pos_pair in *. split_and. 
  
  eassert (EB1 := equiv_b_le_zero _ _ pos _ H4 H0).
  eassert (EB2 := equiv_b_le_zero _ _ _ _ H5 H1). 
  eapply EQ.equiv_b_append. 
  - eapply EQ.equiv_b_trans.
    + apply EQ.equiv_b_symm in EB1.
      apply EB1.
    + eapply EQ.equiv_b_trans.
      * apply H2.
      * apply EB2.
  - apply H.
Qed.

(* would require sigma_non_inter, should we combine
     these two properties together?
 *)
Lemma sigma_encode_consist : forall
    {A A' : Set} {P1 : A -> Prop} (P2 : A -> A' -> Prop)
    (ser : Serialize A P1)
    (pser2 : forall (a : A), P1 a -> Serialize A' (P2 a)),
    encode_consistent _ _ ser ->
    (forall a pf_a, encode_consistent _ _ (pser2 a pf_a)) ->
    (forall a pf, encode_non_inter _ _ (pser2 a pf)) ->
    encode_consistent _ _ (sigma_serialize ser P2 pser2).
Proof.
  intros. unfold encode_consistent. intros.
  unfold sigma_serialize in *.
  repeat destruct_match. destruct p0, p0, p, p.
  repeat destruct_match. destruct p3, p3, p4, p4.
  inversion H3. subst.  inversion H6.  subst.
  repeat clear_redu. 

  rewrite (proof_irrelevance _ p2 p1) in E, E2. 
  assert (G1 := H _ _ _ _ _ _ _ _ _ _ E0 E). 
  rewrite (proof_irrelevance _ p6 p5) in E2. 
  eassert (G2 := H0 _ _ _ _ _ _ _ _ _ _ _ _ E1 E2).
  (* Here,
       bf
       b     pos  -   p0
       bf'            p0   -  pos'

       bf0
       b0    pos0 -   p
       bf0'           p    -  pos0'

       we need to have non-inter on pser2, such that we would
       say that b - bf' are same from pos - p0.
   *)
  assert (G3 := H1 _ _ _ _ _ _ _ _ E1).
  assert (G4 := H1 _ _ _ _ _ _ _ _ E2).
  split_and.
  eapply encode_consist_proof_helper.
  - apply G2.
  - apply H3.
  - apply H2.
  - apply G1.
Qed.


Definition same_len_after_enc {A : Set} {P : A -> Prop} (encode : Serialize A P) :
  encode_non_inter _ _ encode ->
  (forall {a : A} {bf bf' : BA.Buffer} {pos pos': BA.Pos} {pf : P a},
      encode bf pos a = Some (bf', pos', pf) ->
      BA.len bf = BA.len bf').
Proof.
  intros. 
  assert (G := H _ _ _ _ _ _ H0).
  split_and.
  assert (G' := EQ.equiv_b_implies_valid_pair H3).
  split_and.  unfold EQ.valid_pos_pair in *.

  apply EQ.equiv_b_eq_len in H3.
  unfold BProp.pos_to_len in H3.
  repeat rewrite BProp.pos_end_equals_len in *.
  lia. 
Qed.

Lemma sigma_encode_len : forall
    {A A' : Set} {P1 : A -> Prop} (P2 : A -> A' -> Prop)
    (ser : Serialize A P1)
    (pser2 : forall (a : A), P1 a -> Serialize A' (P2 a)),
    encode_len_longer ser ->
    (forall a pf_a, encode_len_longer (pser2 a pf_a)) ->
    (encode_non_inter _ _ ser) ->
    encode_len_longer (sigma_serialize ser P2 pser2).
Proof.
  intros. unfold encode_len_longer.  intros.
  unfold sigma_serialize in *.  repeat destruct_enc.
  inversion H3.  subst. clear_redu_all.
  
  destruct (H _ _ _ _ _ _ _ H2 E). 
  rewrite H3.
  (* I do need to say that BA.len x = BA.len bf0
       This requires that 
   *)
  eassert (EL := same_len_after_enc ser H1 E).
  eassert (EL2 := same_len_after_enc ser H1 H3).
  rewrite EL, EL2 in H2.
  destruct (H0 _ _ _ _ _ _ _ _ _ H2 E0).
  rewrite H4.
  exists x0. encode_eq.
Qed.

Lemma sigma_decode_consist : forall  
    {A A' : Set} {P1 : A -> Prop} (P2 : A -> A' -> Prop)
    (ser : Parse A P1)
    (pser2 : forall (a : A), P1 a -> Parse A' (P2 a)),
    decode_consistent _ _ ser ->
    (forall a pf_a, decode_consistent _ _ (pser2 a pf_a)) ->
    decode_consistent _ _ (sigma_parse ser P2 pser2).
Proof.
  intros. unfold decode_consistent in *. intros.
  unfold sigma_parse in *.
  unfold bind_parse, return_parse in *. 
  repeat destruct_enc.
  inversion H1.  destruct a. inversion H3.  subst.
  clear H3. clear H1.
  
  destruct (H _ _ _ _ _ _ E). 
  destruct (H0 _ _ _ _ _ _ _ _ E0).

  split.
  - unfold BProp.le_pos in *.  try lia.
  - intros. 
    eassert (EB := EQ.equiv_b_split H5 p H1 H3).
    destruct EB.  split_and.
    rewrite (H2 _ _ _ H8).
    rewrite (H4 _ _ _ H10).
    decode_eq. 
Qed.

Lemma sigma_correct_surj
  : forall {A A' : Set} (P1 : A -> Prop)
      (P2 : A -> A' -> Prop)
      (ser1 : Serialize A P1)
      (par1 : Parse A P1)
      (fser2 : forall (a : A), P1 a -> Serialize A' (P2 a))
      (pser2 : forall (a : A), P1 a -> Parse A' (P2 a)),
    format_correct_surj _ _ ser1 par1 ->
    (forall a pf, format_correct_surj _ _ (fser2 a pf) (pser2 a pf)) ->
    decode_consistent _ _ par1 ->
    (forall a pf, encode_non_inter _ _ (fser2 a pf)) ->
    format_correct_surj _ _ 
      (sigma_serialize ser1 P2
         (fun a pf => fser2 a pf))
      (sigma_parse par1 _  pser2).
Proof.
  intros. 
  unfold format_correct_surj, sigma_parse, return_parse. 
  intros.
  
  assert (PC1 := H).

  unfold sigma_serialize, bind_parse in *.
  destruct_match. destruct p, p. 
  destruct_match. destruct p1, p1.
  
  inversion H5; subst.
  repeat clear_redu.
  assert (G := H _ _ _ _ _ _ E).
  
  eassert (G1 := H0 _ _ _ _ _ _ _ _ E0).
  destruct (H1 _ _ _ _ _ _ G). 
  assert (S2 := H2 _ _ _ _ _ _ _ _ E0).
  split_and.

  unfold BProp.le_pos in H3. 
  eassert (S3 := equiv_b_le_zero _ _ _ _  H3 H5). 
  rewrite (H4 _ _ _ S3), G1.
  decode_eq. 
  destruct a; auto. 
Qed.

Lemma sigma_correct_inj
  : forall {A A' : Set} (P1 : A -> Prop)
      (P2 : A -> A' -> Prop)
      (ser1 : Serialize A P1)
      (par1 : Parse A P1)
      (fser2 : forall (a : A), P1 a -> Serialize A' (P2 a))
      (pser2 : forall (a : A), P1 a -> Parse A' (P2 a)),
    format_correct_inj_same _ _  ser1 par1 ->
    (forall a pf, format_correct_inj_same _ _ (fser2 a pf) (pser2 a pf)) ->
    encode_non_inter _ _ ser1 ->
    (forall a pf, encode_non_inter _ _ (fser2 a pf)) ->
    format_correct_inj_same _ _ 
      (sigma_serialize ser1 P2
         (fun a pf => fser2 a pf))
      (sigma_parse par1 _  pser2).
Proof.
    intros. unfold format_correct_inj_same in *.
    intros.  unfold sigma_parse, bind_parse, return_parse in H3.
    repeat destruct_enc. 
    destruct a. inversion H3.
    destruct (flg_add_to_same _ _ H9).
    subst. clear H3. 

    unfold sigma_serialize. simpl. 
    destruct (H _ _ _ _ _ E _ H4).
    destruct H3.

    rewrite H3.
    
    eassert (SL := same_len_after_enc _ H1 H3).
    rewrite H4 in SL. apply eq_sym in SL. 
    destruct (H0 _ _ _ _ _ _ _ E0 x SL).
    destruct H6.

    rewrite H6. exists x0. 
    split.
    - f_equal. f_equal. apply  proof_irrelevance.
    - eapply EQ.equiv_b_append.
      shelve.
      apply H7.
      Unshelve.
      assert (EB1 := H2 _ _ _ _ _ _ _ _ H6).
      assert (EB2 := H1 _ _ _ _ _ _ H3). 
      split_and. unfold BProp.le_pos in *. 
      
      eapply EQ.equiv_b_trans.
      + apply H5.
      + apply equiv_b_le_zero; auto. 
  Qed.
          
  (* Here they need the equivalence property.
     Again, here we have

     bf
     b     pos  -   p0
     bf'            p0   -  pos'

     We are decoding bf.
     bf    pos  -   p0   -  pos'

     We are encoding to bf0
     bf0
     x     pos  -   p
     x0             p    -  pos'

     So here, we are encoding to x. Thus, we need to say
     encode the second part after x. So we need to say
     

     When parsing, we are reading from bf'. So we also need
     the non-inter property. 
   *)

Lemma sigma_to_len_correct
  : forall {A A' : Set} (P1 : A -> Prop)
      (P2 : A -> A' -> Prop)
      (ser1 : Serialize A P1)
      (par1 : Parse A P1)
      (tl1 : A -> option nat)
      (fser2 : forall (a : A), P1 a -> Serialize A' (P2 a))
      (pser2 : forall (a : A), P1 a -> Parse A' (P2 a))
      (tl2 : forall (a : A),  (A' -> option nat)),
    format_to_len_correct _ _  ser1 par1 tl1 ->
    (forall a pf, format_to_len_correct _ _ (fser2 a pf) (pser2 a pf) (tl2 a)) ->
    encode_non_inter _ _ ser1 -> 
     (forall a pf, encode_non_inter _ _ (fser2 a pf)) -> 
    format_to_len_correct _ _ 
      (sigma_serialize ser1 P2
         (fun a pf => fser2 a pf))
      (sigma_parse par1 _  pser2)
      (sigma_to_len tl1 tl2).
Proof. 
  unfold format_to_len_correct.  intros. split_and. split.
  - intros. destruct a. simpl.
    unfold sigma_serialize in H. repeat destruct_enc.
    simpl in E0.  
    inversion H. subst. clear H. simpl in *. 
    
    eassert (K1 := H3 _ _ _ _ _ _ E).
    destruct (H0 a p0). 
    eassert (K2 := H _ _ _ _ _ _ E0).

    unfold sigma_to_len. simpl. rewrite K1, K2. unfold add_opt. f_equal.

    eassert (NI1 := H1 _ _ _ _ _ _ E).
    eassert (NI2 := H2 _  _ _ _ _ _ _ _ E0).
    split_and. unfold BProp.le_pos in *.  lia.
  - intros. unfold sigma_parse, bind_parse, return_parse in H. repeat destruct_enc. 
    inversion H. subst. clear H.

    eassert (K1 := H4 _ _ _ _ _ _ E).
    destruct (H0 x p0).
    eassert (K2 := H5 _ _ _ _ _ _ E0).
    destruct_ex.
    unfold sigma_to_len.  simpl. rewrite H6, H7. simpl.  exists (x2 + x1).  auto. 
Qed.
    
Opaque Nat.pow.
Lemma sigma_correct_inj_diff
  : forall {A A' : Set} (P1 : A -> Prop)
      (P2 : A -> A' -> Prop)
      (ser1 : Serialize A P1)
      (par1 : Parse A P1)
      (tl1 : A -> option nat)
      (fser2 : forall (a : A), P1 a -> Serialize A' (P2 a))
      (pser2 : forall (a : A), P1 a -> Parse A' (P2 a))
      (tl2 : forall (a : A),  (A' -> option nat)),
    format_correct_inj_diff _ _  ser1 par1 tl1 ->
    (forall a pf, format_correct_inj_diff _ _ (fser2 a pf) (pser2 a pf) (tl2 a)) ->
    encode_non_inter _ _ ser1 ->
    (* (forall a pf, encode_non_inter _ _ (fser2 a pf)) -> *)
    format_to_len_correct _ _  ser1 par1 tl1 ->
    (forall a pf, format_to_len_correct _ _ (fser2 a pf) (pser2 a pf) (tl2 a)) ->
    format_correct_inj_diff _ _ 
      (sigma_serialize ser1 P2
         (fun a pf => fser2 a pf))
      (sigma_parse par1 _  pser2)
      (sigma_to_len tl1 tl2).
Proof.
  intros. unfold format_correct_inj_diff. intros.
  unfold sigma_parse, bind_parse, return_parse in *.
  destruct a. repeat destruct_enc. inversion H4. subst.
  clear H4.
  eassert (K1 := H _ _ _ _ _ _ E).
  eassert (K2 := H0 _ _ _ _ _ _ _ _ E0).

  destruct_ex. exists (x + x0). intros. 
  assert (G1 : BA.to_nat pos0 + x0 <= BA.len bf0). { lia. }
  apply H5 in G1. 

  simpl in *. 
  eassert (T1 := (proj2 H2) _ _ _ _ _ _ E).
  eassert (T2 := (proj2 (H3 a p0)) _ _ _ _ _ _ E0).
  unfold sigma_to_len.  simpl. 
  destruct_ex.
  rewrite H7, H8. simpl.
  
  destruct G1.
  { left. 
    
    rewrite H8 in H9.
    assert (x2 <= x2 + x1). { lia. }
    apply get_byte_len_mono in H10. lia. }
  
  destruct_ex.  split_and. 
  unfold sigma_serialize. simpl.
  rewrite H10. 
    
  assert (G2 : BA.to_nat x4 + x <= BA.len x3). 
  { eassert (SL := same_len_after_enc ser1 H1 H10). lia. }

  apply H4 in G2.
  destruct G2.
  { left. rewrite H7 in H13.
    assert (x1 <= x2 + x1). { lia. }
    apply get_byte_len_mono in H14. lia. } 

  right.
  destruct_ex.  split_and. 
  rewrite H14.  exists x5. exists x6. 
  split.
  - encode_eq.
  - lia. 
Qed.


(* Here, for sigma and append, we could show that
     append is simply a special case of sigma. Therefore,
     we don't have to prove properties of append. We could
     just use the reuse the proof for sigma. 
 *)
Lemma append_eq_sigma_encode :
  forall {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop}
    (sa : Serialize A P1) (sb : Serialize B P2),
    (append_serialize sa sb) =
      (sigma_serialize
         sa
         (fun _ b => P2 b)
         (fun _ _ => sb)).
Proof.
  intros. unfold append_serialize, sigma_serialize. auto.
Qed.

Lemma append_eq_sigma_decode :
  forall {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop}
    (pa : Parse A P1) (pb : Parse B P2),
    (append_parse pa pb) =
      (sigma_parse
         pa
         (fun _ b => P2 b)
         (fun _ _ => pb)).
Proof.
  intros. unfold append_parse, sigma_parse. auto.
Qed.

Lemma append_eq_sigma_to_len :
  forall {A B : Set}
    (sa : A -> option nat) (sb : B -> option nat),
    (append_to_len sa sb) =
      (sigma_to_len sa (fun _ b => sb b) ).
Proof.
  auto. 
Qed.

(* We still need to add proofs for Append, by using the
     proofs for sigma *)
Lemma append_non_inter :
  forall {A A' : Set} {P1 : A -> Prop}
    {P2 : A' -> Prop}
    (ser1 : Serialize A P1)
    (ser2 : Serialize A' P2),
    encode_non_inter _ _ ser1 ->
    encode_non_inter _ _ ser2 ->
    encode_non_inter _ _ (append_serialize ser1 ser2).
Proof.
  intros.
  rewrite append_eq_sigma_encode. 
  eassert (G := sigma_non_inter
                  (fun _ b => P2 b) ser1 (fun _ _ => ser2) H).
  apply G. intros.  apply H0.
Qed.

Lemma append_encode_consist : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (ser1 : Serialize A P1)
    (ser2 : Serialize A' P2),
    encode_consistent _ _ ser1 ->
    encode_consistent _ _ ser2 ->
    encode_non_inter _ _ ser2 ->
    encode_consistent _ _ (append_serialize ser1 ser2).
Proof.
  intros. rewrite append_eq_sigma_encode.
  eassert (G := sigma_encode_consist (fun _ b => P2 b) ser1
                  (fun _ _ => ser2) H).
  apply G;
    intros; auto. 
Qed.

Lemma append_encode_len : forall
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (ser1 : Serialize A P1)
    (ser2 : Serialize A' P2),
    encode_len_longer ser1 ->
    (encode_len_longer ser2) ->
    (encode_non_inter _ _ ser1) ->
    encode_len_longer (append_serialize ser1 ser2).
Proof.
  intros.  rewrite append_eq_sigma_encode.
  eassert (G := sigma_encode_len (fun _ b => P2 b) ser1
                  (fun _ _ => ser2) H).
  apply G; intros; auto.
Qed.

Lemma append_decode_consist : forall  
    {A A' : Set} {P1 : A -> Prop} {P2 : A' -> Prop}
    (ser1 : Parse A P1)
    (ser2 : Parse A' P2),
    decode_consistent _ _ ser1 ->
    decode_consistent _ _ ser2 ->
    decode_consistent _ _ (append_parse ser1 ser2).
Proof.
  intros. rewrite append_eq_sigma_decode.
  eassert (G := sigma_decode_consist
                  (fun _ b => P2 b) ser1 (fun _ _ => ser2)).
  apply G; intros; auto.
Qed.

Lemma append_correct_surj 
  : forall {A A' : Set} (P1 : A -> Prop)
      (P2 : A' -> Prop)
      (ser1 : Serialize A P1)
      (par1 : Parse A P1)
      (ser2 : Serialize A' P2)
      (par2 : Parse A' P2),
    format_correct_surj _ _ ser1 par1 ->
    format_correct_surj _ _ ser2 par2 ->
    decode_consistent _ _ par1 ->
    encode_non_inter _ _ ser2 ->
    format_correct_surj _ _ 
      (append_serialize ser1 ser2)
      (append_parse par1 par2).
Proof.
  intros. rewrite append_eq_sigma_decode, append_eq_sigma_encode.
  eassert (G := sigma_correct_surj _ _ ser1 par1
                  (fun _ _ => ser2) (fun _ _ => par2) ).
  apply G; auto.
Qed.

Lemma append_correct_inj :
  forall {A A' : Set} (P1 : A -> Prop)
    (P2 : A' -> Prop)
    (ser1 : Serialize A P1)
    (par1 : Parse A P1)
    (ser2 : Serialize A' P2)
    (par2 : Parse A' P2),
    format_correct_inj_same _ _ ser1 par1 ->
    format_correct_inj_same _ _ ser2 par2 ->
    encode_non_inter _ _ ser1 ->
    encode_non_inter _ _ ser2 ->
    format_correct_inj_same _ _ 
      (append_serialize ser1 ser2)
      (append_parse par1 par2).
Proof.
  intros.  rewrite append_eq_sigma_decode, append_eq_sigma_encode.
  eassert (G := sigma_correct_inj _ _ ser1 par1
                  (fun _ _ => ser2) (fun _ _ => par2) ).
  apply G; auto.
Qed.

Lemma append_to_len_correct : 
  forall {A A' : Set} {P1 : A -> Prop}
    {P2 : A' -> Prop}
    (ser1 : Serialize A P1)
    (par1 : Parse A P1)
    (tl1 : A -> option nat)
    (ser2 : Serialize A' P2)
    (par2 : Parse A' P2)
    (tl2 : A' -> option nat),
    format_to_len_correct _ _  ser1 par1 tl1 ->
    format_to_len_correct _ _ ser2 par2 tl2 ->
    encode_non_inter _ _ ser1 -> 
    encode_non_inter _ _ ser2 -> 
    format_to_len_correct _ _ 
      (append_serialize ser1 ser2)
      (append_parse par1 par2)
      (append_to_len tl1 tl2).
Proof.
  intros. rewrite append_eq_sigma_encode, append_eq_sigma_decode, append_eq_sigma_to_len.
  eassert (G := sigma_to_len_correct _ _ ser1 par1 tl1
                  (fun _ _ => ser2)).
  apply G; auto. 
Qed.
  
Lemma append_correct_inj_diff :
  forall {A A' : Set} {P1 : A -> Prop}
    {P2 : A' -> Prop}
    (ser1 : Serialize A P1)
    (par1 : Parse A P1)
    (tl1 : A -> option nat)
    (ser2 : Serialize A' P2)
    (par2 : Parse A' P2)
    (tl2 : A' -> option nat),
    format_correct_inj_diff _ _ ser1 par1 tl1 ->
    format_correct_inj_diff _ _ ser2 par2 tl2 ->
    encode_non_inter _ _ ser1 ->
    format_to_len_correct _ _  ser1 par1 tl1 ->
    format_to_len_correct _ _ ser2 par2 tl2 ->
    format_correct_inj_diff _ _ 
      (append_serialize ser1 ser2)
      (append_parse par1 par2)
      (append_to_len tl1 tl2). 
Proof.
  intros.  rewrite append_eq_sigma_decode, append_eq_sigma_encode,
    append_eq_sigma_to_len.
  eassert (G := sigma_correct_inj_diff _ _ ser1 par1 tl1
                  (fun _ _ => ser2) (fun _ _ => par2) ).
  apply G; auto.
Qed.

(* Can we also prove that restrict is a special case of
     project? No.

      Note that restrict and project are after all different. 
     project requires that the function is a one-to-one correspondance 
     within the defined range. However, in restrict, it is not enforced.

     We restrict the range smaller such that we could not recover some 
     information.

     However, serialize is equal.
 *)
Lemma restrict_eq_proj_encode
  : forall {A : Set} {P R : A -> Prop} 
      (r_dec : dec_P R)
      (serial : Serialize A P),
    restrict_serialize r_dec serial = 
      proj_serialize serial id r_dec. 
Proof.
  intros. unfold restrict_serialize, proj_serialize.
  auto.
Qed.

Lemma restrict_non_inter : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (r_dec : dec_P R),
    encode_non_inter _ _ encode ->
    encode_non_inter _ _ (restrict_serialize r_dec encode).
Proof.
  intros. unfold encode_non_inter in *.
  intros. unfold restrict_serialize in H0.
  destruct_match_dec. destruct_match.
  destruct p, p. inversion H0. subst.
  eapply H.
  apply E0.
Qed.

Lemma restrict_encode_consist : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (r_dec : dec_P R),
    encode_consistent _ _ encode ->
    encode_consistent _ _ (restrict_serialize r_dec encode).
Proof.
  intros. rewrite restrict_eq_proj_encode.
  apply proj_encode_consist.  apply H. 
Qed.

Lemma restrict_encode_len : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (r_dec : dec_P R),
    encode_len_longer encode ->
    encode_len_longer (restrict_serialize r_dec encode).
Proof.
  intros. unfold encode_len_longer. 
  intros. 
  unfold restrict_serialize in H1. 
  destruct_match_dec. destruct_enc. 
  inversion H1. subst.  
  destruct (H _ _ _ _ _ _ _  H0 E0).

  unfold restrict_serialize. rewrite E, H2.
  exists x. encode_eq. 
Qed.

Lemma restrict_decode_consist : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (decode : Parse A P)
    (r_dec : dec_P R),
    decode_consistent _ _ decode ->
    decode_consistent _ _ (restrict_parse r_dec decode).
Proof.
  intros. unfold decode_consistent in *. intros.
  unfold restrict_parse in H0.
  destruct_enc. destruct_match_dec_new. 
  inversion H0. subst. 
  
  destruct  (H _ _ _ _ _ _ E). 
  split; auto. intros.
  unfold restrict_parse. 
  assert (G' := H2 _ _ _ H3).
  rewrite G', E0. decode_eq. 
Qed.

Lemma restrict_correct_surj : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (decode : Parse A P)
    (r_dec : dec_P R),
    format_correct_surj _ _ encode decode ->
    format_correct_surj _ _ 
      (restrict_serialize r_dec encode)
      (restrict_parse r_dec decode).
Proof.
  intros. unfold format_correct_surj in *.
  intros. unfold restrict_serialize in H0.
  destruct_match_dec. destruct_match_new.
  destruct p, p. inversion H0.  subst.
  repeat clear_redu.
  assert (G := H _ _ _ _ _ _ E0).  unfold restrict_parse.
  rewrite G, E. decode_eq. 
Qed.

Lemma restrict_correct_inj : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (decode : Parse A P)
    (r_dec : dec_P R),
    format_correct_inj_same _ _ encode decode ->
    format_correct_inj_same _ _ 
      (restrict_serialize r_dec encode)
      (restrict_parse r_dec decode).
Proof.
  intros. unfold format_correct_inj_same in *. intros.
  unfold restrict_parse in H0.
  destruct_enc. 
  destruct_match_dec_new. inversion H0. subst.
  clear H0.
  
  destruct (H _ _ _ _ _ E _ H1).
  destruct H0.
  unfold restrict_serialize. rewrite E0, H0.
  exists x.  split; auto. encode_eq.
Qed.

Lemma restrict_to_len_correct : 
  forall {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (decode : Parse A P)
    (to_len : A -> option nat)
    (r_dec : dec_P R),
    format_to_len_correct _ _ encode decode to_len ->
    format_to_len_correct _ _
      (restrict_serialize r_dec encode)
      (restrict_parse r_dec decode)
      to_len.
Proof.
  intros. unfold format_to_len_correct in *. split_and.
  split.
  - intros. unfold restrict_serialize in H.
    destruct_match_dec_new. destruct_enc. inversion H. subst. 
    apply H0 in E0. auto.
  - intros. unfold restrict_parse in H. destruct_enc.
    destruct_match_dec_new. inversion H. subst.
    apply H1 in E. auto. 
Qed.

Lemma restrict_correct_inj_diff : forall
    {A : Set} {P : A -> Prop} (R : A -> Prop)
    (encode : Serialize A P)
    (decode : Parse A P)
    (to_len : A -> option nat)
    (r_dec : dec_P R),
    format_correct_inj_diff _ _ encode decode to_len ->
    format_correct_inj_diff _ _ 
      (restrict_serialize r_dec encode)
      (restrict_parse r_dec decode)
      to_len.
Proof.
  intros. unfold format_correct_inj_diff in *. intros.
  unfold restrict_parse in H0. destruct_enc.
  destruct_match_dec_new.  inversion H0. subst.
  assert (G := H _ _ _ _ _ _ E). 
  destruct_ex. exists x. intros.
  apply H1 in H2.
  destruct H2. 
  { left. auto. } 
  right. 
  destruct_ex. split_and.  unfold restrict_serialize.
  rewrite E0, H3. exists x0. exists x1. 
  split.
  - encode_eq.
  - lia. 
Qed.

(* I need some way to imply to all the lemmas from the 
   format_correct
 *)
Ltac fmt_imply_t :=
  let H := fresh "H" in
  intro H; 
  unfold format_correct in H; split_and; assumption.

Lemma fmt_enc_ni {A : Set} {P s p t}  :
  format_correct s p t ->
  encode_non_inter A P s.
  fmt_imply_t. Qed.

Lemma fmt_enc_consist {A : Set} {P s p t}  :
  format_correct s p t ->
  encode_consistent A P s.
  fmt_imply_t. Qed.

Lemma fmt_dec_consist {A : Set} {P s p t}  :
  format_correct s p t ->
  decode_consistent A P p.
  fmt_imply_t. Qed.

Lemma fmt_surj {A : Set} {P s p t}  :
  format_correct s p t ->
  format_correct_surj A P s p.
  fmt_imply_t. Qed.

Lemma fmt_inj_same {A : Set} {P s p t}  :
  format_correct s p t ->
  format_correct_inj_same A P s p.
  fmt_imply_t. Qed.

Lemma fmt_inj_diff {A : Set} {P s p t}  :
  format_correct s p t ->
  format_correct_inj_diff A P s p t.
  fmt_imply_t. Qed.

Lemma fmt_len_c {A : Set} {P s p t}  :
  format_correct s p t ->
  format_to_len_correct A P  s p t.
  fmt_imply_t. Qed.

(* This only happens when it already satisfy the inj_same
   And it can only produce same-length
 *)
(*
Lemma enc_len_implies_inj_diff : 
  forall {A : Set} {Pr : A -> Prop}
         (ser : Serialize A P)
         encode_len_longer ser
   format_correct_inj_diff _ _ .
Proof.
  intros. unfold Parse_T, format_correct_inj_diff. intros.
  unfold to_Parse_T in *. 
  destruct_enc.  inversion H. subst.
  clear_redu_all. clear H.
  eassert (G := CT.basic_format_inj fmt _ _ _ _ _ E).  
  exists (BA.len bf).
  intros.
(* We can have a longer buffer, and make sure that the new buffer
   aligns with bf0. 
 *)
  unfold Serialize_T.
  assert (G1 := G bf (eq_refl)).
  destruct G1. split_and.
  eassert (G2 := CT.basic_encode_len_longer fmt _ _ _ _ _ _ _ H H1).
  destruct G2.
  rewrite H0. exists x0. encode_eq.
Qed.
*)


Lemma format_correct_inj_helper : 
  forall bf b bf' pos p pos',
    EQ.equiv_b bf b pos p pos p -> 
    EQ.equiv_b bf bf' p pos' p pos' ->
    EQ.equiv_b b bf' (BProp.pos_zero) p (BProp.pos_zero) p ->
    EQ.equiv_b bf bf' pos pos' pos pos'.
Proof.
  intros.
   eapply EQ.equiv_b_append.
   - eapply EQ.equiv_b_trans.
     + apply H.
     + apply equiv_b_le_zero.
       * assert (V := EQ.equiv_b_implies_valid_pair H).
         unfold EQ.valid_pos_pair in V.  split_and.
         auto. 
       * auto. 
   - auto.
Qed.
