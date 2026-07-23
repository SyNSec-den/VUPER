Require Import
          ASN1Parser.tact
          Lia.

Module Type Array.
  Parameter Buffer : Type.
  
  Parameter len : Buffer -> nat.

  (* Here, byte len returns the length of the buffer in bytes. *)  
  Parameter byte_len : Buffer -> nat. 

  (*Axiom byte_len_size_eight : forall (bf : Buffer), byte_len bf * 8 = len bf.*) 
  
  (* Make function takes in a nat, say n, as an input for length, 
     and outputs a Buffer of length n.
   *)
  Parameter make : nat -> Buffer.

  Parameter Pos : Type.

  Parameter to_nat : Pos -> nat. 
  Parameter of_nat : nat -> Pos.

End Array.

Fixpoint list_bool_eqb (l1 l2 : list bool) : bool :=
  match l1, l2 with
  | cons h1 t1, cons h2 t2 => andb (Bool.eqb h1 h2) (list_bool_eqb t1 t2)
  | cons _ _, nil => false
  | nil, cons _ _ => false
  | nil, nil => true
  end.


(* Here, props mean properties *)
Module Type ArrayProps (B : Array).
  Axiom make_len_le : forall n, n <= B.len (B.make n). 

  Parameter to_bits : B.Buffer -> list bool.

  Parameter of_bits : list bool -> option B.Buffer.

  Axiom to_bits_correct : forall bf : B.Buffer, of_bits (to_bits bf) = Some bf.

  Axiom to_bits_len : forall (bf : B.Buffer), length (to_bits bf) = B.len bf. 

   (* Question : Is it better to use Pos or just use Nat? 
     
     For the bool list version, Pos is just nat. However, 
     for the byte list version, Pos is like (nat * byte_pos), 
     where byte_pos can be defined like 
     Inductive BytePos := 
     | I0 | I1 | ... | I7. 
     
     Two things can be done here, 
     1. Just use Pos for comparsion, 
     2. Use nat for comparsion with some correspondance 
        between Pos and nat. It would be easy to convert 
        Pos to nat. But not that trivial vice versa. 

   *)
  
  Definition le_pos : B.Pos -> B.Pos -> Prop :=
    fun p1 p2 => B.to_nat p1 <= B.to_nat p2.

  Definition pos_to_len : B.Pos -> B.Pos -> nat :=
    fun p1 p2 => B.to_nat p2 - B.to_nat p1. 
  
  Parameter pos_zero : B.Pos.
  Parameter pos_end : B.Buffer -> B.Pos.

  Axiom of_to_nat : forall (pos : B.Pos), B.of_nat (B.to_nat pos) = pos.

  Axiom to_of_nat : forall (n : nat), B.to_nat (B.of_nat n) = n.
  
  Axiom pos_zero_equals_zero : B.to_nat (pos_zero) = 0.
  
  Axiom pos_end_equals_len : forall (bf : B.Buffer),
      B.to_nat (pos_end bf) = B.len bf.

  Axiom len_equals_pos_end : forall {bf1 bf2 : B.Buffer},
      B.len bf1 = B.len bf2 -> pos_end bf1 = pos_end bf2. 

  Axiom pos_zero_le_all : forall (pos : B.Pos), le_pos pos_zero pos.

  Axiom le_pos_refl : forall (pos: B.Pos), le_pos pos pos.

  Axiom le_pos_trans : forall {p1 p2 p3 : B.Pos},
      le_pos p1 p2 -> le_pos p2 p3 -> le_pos p1 p3. 
  
End ArrayProps.


Definition slice (ls : list bool) (a b : nat)
  : list bool
  := List.skipn a (List.firstn b ls).


Lemma slice_nil : forall (p1 p1' : nat), slice nil p1 p1' = nil.
Proof.
  intros. unfold slice. rewrite List.firstn_nil, List.skipn_nil.
  reflexivity.
Qed.

Lemma slice_app : forall (l : list bool) (b : bool) (p1 p1' : nat),
    slice (b :: l) (S p1) (S p1') = slice l p1 p1'.
Proof.
  intros. unfold slice. 
  rewrite List.firstn_cons, List.skipn_cons. auto.
Qed.

Lemma slice_smaller  : forall {l : list bool} {p1 p1' p0 p0' : nat},
    p1 <= p0 -> p0 <= p0' -> p0' <= p1' -> p1' <= length l ->
    slice l p0 p0' = slice (slice l p1 p1') (p0 - p1) (p0' - p1).
Proof.
  intro l. intro p1. generalize dependent l.   induction p1.
  - intros. destruct p0' eqn:E1.
    + destruct p0; try lia.
      simpl. unfold slice. rewrite List.firstn_O. auto.
    + unfold slice. rewrite List.skipn_O. f_equal; try lia.
      rewrite List.firstn_firstn.
      f_equal. lia. 
  - intros. destruct p0; try lia. destruct p0'; try lia. destruct p1'; try lia.
    destruct l. simpl in H2; try lia.
    repeat rewrite slice_app. simpl.  apply IHp1; simpl in *; try lia. 
Qed.

Lemma slice_implies_len_eq : forall {bf1 bf2 : list bool} {p1 p1' p2 p2' : nat},
    p1 <= p1' -> p1' <= length bf1 ->
    p2 <= p2' -> p2' <= length bf2 -> 
    slice bf1 p1 p1' = slice bf2 p2 p2' -> p1' - p1 = p2' - p2.
Proof.
  intros.
  unfold slice in *.
  assert (G := f_equal (length (A:=bool)) H3).
  repeat rewrite List.length_skipn in G. 
  repeat rewrite List.length_firstn in G. 
  rewrite min_l in G; try lia. 
Qed.

(* to prove this, we just need to show that slicing something within a slice
       it the same as slicing it from the original list. 
 *)
Lemma slice_equiv :
  forall {bf1 bf2 : list bool} {p1 p1' p2 p2' p1_0 p1_0' p2_0 p2_0' : nat},
    p1 <= p1_0 -> p1_0 <= p1_0' -> p1_0' <= p1' -> p1' <= length bf1 -> 
    p2 <= p2_0 -> p2_0 <= p2_0' -> p2_0' <= p2' -> p2' <= length bf2 ->
    p1_0 - p1 = p2_0 - p2 -> p1' - p1_0' = p2' - p2_0' ->
    slice bf1 p1 p1' = slice bf2 p2 p2' ->
    slice bf1 p1_0 p1_0' = slice bf2 p2_0 p2_0'.
Proof. 
  intros. 
  - rewrite (slice_smaller H H0 H1 H2).
    rewrite (slice_smaller H3 H4 H5 H6).
    f_equal; auto.
    assert (p1 <= p1'). { lia. }
    assert (p2 <= p2'). { lia. }
    assert (G := slice_implies_len_eq H10 H2 H11 H6 H9).
    lia.
Qed.

Lemma slice_same : forall {bf : list bool} {n : nat},
    n <= length bf -> slice bf n n = nil.
Proof.
  intros. unfold slice.
  assert (n = length (List.firstn n bf)).
  { rewrite List.length_firstn. lia. }
  rewrite H0 at 1. 
  rewrite List.skipn_all.
  auto.
Qed.

Lemma slice_from_zero : forall {bf : list bool} {n : nat},
    n <= length bf -> slice bf 0 n = List.firstn n bf.
Proof.
  intros. unfold slice. rewrite List.skipn_O.  auto.  Qed.

(* we should use one  *)
Lemma slice_append : forall {bf : list bool}  {p p' pm : nat} {l1 l2 : list bool},
    p <= pm -> pm <= p' -> p'  <= length bf  ->
    slice bf p pm = l1 ->
    slice bf pm p' = l2 ->
    slice bf p p' = app l1 l2.
Proof.
  intros bf p p'.  generalize dependent p. generalize dependent bf. 
  induction p'.
  - intros.  destruct pm; try lia.
    destruct p; try lia.
    rewrite slice_same in *; auto.
    rewrite <- H2, <- H3.  auto.
  - intros. destruct bf; simpl in H1; try lia.
    destruct pm.
    + destruct p; try lia. 
      rewrite slice_same in H2; try lia. rewrite <- H2.
      rewrite List.app_nil_l. auto.
    + rewrite  slice_app in H3.  
      destruct p.
      * rewrite slice_from_zero in *; simpl; try lia.
        rewrite slice_from_zero in H2; simpl; try lia. 
        rewrite List.firstn_cons in *. 
        destruct l1; inversion H2. subst.
        rewrite <- List.app_comm_cons. f_equal.
        repeat rewrite <- slice_from_zero; try lia.
        eapply (IHp' bf 0 pm); try lia; auto.
      * rewrite slice_app in *.
        eapply (IHp' bf p pm); try lia; auto.
Qed.

(* In order for this lemma to hold, we first need to make sure that 
     the slice is not out of bound. 
 *)
Lemma slice_append_helper :
  forall {bf1 bf2 : list bool}  {p1 p1' p1m p2 p2' p2m: nat},
    p1 <= p1m -> p1m <= p1' -> p1'  <= length bf1  ->
    p2 <= p2m -> p2m <= p2' -> p2' <= length bf2 -> 
    slice bf1 p1 p1m = slice bf2 p2 p2m ->
    slice bf1 p1m p1' = slice bf2 p2m p2' -> 
    slice bf1 p1 p1' = slice bf2 p2 p2'.
Proof. 
  intros.
  assert (G1 := slice_append H H0 H1 H5 H6).
  assert (G2 := slice_append H2 H3 H4 (eq_refl (slice bf2 p2 p2m))
                  (eq_refl (slice bf2 p2m p2'))). 
  rewrite G1, G2. auto.
Qed.


Module Type EquivBits (B : Array)  (BProp : ArrayProps B).

  Definition valid_pos_pair : B.Buffer -> B.Pos -> B.Pos -> Prop :=
    fun bf p1 p2 => 
      (B.to_nat p1 <= B.to_nat p2) /\ (B.to_nat p2 <= B.len bf).

  Definition valid_pos_pairb : B.Buffer -> B.Pos -> B.Pos -> bool :=
    fun bf p1 p2 =>
      andb (Nat.leb (B.to_nat p1) (B.to_nat p2))
        (Nat.leb (B.to_nat p2) (B.len bf)).


  Axiom valid_pos_pair_dec : forall (bf : B.Buffer) (pos pos' : B.Pos),
      valid_pos_pair bf pos pos' <-> valid_pos_pairb bf pos pos' = true.
  
  Parameter to_bool_list : B.Buffer -> B.Pos -> B.Pos -> option (list bool).

  Parameter equiv_b : forall  (bf1 bf2 : B.Buffer) (p1 p1' p2 p2' : B.Pos), Prop. 
  
  Axiom equiv_b_trans : forall  {bf1 bf2 bf3: B.Buffer} {p1 p1' p2 p2' p3 p3': B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      equiv_b bf2 bf3 p2 p2' p3 p3' ->
      equiv_b bf1 bf3 p1 p1' p3 p3'.

  Axiom equiv_b_symm : forall  {bf1 bf2 : B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      equiv_b bf2 bf1 p2 p2' p1 p1'.

  Axiom equiv_b_refl : forall  {bf1 : B.Buffer} {p1 p1' : B.Pos},
      valid_pos_pair bf1 p1 p1' -> 
      equiv_b bf1 bf1 p1 p1' p1 p1'.

  Axiom equiv_b_nil : forall (bf1 bf2 : B.Buffer) {p1 p1' p2 p2' : B.Pos},
      B.to_nat p1 <= B.len bf1 ->
      B.to_nat p2 <= B.len bf2 -> 
      B.to_nat p1 = B.to_nat p1' ->
      B.to_nat p2 = B.to_nat p2' ->
      equiv_b bf1 bf2 p1 p1' p2 p2'.  
  
  Axiom equiv_b_le : forall (bf1 bf2 : B.Buffer) (p1 p1' p2 p2': B.Pos) 
                            (p1_0 p1_0' p2_0 p2_0' : B.Pos),
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      BProp.le_pos p1 p1_0 -> BProp.le_pos p2 p2_0 -> BProp.le_pos p1_0' p1' -> BProp.le_pos p2_0' p2' ->
      BProp.le_pos p1_0 p1_0' -> BProp.le_pos p2_0 p2_0' -> 
      BProp.pos_to_len p1 p1_0 = BProp.pos_to_len p2 p2_0 ->
      BProp.pos_to_len p1_0' p1' = BProp.pos_to_len p2_0' p2' -> 
      equiv_b bf1 bf2 p1_0 p1_0' p2_0 p2_0'.

  Axiom equiv_b_same_pos : forall {bf bf' : B.Buffer} {p1 p1' p0 p0' : B.Pos},
      equiv_b bf bf' p1 p1' p1 p1' ->
      BProp.le_pos p1 p0 -> BProp.le_pos p0' p1' ->  BProp.le_pos p0 p0' ->
      equiv_b bf bf' p0 p0' p0 p0'.
  
  (* New theorems about the equiv_b, so when we are seeing some equiv_b in some 
     Range pos1 pos2, then it should also work for smaller ranges. 

     say 
     |--------|--------|--------|
       ^    ^       ^       ^
       p1   p1'     p2'     p2
     
     The thing we want is that if it is equiv through p1 to p2, then 
     it shall be the same through p1' to p2' as well. 
     
     The biggest difference is that our approach is very fine grained that 
     is correct down to bit level. 
   *)

  Axiom equiv_b_implies_valid_pair : forall {bf1 bf2 : B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      valid_pos_pair bf1 p1 p1' /\ valid_pos_pair bf2 p2 p2'. 

  Axiom equiv_b_eq_len : forall {bf1 bf2 : B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' -> 
      BProp.pos_to_len p1 p1' = BProp.pos_to_len p2 p2'.

  Axiom equiv_b_split  : forall {bf1 bf2: B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' -> forall (p : B.Pos),
        BProp.le_pos p1 p -> BProp.le_pos p p1' ->
        exists (p0 : B.Pos), BProp.le_pos p2 p0 /\ BProp.le_pos p0 p2' /\
                             equiv_b bf1 bf2 p1 p p2 p0 /\
                             equiv_b bf1 bf2 p p1' p0 p2'.

  Axiom equiv_b_append : forall {bf1 bf2: B.Buffer} {p1 p1' p1m p2 p2' p2m: B.Pos},
      equiv_b bf1 bf2 p1 p1m p2 p2m ->
      equiv_b bf1 bf2 p1m p1' p2m p2' ->
      equiv_b bf1 bf2 p1 p1' p2 p2'.
    
End EquivBits.

Module EquivBits_Impl (B : Array) (BProp : ArrayProps B)
  <: EquivBits B BProp.

  Definition valid_pos_pair : B.Buffer -> B.Pos -> B.Pos -> Prop :=
    fun bf p1 p2 => 
      (B.to_nat p1 <= B.to_nat p2) /\ (B.to_nat p2 <= B.len bf).

  Definition valid_pos_pairb : B.Buffer -> B.Pos -> B.Pos -> bool :=
    fun bf p1 p2 =>
      andb (Nat.leb (B.to_nat p1) (B.to_nat p2))
        (Nat.leb (B.to_nat p2) (B.len bf)).

  Lemma valid_pos_pair_dec : forall (bf : B.Buffer) (pos pos' : B.Pos),
      valid_pos_pair bf pos pos' <-> valid_pos_pairb bf pos pos' = true.
  Proof.
    intros. split; unfold valid_pos_pair, valid_pos_pairb; intros. 
    - destruct H. rewrite <- PeanoNat.Nat.leb_le  in H, H0.
      rewrite H, H0. auto.
    - repeat rewrite <- PeanoNat.Nat.leb_le. 
      apply Bool.andb_true_iff. auto.   
  Qed.
    
  Definition to_bool_list : B.Buffer -> B.Pos -> B.Pos -> option (list bool) :=
    fun bf p1 p2 =>
      if valid_pos_pairb bf p1 p2 then
        Some (slice (BProp.to_bits bf) (B.to_nat p1) (B.to_nat p2))
      else
        None.

  Definition equiv_b  (bf1 bf2 : B.Buffer) (p1 p1' p2 p2' : B.Pos) : Prop :=
    match (to_bool_list bf1 p1 p1'), (to_bool_list bf2 p2 p2') with
    | Some l1, Some l2 =>  l1 = l2
    | None , _ => False
    | _, None => False
    end.

  Lemma equiv_b_trans : forall {bf1 bf2 bf3: B.Buffer} {p1 p1' p2 p2' p3 p3': B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      equiv_b bf2 bf3 p2 p2' p3 p3' ->
      equiv_b bf1 bf3 p1 p1' p3 p3'.
  Proof.
    intros. unfold equiv_b in *.
    destruct_match_false. 
    auto.
  Qed.

  Lemma equiv_b_symm : forall {bf1 bf2 : B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      equiv_b bf2 bf1 p2 p2' p1 p1'.
  Proof.
    intros. unfold equiv_b in *.
    destruct_match_false.
    auto.
  Qed.  

  Lemma equiv_b_refl : forall  {bf1 : B.Buffer} {p1 p1' : B.Pos},
      valid_pos_pair bf1 p1 p1' -> 
      equiv_b bf1 bf1 p1 p1' p1 p1'.  
  Proof.
    intros. unfold equiv_b in *.
    destruct (to_bool_list bf1 p1 p1') eqn:E; auto. 
    unfold to_bool_list in E.
    destruct_if_in. 
    unfold valid_pos_pair, valid_pos_pairb in *.
    destruct H. 
    rewrite <- PeanoNat.Nat.leb_le in H, H0. 
    rewrite H, H0 in E0. simpl in E0.  inversion E0. 
  Qed.

  Lemma equiv_b_nil : forall (bf1 bf2 : B.Buffer) {p1 p1' p2 p2' : B.Pos},
      B.to_nat p1 <= B.len bf1 ->
      B.to_nat p2 <= B.len bf2 -> 
      B.to_nat p1 = B.to_nat p1' ->
      B.to_nat p2 = B.to_nat p2' ->
      equiv_b bf1 bf2 p1 p1' p2 p2'.  
  Proof.
    intros. unfold equiv_b, to_bool_list. 
    (* Here, we utilize slice two same bits would result
       in nil. 
     *)
    assert (V1 : valid_pos_pair bf1 p1 p1').
    { unfold valid_pos_pair.  lia. } 
    assert (V2 : valid_pos_pair bf2 p2 p2').
    { unfold valid_pos_pair.  lia. } 
    rewrite valid_pos_pair_dec in V1, V2.
    rewrite V1, V2.
    rewrite <- BProp.to_bits_len in H, H0. 
    assert (G1 := slice_same H).
    assert (G2 := slice_same H0). 
    rewrite <- H1, <- H2, G1, G2. auto. 
  Qed.
  
  Lemma valid_pos_pair_le : forall {bf : B.Buffer} {p1 p1' p1_0 p1_0' : B.Pos},
      BProp.le_pos p1_0 p1_0' ->  BProp.le_pos p1_0' p1' ->
      valid_pos_pair bf p1 p1' -> valid_pos_pair bf p1_0 p1_0'.
  Proof.
    intros.
    unfold valid_pos_pair in *. destruct H1. 
    split; auto. 
    eapply PeanoNat.Nat.le_trans; eauto.
  Qed.  

   Lemma equiv_b_le : forall {bf1 bf2 : B.Buffer} {p1 p1' p2 p2': B.Pos} 
                            {p1_0 p1_0' p2_0 p2_0' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      BProp.le_pos p1 p1_0 -> BProp.le_pos p2 p2_0 -> BProp.le_pos p1_0' p1' -> BProp.le_pos p2_0' p2' ->
      BProp.le_pos p1_0 p1_0' -> BProp.le_pos p2_0 p2_0' -> 
      BProp.pos_to_len p1 p1_0 = BProp.pos_to_len p2 p2_0 ->
      BProp.pos_to_len p1_0' p1' = BProp.pos_to_len p2_0' p2' -> 
      equiv_b bf1 bf2 p1_0 p1_0' p2_0 p2_0'.
  Proof.
    intros. 
    unfold equiv_b in *.
    destruct_match_false. 
    unfold BProp.le_pos, BProp.pos_to_len, to_bool_list in *.
    repeat destruct_if_in. 
    rewrite <- valid_pos_pair_dec in E1, E2. 
    assert (G := valid_pos_pair_le H4 H2 E2).
    assert (G1 := valid_pos_pair_le H5 H3 E1).
    assert (G' := G). destruct G'.
    assert (G1' := G1). destruct G1'.
    rewrite valid_pos_pair_dec in G, G1.
    rewrite G, G1.
    (* Here, proving it using slice is very implementation unique. 
       However, we could potentially reuse 
     *)
    destruct E1. destruct E2.
    rewrite <- BProp.to_bits_len in *. 
    eapply (slice_equiv H0 H4 H2 H15  H1 H10 H3 H13); auto.
  Qed.

  Corollary equiv_b_same_pos : forall {bf bf' : B.Buffer} {p1 p1' p0 p0' : B.Pos},
      equiv_b bf bf' p1 p1' p1 p1' ->
      BProp.le_pos p1 p0 -> BProp.le_pos p0' p1' -> BProp.le_pos p0 p0' ->
      equiv_b bf bf' p0 p0' p0 p0'.
  Proof.
    intros. eapply equiv_b_le; auto; try apply H; auto. 
  Qed.

  Lemma equiv_b_implies_valid_pair : forall {bf1 bf2 : B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' ->
      valid_pos_pair bf1 p1 p1' /\ valid_pos_pair bf2 p2 p2'. 
  Proof.
    intros. unfold equiv_b in *.
    destruct_match_false. 
    unfold to_bool_list in *.
    repeat destruct_if_in. 
    rewrite <- valid_pos_pair_dec in E1, E2.
    auto.
  Qed.

    Lemma equiv_b_eq_len : forall {bf1 bf2 : B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' -> 
      BProp.pos_to_len p1 p1' = BProp.pos_to_len p2 p2'.
  Proof.
    intros.
    unfold equiv_b in H.
    destruct_match_false. 
    unfold to_bool_list in *.
    repeat destruct_if_in. 
    inversion E. 
    rewrite <- valid_pos_pair_dec in E1, E2.
    unfold BProp.pos_to_len.
    destruct E1, E2. rewrite <- BProp.to_bits_len in *.
    eapply slice_implies_len_eq; auto.
    - apply H4. 
    - apply H2.
    - auto.
  Qed.

  Lemma equiv_b_split : forall {bf1 bf2: B.Buffer} {p1 p1' p2 p2' : B.Pos},
      equiv_b bf1 bf2 p1 p1' p2 p2' -> forall (p : B.Pos),
        BProp.le_pos p1 p -> BProp.le_pos p p1' ->
        exists (p0 : B.Pos), BProp.le_pos p2 p0 /\ BProp.le_pos p0 p2' /\
                                 equiv_b bf1 bf2 p1 p p2 p0 /\
                                 equiv_b bf1 bf2 p p1' p0 p2'.
  Proof.
    intros.
    exists (B.of_nat ((B.to_nat p2) + ((B.to_nat p) - (B.to_nat p1)))).
    unfold BProp.le_pos in *.
    assert (G := H). apply equiv_b_implies_valid_pair in G.
    assert (G1 := H). apply equiv_b_eq_len in G1. 
    unfold valid_pos_pair in G. unfold BProp.pos_to_len in G1.
    rewrite BProp .to_of_nat in *.  
    repeat split; try lia;
      apply  (equiv_b_le H); unfold BProp.le_pos, BProp.pos_to_len; auto;
      try rewrite BProp.to_of_nat; try lia.
  Qed.

  Lemma equiv_b_append :  forall {bf1 bf2: B.Buffer} {p1 p1' p1m p2 p2' p2m: B.Pos},
      equiv_b bf1 bf2 p1 p1m p2 p2m ->
      equiv_b bf1 bf2 p1m p1' p2m p2' ->
      equiv_b bf1 bf2 p1 p1' p2 p2'.
  Proof.
    intros. unfold equiv_b in *. 
    destruct_match_false. 
    unfold to_bool_list in *.
    repeat destruct_if_in.
    repeat destruct_if_goal; rewrite <- valid_pos_pair_dec in *;
      unfold valid_pos_pair in *; split_and; try rewrite <- BProp.to_bits_len in *. 
    - eapply (slice_append_helper H11); try assumption.
      apply H9. auto. auto. auto.
    - assert (valid_pos_pairb bf2 p2 p2' = true).
      { rewrite <- valid_pos_pair_dec. split; try lia. 
          rewrite <- BProp.to_bits_len. lia. }
      rewrite H11 in E8. discriminate .
    - assert (valid_pos_pairb bf1 p1 p1' = true).
      { rewrite <- valid_pos_pair_dec. split; try lia.
          rewrite <- BProp.to_bits_len. lia. }
      rewrite H9 in E7.  discriminate. 
  Qed.

End EquivBits_Impl.

