Require Import
          Lia
          Coq.Logic.FunctionalExtensionality
          ASN1Parser.tact. 

(* This file is to show the representation of bit string in coq. 
     Using a vector of bytes.

     This will be translate into OCaml as a BigArray object. 
 *)

Record ByteBuffer :=
  buf_con
    { buf_len : nat;
      buffer : list Byte.byte;
      length_eq : length buffer = buf_len
    }.

Fixpoint byte_buf_make (n : nat) (c : Byte.byte)
  : list Byte.byte :=
  match n with
  | 0 =>  nil 
  | S m =>  c :: byte_buf_make m c
  end.

Lemma byte_buf_make_eq_length : forall n c, length (byte_buf_make n c) = n.
Proof.
  intros. induction n; simpl; auto.
Qed.

Definition byte_make (n : nat) (c : Byte.byte) : ByteBuffer :=
  buf_con n (byte_buf_make n c) (byte_buf_make_eq_length n c).

Fixpoint byte_list_get (l : list Byte.byte) (index : nat)
  : option Byte.byte := 
  match l, index with
  | nil, _ => None
  | cons h t, 0 => Some h
  | cons h t, S m => byte_list_get t m
  end.

Require Strings.Byte.

Definition option_bind {A B : Type} (a : option A) (f : A -> option B)
  : option B :=
  match a with
  | Some a' => f a'
  | None => None
  end.

Notation "x <-opt a ;; k" := (option_bind a (fun x => k))
                               (at level 100, right associativity). 

Definition byte_get (bf : ByteBuffer) (index : nat) : option Byte.byte :=
  (byte_list_get (buffer bf) index).

Definition byte_get_nat (bf : ByteBuffer) (index : nat) : option nat := 
  b <-opt byte_get bf index ;;
  Some (Byte.to_nat b).

Notation "bf '[[' index ']]'" := (byte_get_nat bf index) (at level 100). 

Fixpoint byte_list_set (l : list Byte.byte) (index : nat) (c : Byte.byte)
  : option (list Byte.byte) :=
  match l, index with
  | nil, _ => None
  | cons h t, 0 => Some (cons c t)
  | cons h t, S m => match  byte_list_set t m c with
                   | Some l0 => Some (cons h l0)
                   | None => None
                   end
  end.

Definition byte_set (bf : ByteBuffer) (index : nat) (c : Byte.byte)
  : option (ByteBuffer) :=
  match (byte_list_set (buffer bf) index c) with
  | Some l' => Some (buf_con (length l') l' eq_refl)
  | None => None
  end.

Notation "l [[[ index <- chr ]]] " := (byte_set l index chr) (at level 110). 

(* Correctness proofs of these operations,
   We don't really need these 'proofs', because at the end of the day,
   we are extracting these byte_set, byte_get directly into OCaml. So
   I only need a plausible interface of Axioms. This part will be
   similar to the PArray part of Coq. 
 *)
Lemma byte_get_same :
  forall (i : nat) (n : nat) (c : Byte.byte),
    i < n -> byte_list_get (byte_buf_make n c) i  = Some c.
Proof.
  intros. generalize dependent i.
  induction n; intros. 
  - assert (A := PeanoNat.Nat.nlt_0_r i H).
    contradiction.
  - destruct i; simpl; auto.
    assert (G0 := PeanoNat.lt_S_n i n H). 
    apply IHn. auto. 
Qed.

Lemma byte_set_get_list :
  forall (i : nat) (bf : list Byte.byte) (c : Byte.byte),
    (i < length bf) ->
    match (byte_list_set bf i c) with
    | Some l => byte_list_get l i
    | None => None
    end = Some c.
Proof.
  intros i bf. generalize dependent i. 
  induction bf; intros; simpl in H. 
  - inversion H. 
  - destruct i; simpl; auto. 
    assert (G0 := PeanoNat.lt_S_n i (length bf) H). 
    assert (G1 := IHbf i c G0).
    destruct_match. 
    simpl.  auto. 
Qed.

Axiom byte_make_get : 
  forall (idx : nat) (n : nat) (c : Byte.byte),
    idx < n -> byte_get (byte_make n c) idx  = Some c.

Axiom byte_make_length :
  forall (n : nat) (c : Byte.byte),
    buf_len (byte_make n c) = n.

Axiom byte_set_get : forall (idx : nat) (bf bf' : ByteBuffer) (c : Byte.byte),
    byte_set bf idx c = Some bf' -> 
    byte_get bf' idx = Some c.

Axiom byte_set_get_other :
  forall (idx : nat) (bf bf' : ByteBuffer) (c : Byte.byte),
    byte_set bf idx c = Some bf' ->
    (forall idx', idx' <> idx -> 
                  byte_get bf' idx' = byte_get bf idx'). 

(* byte-set won't change the length *)
Axiom byte_set_length :
  forall (idx : nat) (bf bf' : ByteBuffer) (c : Byte.byte),
    byte_set bf idx c = Some bf' ->
    buf_len bf = buf_len bf'. 

Axiom byte_get_in_range : forall (idx : nat) (bf : ByteBuffer),
    idx < buf_len bf ->
    exists c, byte_get bf idx = Some c. 

Axiom byte_get_in_range_rev :  forall (idx : nat) (bf : ByteBuffer) (c : Byte.byte),
    byte_get bf idx = Some c ->
    idx < buf_len bf.

Axiom byte_get_out_range : forall (idx : nat) (bf : ByteBuffer),
    buf_len bf <= idx -> 
    byte_get bf idx = None.
    
Axiom byte_set_in_range : forall (idx : nat) (bf : ByteBuffer) (c : Byte.byte),
    idx < buf_len bf ->
    exists bf', byte_set bf idx c = Some bf'. 

Axiom byte_set_out_range : forall (idx : nat) (bf : ByteBuffer) (c : Byte.byte),
    buf_len bf <= idx ->
    byte_set bf idx c = None. 

(* Some property with equiv. *)


(* byte_pos : the position of the byte that we should operate on, 
     nboff    : the bit difference between the 'byte' and the beginning of 
                the actual byte string,
     nbits    : the bit difference between the 'byte' and the end of the 
                byte string.
     
     The following is an example: 

     |--------|---xxxxx|xxxxxxxx|xx------|
              ^   ^                ^
              p   nboff            nbits
     
     pos_cons 1 3 18
     
     However, it does not have to be normalized, therefore it could be like 
     pos_cons 0 11 26
     
     We can also see that the length of the bit-string represented is 
     nbits - nboff. 
 

*)


Definition byte_to_bit_list (b : Byte.byte) : list bool
  := match (Byte.to_bits b) with
     | (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7)))))))
       => b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: nil
     end.

Fixpoint bytes_to_bits (bytes : list Byte.byte) : list bool
  := match bytes with
     | nil => nil
     | cons h t => app (byte_to_bit_list h) (bytes_to_bits t)
     end.

Import Lists.List.

Fixpoint bit_list_to_byte (bf : list bool) : option (list Byte.byte) :=
  match bf with
  | nil => Some nil
  | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: t =>
      match (bit_list_to_byte t) with
      | Some (bts) => 
          Some (Byte.of_bits (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) :: bts)
      | None => None
      end
  | _ => None
  end.

Inductive ByteIdx :=
| I0
| I1
| I2
| I3
| I4
| I5
| I6
| I7.

Definition ByteIdx_to_nat :=
  fun bi =>
    match bi with
    | I0 => 0
    | I1 => 1
    | I2 => 2
    | I3 => 3
    | I4 => 4
    | I5 => 5
    | I6 => 6
    | I7 => 7
    end.


Definition nat_to_ByteIdx  (n : nat)  : ByteIdx := 
  match n with
  | 0 => I0
  | 1 => I1
  | 2 => I2
  | 3 => I3
  | 4 => I4
  | 5 => I5
  | 6 => I6
  | 7 => I7
  | _ => I7
  end.

Definition byteidx_of_to_nat : forall n : nat,
    n <= 7 ->
    ByteIdx_to_nat (nat_to_ByteIdx n) = n.
Proof.
  intros;
    destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  lia. 
Qed.


Record BytePos :=
  pos_con
    { byte_pos : nat;
      byte_off : ByteIdx
    }.

Require Import ASN1Parser.AbsArray.

Module BA <: Array.

  Definition Buffer := ByteBuffer.

  Definition len : Buffer -> nat :=
    fun bf => buf_len bf * 8.

  Definition byte_len : Buffer -> nat := buf_len.
  
  Definition make : nat -> Buffer :=
    fun z =>
      let n := (Nat.div z 8 + 1) in
      (byte_make z Byte.x00).
  
  Definition Pos := BytePos. 

  Definition to_nat : Pos -> nat :=
    fun pos => (byte_pos pos) * 8 + (ByteIdx_to_nat (byte_off pos)). 

  Definition of_nat : nat -> Pos :=
    fun n => pos_con (Nat.div n 8)  (nat_to_ByteIdx (Nat.modulo n 8)).
End BA.

Module BProp <: ArrayProps BA.
  
  Lemma make_len_le : forall n, n <= BA.len (BA.make n).
    intros. unfold BA.len, BA.make. 
    induction n.
    - simpl. auto.
    - simpl. lia. 
  Qed.

  (* Here, the problem is that during extraction, all of these
     functions will be extracted. However, they are not needed 
     when we extract them. So we should rearrange it such that 
     they would not interfere with the problem.
   *)
  Definition to_bits : BA.Buffer -> list bool := 
    fun bf => bytes_to_bits (buffer bf). 

  Definition of_bits : list bool -> option BA.Buffer :=
    fun bf =>
      match (bit_list_to_byte bf) with
      | Some bf' => Some (buf_con (length bf') bf' eq_refl)
      | None => None
      end.
  
  Lemma to_bits_correct : forall bf : BA.Buffer, of_bits (to_bits bf) = Some bf.
  Proof.
    intros. unfold of_bits, to_bits.
    destruct bf.  generalize dependent buf_len0.
    induction buffer0;  simpl in *; intros. 
    - subst. auto.  
    - unfold byte_to_bit_list.
      destruct buf_len0; inversion length_eq0.
      assert (G := IHbuffer0 buf_len0 H0).
      destruct_match. inversion G. subst. 
      destruct a; simpl; rewrite E; simpl; f_equal; f_equal;
        apply  ProofIrrelevance.proof_irrelevance.
  Qed.
  
  Lemma to_bits_len : forall (bf : BA.Buffer), length (to_bits bf) = BA.len bf.
  Proof.
    intros. unfold to_bits. destruct bf. generalize dependent buf_len0. 
    induction buffer0; intros; simpl in *; unfold  BA.len, BitRep.buf_len  in *.
    - rewrite <- length_eq0. auto.
    - destruct buf_len0; inversion length_eq0.
      assert (G := IHbuffer0 buf_len0 H0).
      subst. 
      destruct a; simpl; rewrite G; reflexivity.
  Qed.

  Definition le_pos : BA.Pos -> BA.Pos -> Prop :=
    fun p1 p2 => BA.to_nat p1 <= BA.to_nat p2.

  Definition pos_to_len : BA.Pos -> BA.Pos -> nat :=
    fun p1 p2 => BA.to_nat p2 - BA.to_nat p1. 
  
  Definition valid_pos_pair : BA.Buffer -> BA.Pos -> BA.Pos -> Prop :=
    fun bf p1 p2 => 
      (BA.to_nat p1 <= BA.to_nat p2) /\ (BA.to_nat p2 <= BA.len bf).

  Definition pos_zero : BA.Pos :=
    pos_con 0 I0.

  (* This does not look good *)
  Definition pos_end : BA.Buffer -> BA.Pos := 
    fun bf =>
      pos_con (buf_len bf) I0.


  Definition valid_pos_pairb : BA.Buffer -> BA.Pos -> BA.Pos -> bool :=
    fun bf p1 p2 =>
      andb (Nat.leb (BA.to_nat p1) (BA.to_nat p2)) (Nat.leb (BA.to_nat p2) (BA.len bf)).

  (* Do we have to prove it in this way?? *)
  Lemma of_to_nat : forall (pos : BA.Pos), BA.of_nat (BA.to_nat pos) = pos.
  Proof.
    intros. destruct pos. unfold BA.of_nat, BA.to_nat.
    unfold byte_pos, byte_off.  
    induction byte_pos0. 
    - f_equal; destruct byte_off0; simpl; reflexivity.
    - assert (G1 := f_equal byte_pos IHbyte_pos0).
      assert (G2 := f_equal byte_off IHbyte_pos0). 
      unfold byte_pos, byte_off in *.
      assert (S byte_pos0 * 8 + ByteIdx_to_nat byte_off0 =
                (byte_pos0 * 8 + ByteIdx_to_nat byte_off0) + 1 * 8).
      { lia. }
      f_equal.
      + rewrite H. 
        rewrite PeanoNat.Nat.div_add; try lia.
      + rewrite H.
        rewrite PeanoNat.Nat.Div0.mod_add.
        apply G2.
  Qed.
  
  Lemma to_of_nat : forall (n : nat), BA.to_nat (BA.of_nat n) = n.
  Proof.
    intros. unfold BA.of_nat, BA.to_nat. 
    unfold byte_pos, byte_off.
    assert (Nat.modulo n 8 <= 7). 
    { assert  (Nat.modulo n 8 < 8).
      - apply PeanoNat.Nat.mod_bound_pos; lia.
      - lia. }
    rewrite byteidx_of_to_nat; auto.
    assert (G := PeanoNat.Nat.div_mod_eq n 8).
    lia. 
  Qed.
  
  Lemma pos_zero_equals_zero : BA.to_nat (pos_zero) = 0.
  Proof.
    unfold BA.to_nat, pos_zero.
    simpl. reflexivity.
  Qed.
  
  Lemma pos_end_equals_len : forall (bf : BA.Buffer),
      BA.to_nat (pos_end bf) = BA.len bf.
  Proof.
    intros. unfold BA.to_nat. simpl. 
    unfold BA.len. 
    auto.
  Qed.
  
  Lemma len_equals_pos_end : forall {bf1 bf2 : BA.Buffer},
      BA.len bf1 = BA.len bf2 -> pos_end bf1 = pos_end bf2.
  Proof.
    intros.
    unfold pos_end, BA.len in *. f_equal.
    lia.
  Qed.

  Lemma pos_zero_le_all : forall (pos : BA.Pos), le_pos pos_zero pos.
  Proof.
    intros. unfold le_pos, BA.to_nat, pos_zero.
    simpl. apply PeanoNat.Nat.le_0_l.
  Qed.

  Lemma le_pos_refl : forall (pos : BA.Pos), le_pos pos pos.
  Proof.
    intros.  unfold le_pos.  auto.
  Qed.

  Lemma le_pos_trans :  forall (p1 p2 p3 : BA.Pos),
      le_pos p1 p2 -> le_pos p2 p3 -> le_pos p1 p3.
  Proof.
    intros. unfold le_pos in *. lia.
  Qed.

End BProp.
