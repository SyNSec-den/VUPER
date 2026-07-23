Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Array.BitRep
  ASN1Parser.Array.ByteBuffer.

Require Import Lia.

Require Import ASN1Parser.tact.

Module BPP.

  (* To prove this non-inter property, we need to show that
     First, 
     we must know there are several cases, first we can prove or have
     some lemmas about byte_set,
     
     basically, byte_set would not change anything before and after
     the byte. This should be an axiom? or a theorem? because either
     way, we will map byte_set to some function in OCaml. Therefore,
     we implicitly assume it would behave exactly like it in Coq.
     The proofs are not that important*.


     say
     |----|----|----|----|

     0    1    2    3    4

     if we set 2, then 0 - 2, (2+1) - end should not change.

     Axiom byte_set_get_other

     Then we have to think about byte-get and byte-set and
     their relation with EQ.equiv_b
   *)
  Axiom byte_get_equiv_b :
    forall (bf : ByteBuffer) (idx : nat) (c : Byte.byte),
      byte_get bf idx = Some c -> 
      (EQ.equiv_b bf (byte_make 1 c) (pos_con idx I0)
         (pos_con (idx + 1) I0) (pos_con 0 I0) (pos_con 1 I0)).
  
  Axiom equiv_b_byte_get :
    forall (bf : ByteBuffer) (idx : nat) (c : Byte.byte),
      (EQ.equiv_b bf (byte_make 1 c) (pos_con idx I0)
         (pos_con (idx + 1) I0) (pos_con 0 I0) (pos_con 1 I0)) ->
      byte_get bf idx = Some c.
  
  Lemma byte_set_equiv : 
    forall (bf bf' : ByteBuffer) (idx : nat) (c : Byte.byte),
      byte_set bf idx c = Some bf' -> 
      (EQ.equiv_b bf' (byte_make 1 c) (pos_con idx I0)
         (pos_con (idx + 1) I0) (pos_con 0 I0) (pos_con 1 I0)).
  Proof.
    intros. 
    assert (G := byte_set_get _ _ _ _ H).
    assert (G1 := byte_get_equiv_b _ _ _ G).
    apply G1.
  Qed.
      
  (* We should have some lemmas about shiftl, and Nat.lor,
     mask_bits. Here, mask_bits will a with nbt bits

     Here, when it is writing to a specific byte, the
     important part is we need to show that it only changes
     the byte from [offset, offset + n).

     b0 (n0 < 256).

     b1 = (Nat.lor (mask_bits (8 - off + n)) n0)
         (Nat.shiftl a (8 - off + n))))

     b0 and b1 are equal from [0, off), [off + n, 8).

     This theorem can be reused. For other proofs.
     But the question is the interface between this byte
     and equiv_b.

     We can have a notion of 'one-byte-difference'. So some
     two buffers only differ by one-byte. 
   *)
  Definition diff_by_one_byte (bf bf' : ByteBuffer) (index : nat) :=
    EQ.equiv_b bf bf'
      BProp.pos_zero (pos_con index I0)
      BProp.pos_zero (pos_con index I0) /\
      EQ.equiv_b bf bf'
        (pos_con (index + 1) I0) (BProp.pos_end bf)
        (pos_con (index + 1) I0) (BProp.pos_end bf').

  Lemma one_byte_equiv (bf bf' : ByteBuffer)
    (len_eq : buf_len bf = buf_len bf') :
    forall idx, (idx < buf_len bf) ->
                byte_get bf idx = byte_get bf' idx ->
                EQ.equiv_b bf bf'
                  (pos_con idx I0) (pos_con (idx + 1) I0)
                  (pos_con idx I0) (pos_con (idx + 1) I0).
  Proof. 
    intros. 
    destruct (byte_get_in_range _ _ H) as [c G].
    rewrite len_eq in H. 
    destruct (byte_get_in_range _ _ H) as [c1 G1].
    rewrite G, G1 in H0.
    inversion H0.  subst.
    assert (F1 := byte_get_equiv_b _ _ _ G).
    assert (F2 := byte_get_equiv_b _ _ _ G1).
    eapply EQ.equiv_b_trans.
    - apply F1.
    - apply EQ.equiv_b_symm.
      apply F2.
  Qed.

  (* Here, lower bound le upper bound *)
  Lemma several_byte_equiv_b  (bf bf' : ByteBuffer)
    (len_eq : buf_len bf = buf_len bf') (lb ub : nat) 
    (lb_ge0 : 0 <= lb)
    (lb_le_ub : lb <= ub)
    (ub_le_len : ub <= buf_len bf) :
    (forall idx, (lb <= idx) -> (idx < ub) ->
                 EQ.equiv_b bf bf'
                   (pos_con idx I0) (pos_con (idx + 1) I0)
                   (pos_con idx I0) (pos_con (idx + 1) I0)) ->
    EQ.equiv_b bf bf'
      (pos_con lb I0) (pos_con ub I0)
      (pos_con lb I0) (pos_con ub I0).
  Proof.
    generalize dependent lb.
    induction ub.
    - intros. (* Base case, here lb = ub = 0 *)
      assert (lb = 0). { lia. }
      (* We need to prove equiv_b holds when positions are all zero *)
      apply EQ.equiv_b_nil; unfold BA.to_nat; simpl; lia.
    - intros.
      (* Basically, prove that equiv_b bf bf' from lb to ub. 

         Case where lb = S ub. Then the same as the 0 case
       *)
      destruct (PeanoNat.Nat.eq_dec lb (S ub)).
      + repeat rewrite <- e.
        apply EQ.equiv_b_nil; unfold BA.to_nat, BA.len; simpl; try lia.
      + assert (ub <= buf_len bf). { lia. }
        assert (lb <= ub). { lia. }
        assert (
            (forall idx : nat,
                lb <= idx ->
                idx < ub ->
                EQ.equiv_b bf bf'
                           {| byte_pos := idx; byte_off := I0 |}
                           {| byte_pos := idx + 1; byte_off := I0 |}
                           {| byte_pos := idx; byte_off := I0 |}
                           {| byte_pos := idx + 1; byte_off := I0 |})).
        { intros.  apply H; try lia. } 
          
        assert (G := IHub H0 lb lb_ge0 H1 H2).
        assert (G1 := H ub H1 (PeanoNat.Nat.lt_succ_diag_r ub)). 

        eapply EQ.equiv_b_append.
        * apply G.
        * rewrite PeanoNat.Nat.add_1_r in G1.
          apply G1.
  Qed.
      
  (* Then, we show that groups of index would also work *)
  Lemma several_byte_equiv  (bf bf' : ByteBuffer)
    (len_eq : buf_len bf = buf_len bf') (lb ub : nat) 
    (lb_ge0 : 0 <= lb)
    (lb_le_ub : lb <= ub)
    (ub_le_len : ub <= buf_len bf) :
    (forall idx, (lb <= idx) -> (idx < ub) ->
                byte_get bf idx = byte_get bf' idx) ->
    EQ.equiv_b bf bf'
      (pos_con lb I0) (pos_con ub I0)
      (pos_con lb I0) (pos_con ub I0).
  Proof.
    intros. 
    apply several_byte_equiv_b; auto.
    intros.
    apply one_byte_equiv; auto. 
    lia.
  Qed.
    
  (* diff only by 1 byte indicates the fact that any byte other
     then that specific index in the byte buffer should be the
     same.


     |--------|
        ^   ^
        |   |
        off n
        I2  
     write n bits, starting from off.
     
     We can probably prove it on a simpler level.
     We need to have a way to represent nat to bool.

     First, we mask the original byte say a0, by 0-off and
     off+n to end.
   *)

  (* Convert n into a list of bool of length bt *)
  Fixpoint nat_to_bool_list_helper (bt : nat) (n : nat) : list bool :=
    match bt with
    | 0 => nil
    | S bt' => (Nat.odd n) :: (nat_to_bool_list_helper bt' (Nat.div2 n))
    end.

  Definition nat_to_bool_list bt n :=
    List.rev (nat_to_bool_list_helper bt n).

  Lemma nat_to_bool_list_helper_len : forall bt n,
      length (nat_to_bool_list_helper bt n) = bt.
  Proof.
    intro bt. induction bt; intros; auto.
    simpl. rewrite (IHbt); auto.
  Qed.
      
  Lemma nat_to_bool_list_len : forall bt n, length (nat_to_bool_list bt n) = bt.
  Proof.
    intros. unfold nat_to_bool_list.
    rewrite List.length_rev. apply nat_to_bool_list_helper_len.
  Qed.

  (*Eval compute in nat_to_bool_list 8 100.  *)

  (* We can show that converting byte to nat to bit-list is
     the same as converting nat to bit-list?

     We can add these when we need them.

     byte_to_bit_list
   *)
  (*Eval compute in byte_to_bit_list Byte.x64 = nat_to_bool_list 8 100.  *)
 
  (*  Nat.shiftr (Nat.land (mask0 m off n) a) (m - off - n). *)

  (* We can also see it is independent of a0.
     Whatever we read is not revelant to a0. 
   *)
  Lemma shiftr_shiftl : forall a n : nat,
      Nat.shiftr (Nat.shiftl a n) n = a.
  Proof.
    intros.
    assert (G := PeanoNat.Nat.shiftr_shiftl_r a n n (le_n n)).
    rewrite G.
    rewrite PeanoNat.Nat.sub_diag. 
    apply PeanoNat.Nat.shiftr_0_r.
  Qed.

  Lemma shiftr_ones_ge : forall n m : nat,
      n <= m ->
      Nat.shiftr (PeanoNat.Nat.ones n) m = 0.
  Proof.
    intros. 
    rewrite PeanoNat.Nat.shiftr_div_pow2, PeanoNat.Nat.ones_equiv.
    assert (G := PeanoNat.Nat.pow_nonzero 2 m (PeanoNat.Nat.neq_succ_0 1)).
    rewrite PeanoNat.Nat.div_small_iff; auto.
    assert (G1 := PeanoNat.Nat.pow_le_mono_r _ _ _ (PeanoNat.Nat.neq_succ_0 1) H).
    lia.
  Qed.
  
  Lemma shiftr_ones : forall n : nat, Nat.shiftr (PeanoNat.Nat.ones n) n = 0.
  Proof.
    intros. apply shiftr_ones_ge; auto. 
  Qed.
    
  Lemma get_put_few_bits (m : nat) (off n : nat) (a0 : nat) (a : nat) :
    off + n <= m ->
    a0 < Nat.pow 2 m ->
    a < Nat.pow 2 n ->
    get_few_bits m off n (put_few_bits m off n a0 a) = a. 
  Proof.
    intros.
    unfold get_few_bits, put_few_bits.
    unfold mask, mask0.
    repeat (try (rewrite PeanoNat.Nat.shiftr_lor); try rewrite PeanoNat.Nat.shiftr_land).
    repeat rewrite shiftr_shiftl.
    rewrite PeanoNat.Nat.shiftr_shiftl_l; try lia.     
    rewrite PeanoNat.Nat.shiftr_shiftl_r; try lia.     

    rewrite shiftr_ones_ge; try lia.  simpl_0_bit.
    assert (m - 0 - off - (m - off - n) = n). { lia. }
    rewrite H2.

    rewrite PeanoNat.Nat.land_lor_distr_r,
      (PeanoNat.Nat.land_comm (PeanoNat.Nat.ones n) a),
      PeanoNat.Nat.land_assoc. 
    rewrite (PeanoNat.Nat.land_comm (PeanoNat.Nat.ones n)). 
    rewrite PeanoNat.Nat.land_ones, PeanoNat.Nat.shiftl_mul_pow2,
      PeanoNat.Nat.Div0.mod_mul.
    simpl_0_bit. 
    destruct a eqn:Ea. 
    - simpl_0_bit. trivial.
    - rewrite PeanoNat.Nat.land_ones_low; trivial.
      rewrite <- PeanoNat.Nat.log2_lt_pow2; lia.
  Qed.
  
  (*Eval compute in put_few_bits 2 4 153 1.

  Eval compute in AbsArray.slice (nat_to_bool_list 8 210) 1 5.  *)

  Definition same_bits (m off n : nat) :=
    Nat.land (mask0 m off n).

  (*Eval compute in same_bits 1 4 210.
  Eval compute in nat_to_bool_list 5 5. *)

  Lemma nat_to_eq_byte_to : forall (a : Byte.byte),
      (nat_to_bool_list 8 (Byte.to_nat a) =
         byte_to_bit_list a).
  Proof.
    intros. 
    destruct a; auto.
  Qed.

  Lemma bytebuffer_eq_byte : forall (c : Byte.byte),
      (BProp.to_bits (byte_make 1 c)) =
        byte_to_bit_list c.
  Proof.
    intros.
    destruct c; auto. 
  Qed.
      
  Lemma nat_to_bool_list_zero : forall a,
      nat_to_bool_list 0 a = nil.
    intros. unfold nat_to_bool_list.  simpl.
    auto.
  Qed.

  (* Here, count k from 0. For example,
     for 1101 = 13, 3rd digit is 1.

     These two function shall be the same
   *)

  
  (*Example n13 := 
    Eval compute in nat_to_bool_list_helper 6 13.
 (* Eval compute in get_kth_digit 1 13. *)
  Eval compute in Nat.testbit 13 1. *)

  Lemma get_kth_equal_nat_bool : forall n k a,
      k < n ->
      Nat.testbit a k = List.nth k (nat_to_bool_list_helper n a) true.
  Proof.
    intros. generalize dependent n.
    generalize dependent a. 
    induction k.
    - intros.
      simpl. destruct n.
      + inversion H.
      + simpl. auto. 
    - intros. 
      destruct n.
      + inversion H.
      + simpl.
        assert (G := IHk (Nat.div2 a) n (Arith_base.lt_S_n_stt _ _ H)).
        rewrite <- G.
        repeat rewrite  (PeanoNat.Nat.div2_spec). 
        f_equal. 
  Qed.

  (* say the list is [1,0,0,0,1,1]. Then the kth digit
     say ntblh 5 = 1 0 0 0 1,
     ntblh 6 = 1 0 0 0 1 1.
     And the 5th digit of (ntblh 6) is 1

     So for the inverse which is (kth_digit 5) (ntbl 5) = ntbl 6.

     Another property we need from ntblh is
     firstn (ntblh 6) = ntblh 5. 
   *)

  Lemma firstn_nat_bool_helper : forall m n a,
      m <= n ->
      List.firstn m (nat_to_bool_list_helper n a) =
        nat_to_bool_list_helper m a.
  Proof.
    intros.
    assert (length (List.firstn m (nat_to_bool_list_helper n a)) = m).
    { rewrite List.firstn_length_le; auto.
      rewrite nat_to_bool_list_helper_len; auto.
    } 
    eapply List.nth_ext.
    - rewrite nat_to_bool_list_helper_len, H0. auto.
    - rewrite H0.  intros.
      rewrite List.nth_firstn.
      destruct_if_goal.
      + rewrite <- get_kth_equal_nat_bool; try lia.
        rewrite <- get_kth_equal_nat_bool; auto; try lia.
      + rewrite PeanoNat.Nat.ltb_ge in E. lia.
  Qed.

  Lemma nat_bool_helper_S : forall n a,
      nat_to_bool_list_helper (S n) a =
        List.app (nat_to_bool_list_helper n a) (Nat.testbit a n :: nil).
  Proof.
    intros.
    erewrite <- (List.firstn_skipn _  (nat_to_bool_list_helper (S n) a)).
    f_equal.
    - apply firstn_nat_bool_helper; auto.
    - assert (length (List.skipn n (nat_to_bool_list_helper (S n) a)) = 1).
      { rewrite List.length_skipn, nat_to_bool_list_helper_len.
        lia. } 
      eapply List.nth_ext; auto. 
      rewrite H.  intros.
      destruct n0; try lia.
      rewrite List.nth_skipn. simpl_nat.  
      rewrite <-  get_kth_equal_nat_bool; simpl; auto.
      Unshelve. 
      apply true.
  Qed.
    
  Lemma nat_to_bool_list_S : forall n a,
      nat_to_bool_list (S n) a =
        cons (Nat.testbit a n) (nat_to_bool_list n a). 
  Proof.
    intros.
    unfold nat_to_bool_list.
    rewrite nat_bool_helper_S.
    rewrite List.rev_unit. auto.
  Qed.

  (* say [1,0,0,0,1,1] as the list-helper. Then 

     Shiftr 3 would result in 0,1,1. 

   *)
  (*Eval compute in nat_to_bool_list_helper 6 49.
  Eval compute in nat_to_bool_list_helper 4 (Nat.shiftr 49 2). *)
 
  (*Lemma shiftr_kth_digit : forall (n m a : nat),
        get_kth_digit m (Nat.shiftr a n) = get_kth_digit (m + n) a.
  Proof.
    intros.
    unfold get_kth_digit.
    rewrite PeanoNat.Nat.shiftr_shiftr.
    f_equal. f_equal.  apply PeanoNat.Nat.add_comm.
  Qed.*)
      
  Lemma shiftr_skipn_helper : forall (n m a : nat),
      n <= m ->
      List.skipn n (nat_to_bool_list_helper m a) =
        nat_to_bool_list_helper (m - n) (Nat.shiftr a n).
  Proof.
    intros.
    assert (length (List.skipn n (nat_to_bool_list_helper m a)) = (m - n)).
    { rewrite List.length_skipn, nat_to_bool_list_helper_len.
      lia. } 
    eapply List.nth_ext; auto.
    - rewrite H0.  
      rewrite nat_to_bool_list_helper_len.  auto.
    - rewrite H0. intros.
      rewrite List.nth_skipn.
      repeat rewrite <- get_kth_equal_nat_bool; try lia.
      rewrite PeanoNat.Nat.shiftr_spec'. f_equal; apply PeanoNat.Nat.add_comm. 
  Qed.
    
  Lemma shiftr_firstn : forall (n m a : nat),
      n <= m ->
      List.firstn n (nat_to_bool_list m a) =
        nat_to_bool_list n (Nat.shiftr a (m - n)).
  Proof.
    intros.
    unfold nat_to_bool_list.
    rewrite List.firstn_rev.
    f_equal. rewrite nat_to_bool_list_helper_len.
    rewrite shiftr_skipn_helper; try lia.
    f_equal; lia.
  Qed.
      
  (*Eval compute in List.skipn 1 (cons 1 (cons 2 (cons 3 nil))). *)

  (* say 0b110001 [1,0,0,0,1,1] as the list-helper. Then 

     land ones 3 would result in [1,0,0], 0,0,0
     i.e., only the 
   *)
 (* Eval compute in nat_to_bool_list_helper 6 49.
  Eval compute in nat_to_bool_list_helper 6 (Nat.land (PeanoNat.Nat.ones 5) 49).   *)

  Lemma ones_kth_digit_in : forall (n m a : nat),
      n < m ->
      Nat.testbit (Nat.land (PeanoNat.Nat.ones m) a) n =
        Nat.testbit a n.
  Proof.
    intros.
    rewrite PeanoNat.Nat.land_spec, PeanoNat.Nat.ones_spec_low; auto. 
  Qed.
    
  Lemma ones_kth_digit_out : forall (n m a : nat),
      m <= n ->
      Nat.testbit (Nat.land (PeanoNat.Nat.ones m) a) n = false. 
  Proof.
    intros. rewrite PeanoNat.Nat.land_spec, PeanoNat.Nat.ones_spec_high; auto. 
  Qed.
  
  Lemma ones_firstn_helper : forall (n m a : nat),
      n <= m ->
      List.firstn n (nat_to_bool_list_helper m a) =
        nat_to_bool_list_helper n (Nat.land (PeanoNat.Nat.ones n) a).
  Proof. 
    intros.
    assert (length (List.firstn n (nat_to_bool_list_helper m a)) = n).
    { rewrite List.firstn_length_le; auto.
      rewrite nat_to_bool_list_helper_len; auto. } 
    eapply List.nth_ext; auto.
    - rewrite H0, nat_to_bool_list_helper_len; auto.
    - intros. rewrite H0 in H1.
      rewrite List.nth_firstn.
      destruct_if_goal.
      + repeat rewrite <- get_kth_equal_nat_bool; try lia. 
        rewrite ones_kth_digit_in; auto.
      + rewrite PeanoNat.Nat.ltb_ge in E.  lia. 
  Qed.

  Lemma ones_skipn : forall (n m a : nat),
      n <= m ->
      List.skipn n (nat_to_bool_list m a) =
        nat_to_bool_list (m - n)
          (Nat.land (PeanoNat.Nat.ones (m - n)) a).
  Proof.
    intros.
    unfold nat_to_bool_list.
    rewrite List.skipn_rev. f_equal.
    rewrite nat_to_bool_list_helper_len.
    apply ones_firstn_helper.
    lia.
  Qed.

  (* land (ones n) (Shiftr a (m - off - n)) *)
        
  Lemma slice_equal_mask : forall (m off n : nat) (a : nat),
      off + n <= m ->
      AbsArray.slice (nat_to_bool_list m a) off (off + n) =
        nat_to_bool_list n
          (get_few_bits m off n a).
  Proof.
    intros. 
    unfold AbsArray.slice, get_few_bits, mask0.
    rewrite shiftr_firstn; auto.
    rewrite ones_skipn; auto; try lia.
    f_equal; try lia.
    f_equal; f_equal; try lia.
  Qed.
        
  (* Problem: how to write this proof, we can easily bruteforce it, takes about
     256 * 8 * 8 time, which is bearable.

     We could also switch out a with nat a' (a' <= 255).

     We can see that (nat_to_bool_list shiftr) is roughly equal to
     firstn nat_to_bool_list
   *)

  (* Eval compute in Nat.testbit 255 8.  *)

  Lemma testbit_eq_le_pow : forall n a,
      (forall m, n <= m -> Nat.testbit a m = false) <->
        a < Nat.pow 2 n.
  Proof.
    intros.
    split.
    - intros.
      assert ((forall n0 : nat, PeanoNat.Nat.testbit (PeanoNat.Nat.div a (PeanoNat.Nat.pow 2 n)) n0 = false)).
      { intros.  assert (G0 := PeanoNat.Nat.div_pow2_bits a ). 
        rewrite G0.
        apply H.
        lia. } 
      assert (G :=  PeanoNat.Nat.bits_inj_0  (PeanoNat.Nat.div a (PeanoNat.Nat.pow 2 n)) H0).
      rewrite <- PeanoNat.Nat.div_small_iff; auto.
      apply PeanoNat.Nat.pow_nonzero. auto.
    - intros. 
      destruct a.
      + apply PeanoNat.Nat.bits_0. 
      + apply PeanoNat.Nat.bits_above_log2.
        rewrite <- PeanoNat.Nat.log2_lt_pow2; try lia.
        assert (2 <> 0). { auto. } 
        eassert (G := PeanoNat.Nat.pow_le_mono_r _ _ _ H1 H0).
        lia.
  Qed.
  
  Lemma shift_lt : forall n m a,
      a < Nat.pow 2 n ->
      m <= n -> 
      Nat.shiftr a (n - m) < Nat.pow 2 m.
  Proof.
    intros.
    rewrite <- testbit_eq_le_pow in *.
    intros.
    rewrite PeanoNat.Nat.shiftr_spec'.
    apply H. lia.
  Qed.
    
  Lemma put_in_byte_left_non_inter : forall (m off n : nat) (a0 a : nat),
      a0 < Nat.pow 2 m ->
      a < Nat.pow 2 n -> 
      off + n <= m ->
      AbsArray.slice (nat_to_bool_list m (put_few_bits m off n a0 a)) 0 off =
        AbsArray.slice (nat_to_bool_list m a0) 0 off.
  Proof.
    intros.
    unfold AbsArray.slice. simpl.
    repeat rewrite  shiftr_firstn; try lia.
    unfold put_few_bits.
    rewrite PeanoNat.Nat.shiftr_lor, PeanoNat.Nat.shiftr_shiftl_r; try lia.   
    assert (PeanoNat.Nat.shiftr a (m - off - (m - off - n)) = 0).
    { rewrite (PeanoNat.Nat.shiftr_div_pow2 a), PeanoNat.Nat.div_small; auto.
      assert ( (m - off - (m - off - n)) = n). { lia. }
      rewrite H2.  trivial. }
    rewrite H2. simpl_0_bit. 
    f_equal.
    rewrite PeanoNat.Nat.shiftr_land.
    unfold mask.  rewrite PeanoNat.Nat.shiftr_lor.
    assert (PeanoNat.Nat.shiftr (mask0 m (off + n) (m - off - n)) (m - off)  = 0). 
    { unfold mask0. rewrite PeanoNat.Nat.shiftr_shiftl_r; try lia.
      apply shiftr_ones_ge. lia. }
    rewrite H3. simpl_0_bit.
    unfold mask0. rewrite PeanoNat.Nat.shiftr_shiftl_r; try lia. 
    assert ( (m - off - (m - 0 - off)) = 0). { lia. }
    rewrite H4. simpl_0_bit. 
    rewrite PeanoNat.Nat.land_comm, PeanoNat.Nat.land_ones,
      PeanoNat.Nat.mod_small;
      auto.
    apply shift_lt; lia.
  Qed.
    (*
      We need some lemmas,
      a < pow 2 n means that a.[m] = false for m >= n. 

        Having slice the same, means that say
       two bytes a, b are same from [1, 5),
       a = 11010001 and b = 01010011
       both from [1, 5) are 1010. We can say
       slice (nat_to_bool_list 8 a) 1 5 =
       slice (nat_to_bool_list 8 b) 1 5.

       Or we could say (land (shiftl (nat_ones 4) (8 - (5 + 1))) a)
       and this of b are the same. 
     *)

  (*  land (ones n) (shiftl a m) = 0 if m >= n *)
  Lemma land_ones_shiftl : forall n m a,
      n <= m ->
      Nat.land (PeanoNat.Nat.ones n) (Nat.shiftl a m) = 0.
  Proof.
    intros.
    rewrite PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.land_comm.
    rewrite PeanoNat.Nat.land_ones. 
    assert (Nat.pow 2 m = (Nat.pow 2 (m - n)) * (Nat.pow 2 n)).
    { rewrite <- PeanoNat.Nat.pow_add_r.
      f_equal.  lia. }
    rewrite H0, PeanoNat.Nat.mul_assoc.
    apply  PeanoNat.Nat.Div0.mod_mul.
  Qed.
  
  Lemma put_in_byte_right_non_inter : forall (m off n : nat) (a0 a : nat),
      off + n <= m ->
      AbsArray.slice (nat_to_bool_list m (put_few_bits m off n a0 a)) (off + n) m =
        AbsArray.slice (nat_to_bool_list m a0) (off + n) m.
  Proof.
    intros.
    unfold AbsArray.slice.
    repeat rewrite List.firstn_all2; try (rewrite nat_to_bool_list_len; auto).
    repeat rewrite ones_skipn; auto.
    f_equal.
    unfold put_few_bits, mask.
    rewrite PeanoNat.Nat.land_lor_distr_r,  PeanoNat.Nat.land_lor_distr_l.
    rewrite land_ones_shiftl; try lia.
    simpl_0_bit. 
    
    rewrite PeanoNat.Nat.land_lor_distr_r.
    unfold mask0.
    rewrite  PeanoNat.Nat.land_assoc.
    rewrite land_ones_shiftl; try lia.
    assert ( (m - (off + n) - (m - off - n)) = 0). { lia. }
    rewrite H0.
    simpl_0_bit. 
    rewrite PeanoNat.Nat.land_assoc.
    rewrite PeanoNat.Nat.sub_add_distr. 
    rewrite PeanoNat.Nat.land_diag. auto.
  Qed.

  Lemma slice_implies_equiv_b : forall (a b : nat) (c1 c2 : Byte.byte),
      a <= b <= 8 ->
      AbsArray.slice (nat_to_bool_list 8 (Byte.to_nat c1)) a b =
        AbsArray.slice (nat_to_bool_list 8 (Byte.to_nat c2)) a b ->
       EQ.equiv_b (byte_make 1 c1) (byte_make 1 c2)
         (BA.of_nat a) (BA.of_nat b)
         (BA.of_nat a) (BA.of_nat b). 
  Proof.
    intros. 
    unfold EQ.equiv_b. intros.

    
    assert (forall c : Byte.byte, EQ.valid_pos_pairb
                                    (byte_make 1 c)
                                    (BA.of_nat a)
                                    (BA.of_nat b)  = true).
    { intros. rewrite <- EQ.valid_pos_pair_dec.
      unfold EQ.valid_pos_pair. repeat rewrite BProp.to_of_nat. 
      simpl. repeat rewrite byteidx_of_to_nat; try lia.
      unfold BA.len. auto.  } 
    
    repeat destruct_match_goal; unfold EQ.to_bool_list in *; repeat destruct_if_in.
    + repeat rewrite bytebuffer_eq_byte,  <- nat_to_eq_byte_to.
      repeat rewrite BProp.to_of_nat.
      apply H0.
    + rewrite (H1 c2) in E1. discriminate.
    + rewrite (H1 c1) in E0. discriminate.
  Qed.

  Lemma pos_zero_of_nat : BProp.pos_zero = BA.of_nat 0.
  Proof.
    unfold BProp.pos_zero, BA.of_nat.  simpl. auto.
  Qed.

  (* This is easily derived from get_put
     and slice. 
   *)
  Lemma put_in_byte_consistent : forall (m off: nat) (m' off' : nat) (n : nat)
                                        (a0 a0' : nat) (a : nat),
      off + n <= m ->
      off' + n <= m' ->
      a0 < Nat.pow 2 m ->
      a0' < Nat.pow 2 m' ->
      a < Nat.pow 2 n ->
      AbsArray.slice (nat_to_bool_list m (put_few_bits m off n a0 a)) off (off + n) = 
        AbsArray.slice (nat_to_bool_list m' (put_few_bits m' off' n a0' a)) off' (off' + n).
  Proof.
    intros. 
    repeat (rewrite slice_equal_mask; auto).
    f_equal.
    repeat (rewrite get_put_few_bits; auto). 
  Qed.
      
  (*
    Here, we have the idea of writing a nat to k-bytes
    if we have a ByteBuffer, first we read k-bytes from it,
    we read it into a nat a0 (of length 8 * k),  then
    we write n-bits to a0, resulting in a,
    
    starting from some byte-number i

    We should make sure that i + k <= buf_len bf.
    Case where k = 0, then output 0. 
   *)
  


  Ltac destruct_match_false_new :=
    repeat match goal with
      | [ H : context[ match ?X with
                       | Some _ => _
                       | None => False
                       end ] |- _ ] =>
          let E := fresh "E" in
          destruct X eqn:E; try contradiction
      end.

  Lemma slice_0_len : forall l, AbsArray.slice l 0 (length l) = l.
  Proof.
    intros. 
    rewrite AbsArray.slice_from_zero; auto.
    apply List.firstn_all2; auto.
  Qed.


  Lemma get_byte_le_256 :  forall bf i n,
      (bf [[i]]) = Some n ->
      n < Nat.pow 2 8.
  Proof.
    intros.
    unfold byte_get_nat, option_bind in H.
    destruct_match.
    assert (G := Byte.to_nat_bounded b).
    simpl.
    lia.
  Qed.
  
  
  Lemma read_k_bytes_le : forall k i bf a,
      read_k_bytes k i bf = Some a ->
      a < Nat.pow 2 (k * 8).
  Proof.
    intro k.
    induction k.
    - intros. simpl in *.
      destruct_if_in_new.  inversion H; auto. 
    - intros. simpl in H.
      unfold option_bind in H.
      repeat destruct_match.
      rewrite <- testbit_eq_le_pow.
      intros.

      assert (G := IHk (i + 1) _ _ E0).
      rewrite <- testbit_eq_le_pow in G.
      rewrite PeanoNat.Nat.lor_spec.

      assert (G1 := get_byte_le_256 _ _ _ E).
      rewrite <- testbit_eq_le_pow in G1.
      apply Bool.orb_false_intro.
      +  rewrite PeanoNat.Nat.shiftl_spec_high'; try lia.
         apply G1. lia.
      + apply G.  lia.
  Qed.
  
  Lemma byte_get_slice : forall (bf : ByteBuffer) (i a : nat),
      (bf [[i]]) = Some a ->
      nat_to_bool_list 8 a = AbsArray.slice (BProp.to_bits bf) (i * 8) (i * 8 + 8).
  Proof.
    intros.
    unfold byte_get_nat, option_bind in H. destruct_match.   
    
    assert (G := byte_get_equiv_b bf i b E).

    unfold EQ.equiv_b in G.
    destruct_match_false_new.
    
    unfold EQ.to_bool_list in E0, E1.
    repeat destruct_if_in_new.
    unfold BA.to_nat in E0, E1.  simpl in E0, E1.
    rewrite PeanoNat.Nat.mul_add_distr_r in E0.
    simpl_nat_in.
    inversion E0. inversion E1.
    rewrite bytebuffer_eq_byte,  <- nat_to_eq_byte_to in H3.
    rewrite slice_0_len in H3.  
    
    rewrite H2, H3. auto.
  Qed.

  Lemma nat_to_bool_n : forall n a b,
      (Nat.land (PeanoNat.Nat.ones n) a) = (Nat.land (PeanoNat.Nat.ones n) b) ->
      nat_to_bool_list n a =
        nat_to_bool_list n b.
  Proof.
    intros.
    unfold nat_to_bool_list.
    f_equal.
    assert (G1 :=  nat_to_bool_list_helper_len n a).
    assert (G2 :=  nat_to_bool_list_helper_len n b). 
    eapply List.nth_ext.
    - rewrite G1, G2. auto. 
    - intros.  rewrite G1 in H0. 
      repeat rewrite <- get_kth_equal_nat_bool; auto.
      rewrite <- (ones_kth_digit_in _ _ a H0).
      rewrite <- (ones_kth_digit_in _ _ b H0).
      rewrite H.
      auto.
  Qed.

  (*Lemma read_k_implies_valid : forall (k i : nat) (bf : ByteBuffer) (a : nat),
      (read_k_bytes (k + 1) i bf) = Some a ->
      (S k + i) <= buf_len bf.
  Proof.
    intros k. 
    induction k.
    - intros. simpl in H.
      unfold option_bind, byte_get_nat, option_bind in H.
      repeat destruct_match_new. 
      assert (G := byte_get_in_range_rev _ _ _ E0).
      lia.
    - intros. simpl in H.  
      unfold option_bind , byte_get_nat, option_bind in H.
      repeat destruct_match_new.
      assert (G := IHk (i + 1) _ _ E0). 
      lia.
  Qed. *)
          
  (* We could show that read-k-bytes is the same as
     
     (AbsArray.slice (BProp.to_bits bf) (BA.to_nat p1) (BA.to_nat p2)) 
   *)
  Lemma read_k_bytes_len_le : forall k i bf a,
      read_k_bytes k i bf = Some a -> 
      k + i <= buf_len bf.
  Proof.
    intro k. induction k.
    - intros; simpl in H.
      destruct_if_in_new. inversion H; subst.  
      simpl_nat.
      apply PeanoNat.Nat.leb_le.  auto.
    - intros.
      simpl in H.  
      
      unfold option_bind, byte_get_nat, option_bind in H.
      repeat destruct_match_new. 
      
      assert (G := IHk _ _ _ E0).
      lia.
  Qed.
  
  Lemma read_k_equals_slice : forall (k i : nat) (bf : ByteBuffer) (a : nat),
      (read_k_bytes k i bf) = Some a ->
      nat_to_bool_list (k * 8) a
      = AbsArray.slice (BProp.to_bits bf) (i * 8) ((i + k) * 8).
  Proof.
    intro k.
    induction k; intros.
    - simpl. rewrite nat_to_bool_list_zero. simpl_nat.
      rewrite AbsArray.slice_same; auto.
      rewrite BProp.to_bits_len. unfold BA.len.
      assert (G := read_k_bytes_len_le _ _ _ _ H). 
      lia.
    - Opaque Nat.shiftl. 
      
      simpl in H. unfold option_bind in H.
      repeat destruct_match.
      assert (G0 := read_k_bytes_len_le _ _ _ _ E0). 

      assert  (i + 1 + k <= buf_len bf). { lia. } 
      assert (G := IHk (i + 1) bf _  E0).
      (* Will use AbsArray.slice_append
         We can simply prove ntbl (8k + 8) (lor (n0 << 8) n)
         = (ntbl n)  ++ ntbl (k * 8) n0

         And ntbl n = slice bf (8i) (8i + 8).

         Example,
         0xa, 0xb, 0xc,
          
         When I am reading it, i read 0xa,
         (shift 0xa (2 * 8) || shift (0xb 8) || 0xc).

       *)
      assert (G1 := byte_get_slice _ _ _ E).
      assert (S k * 8 - 8 = k * 8). { lia. } 
            
      assert (  app (nat_to_bool_list 8 n) (nat_to_bool_list (k * 8) n0)
                = nat_to_bool_list (S k * 8) ( Nat.lor (Nat.shiftl n (k * 8)) n0 )).
      { rewrite <- (List.firstn_skipn 8).
        f_equal.
        - rewrite shiftr_firstn; try lia.
          rewrite PeanoNat.Nat.shiftr_lor.   
          rewrite PeanoNat.Nat.shiftr_shiftl_l; try lia.
          apply nat_to_bool_n.
          assert (k * 8 - (S k * 8 - 8) = 0). { lia. }
          rewrite H4. simpl_0_bit.  
          rewrite PeanoNat.Nat.land_lor_distr_r.
          
          rewrite H3.

          assert (G2 := read_k_bytes_le _ _ _ _ E0). 
          eassert (G3 := shift_lt _ _ _ G2 (PeanoNat.Nat.le_0_l _)).  
          rewrite PeanoNat.Nat.sub_0_r,  PeanoNat.Nat.lt_1_r in G3.  
          rewrite G3.

          simpl_0_bit.
          auto.
        - rewrite ones_skipn; try lia.
          rewrite H3.
          apply nat_to_bool_n.
          rewrite PeanoNat.Nat.land_assoc, PeanoNat.Nat.land_diag,
            PeanoNat.Nat.land_lor_distr_r.

          rewrite land_ones_shiftl; auto.
          simpl_0_bit.
          auto.
      }
      rewrite <- H4.
      erewrite AbsArray.slice_append. 
      + f_equal.
      + assert (i * 8 <= (i + 1) * 8). { lia. }
        apply H5.
      + lia.
      + rewrite BProp.to_bits_len.
        unfold BA.len.
        lia.
      + rewrite G1.
        f_equal.  lia.
      + rewrite G.
        f_equal; lia.
  Qed.
  
  (* The step now it to fully write the surjection of the proof. That is
     we need to re-define the whole process. Our original definition only
     accomadate so much. Now we need to expand it to 8 * 7 = 57 bits.

     This is because OCaml integers are 63-bits, and consider the first
     bit for

     So we can actually prove some basic properties of read-n-bits and
     put-n-bits
   *)

  Lemma put_k_bytes_len : forall  (k i : nat) (bf bf' : ByteBuffer) (a : nat),
      put_k_bytes k i bf a = Some bf' -> 
      buf_len bf = buf_len bf'.
  Proof.
    intro k. induction k.
    - intros. simpl. unfold put_k_bytes in H.
      destruct_if_in_new. 
      inversion H; auto.
    - intros. Opaque Nat.shiftr. simpl in H.
      unfold option_bind in H. repeat destruct_match_new. 
      assert (G1 := IHk _ _ _ _ H).
      rewrite <- G1.
      erewrite byte_set_length; auto. apply E0. 
  Qed.

  Lemma put_few_bits_le : forall (m off n a0 a : nat),
      off + n <= m -> 
      a0 < Nat.pow 2 m ->
      a < Nat.pow 2 n -> 
      put_few_bits m off n a0 a < Nat.pow 2 m.
  Proof.
    intros.
    unfold put_few_bits.
    rewrite <- testbit_eq_le_pow in *.
    intros.
    rewrite PeanoNat.Nat.lor_spec.
    apply Bool.orb_false_intro.
    - rewrite PeanoNat.Nat.land_spec.
      rewrite H0; auto. 
      rewrite Bool.andb_false_r. trivial.
    - rewrite PeanoNat.Nat.shiftl_spec_high'; try lia.
      apply H1.
      lia.
  Qed.
    
  Ltac simpl_put_n_bits H :=
    unfold put_n_bits in H;
    destruct_if_in_new;
    destruct_match_dec_new;
    unfold option_bind in H;
    repeat destruct_match_new.

  Lemma div_plus_one : forall (n a : nat), a <= (Nat.div (a + n) (S n)) * (S n).
  Proof.
    intros.
    (* PeanoNat.Nat.div_add *)
    destruct a.
    - simpl_nat.
    - rewrite PeanoNat.Nat.add_succ_comm,  <- (PeanoNat.Nat.mul_1_l (S n)) at 1.
      rewrite PeanoNat.Nat.div_add; auto.
      rewrite PeanoNat.Nat.mul_add_distr_r.
      simpl_nat.
      rewrite <- PeanoNat.Nat.add_succ_comm.
      assert (a <= (S n * Nat.div a (S n)) + n).
      { rewrite (PeanoNat.Nat.Div0.div_mod a (S n)) at 1.
        assert (PeanoNat.Nat.modulo a (S n) <= n).
        { assert (G := PeanoNat.Nat.mod_upper_bound a (S n) (PeanoNat.Nat.neq_succ_0 _)).
          lia. }
        lia.
      }
      lia.
  Qed.
  
  Lemma ones_le : forall a n, PeanoNat.Nat.land a (PeanoNat.Nat.ones n) < Nat.pow 2 n.
  Proof.
    intros. rewrite PeanoNat.Nat.land_ones.
    apply PeanoNat.Nat.mod_upper_bound.
    apply PeanoNat.Nat.pow_nonzero.
    auto.
  Qed.

  Ltac simpl_put_k_bytes H :=
    simpl in H;
    unfold option_bind in H;
    repeat destruct_match_new.
  
  (* I need this property before I can prove put-read *)
  Lemma put_k_bytes_non_inter_helper : forall (k i : nat) (bf bf' : ByteBuffer) (a : nat),
      put_k_bytes k i bf a = Some bf' ->
      (forall j, j < i \/ k + i <= j -> byte_get bf j = byte_get bf' j).
  Proof.
    intro k.
    induction k.
    - intros. simpl in H.
      destruct_if_in_new. 
      inversion H. auto. 
    - intros.
      Opaque Nat.mul. 
      simpl_put_k_bytes H.
      Transparent Nat.mul. 

      assert (G := IHk _ _ _ _ H). 
      rewrite <- G; try lia.

      erewrite (byte_set_get_other _ _ _ _ E0); auto. 
      lia. 
  Qed.
 
  Lemma put_read_k_bytes : forall (k i : nat) (bf bf' : ByteBuffer) (a : nat),
      a < Nat.pow 2 (k * 8) ->
      put_k_bytes k i bf a = Some bf' -> 
      read_k_bytes k i bf' = Some a.
  Proof.
    intro k. induction k.
    - intros. 
      simpl in *.
      destruct_if_in_new.  inversion H0; subst.
      rewrite E.  destruct a; try lia; auto. 
    - intros.
      Opaque Nat.mul. 
      simpl_put_k_bytes H0. 
      Transparent Nat.mul. 

      eassert (G := IHk _ _ _ _ (ones_le _ _) H0).

      simpl.

      unfold option_bind, byte_get_nat, option_bind.
      rewrite G.

      assert (i < i + 1). { unfold lt. rewrite PeanoNat.Nat.add_1_r. trivial.  }
      eassert (G1 := put_k_bytes_non_inter_helper _ _ _ _ _ H0 i (or_introl H1)).
      assert (G2 := byte_set_get _ _ _ _ E0). 
      rewrite <- G1, G2. 

      f_equal.
      erewrite Byte.to_of_nat; try apply E.

      rewrite PeanoNat.Nat.shiftr_land.
      unfold mask0.  rewrite PeanoNat.Nat.shiftr_shiftl_r; try lia.
      assert ((k * 8 - (S k * 8 - 0 - 8)) = 0). { lia. }
      rewrite H2. simpl_0_bit.

      (* shiftr a (8k) < 2 ^ 8, thus land and ones are useless here *)
      assert (8 <= S k * 8). { lia. }

      eassert (G' := shift_lt _ _ _ H H3).
      assert (S k * 8 - 8 = k * 8). { lia. }
      rewrite H4 in G'.
      rewrite PeanoNat.Nat.land_ones. 
      rewrite PeanoNat.Nat.mod_small; auto. 
      rewrite <- PeanoNat.Nat.ldiff_ones_r. 
      rewrite PeanoNat.Nat.lor_ldiff_and. 
      auto. 
  Qed.

  Lemma put_k_equals_slice : forall (k i : nat) (bf bf' : ByteBuffer) (a : nat),
      a < Nat.pow 2 (k * 8) -> 
      i + k <= buf_len bf -> 
      (put_k_bytes k i bf a) = Some bf' ->
      nat_to_bool_list (k * 8) a
      = AbsArray.slice (BProp.to_bits bf') (i * 8) ((i + k) * 8).
  Proof.
    intros.  
    (* Can i simply use the fact that read-k-bytes on bf'
       will give me a, thus they are the same?
     *)
    eassert (G1 := put_read_k_bytes _ _ _ _ _ H H1).
    assert (G1' := put_k_bytes_len _ _ _ _ _ H1).
    rewrite G1' in H0. 
    eassert (G2 := read_k_equals_slice _ _ _ _ G1).
    apply G2.
  Qed.
    
  Lemma put_read_n_bits : forall (n : nat),
      format_correct_surj _ _ (put_n_bits n) (read_n_bits n).
  Proof.
    intros. unfold format_correct_surj.
    intros.
    simpl_put_n_bits H.
    inversion H; subst.
    
    unfold read_n_bits.
    unfold BA.len in *.
    rewrite <- (put_k_bytes_len _ _ _ _ _ E2).
    rewrite E.

    eassert (G0 :=  put_few_bits_le
                     (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                     (ByteIdx_to_nat (byte_off pos))
                     n
                     n0
                     a
                     (div_plus_one _ _ )
                     (read_k_bytes_le _ _ _ _ E1)
                     pf
           ). 
    eassert (G := put_read_k_bytes _ _ _ _ _ G0 E2).
    unfold option_bind.
    rewrite G. decode_eq. 

    apply get_put_few_bits; auto.
    - apply div_plus_one.
    - eapply read_k_bytes_le. 
      apply E1.
  Qed.

  Lemma lor_ones_shiftl : forall m off,
      off <= m ->
      Nat.lor (Nat.shiftl (PeanoNat.Nat.ones off) (m - off)) (PeanoNat.Nat.ones (m - off)) =
        PeanoNat.Nat.ones m.
  Proof.
    intros.
    apply PeanoNat.Nat.bits_inj.
    unfold PeanoNat.Nat.eqf. intros.
    rewrite PeanoNat.Nat.lor_spec.
    
    destruct (Compare_dec.le_gt_dec m n).
    - repeat rewrite PeanoNat.Nat.ones_spec_high; try lia.
      rewrite PeanoNat.Nat.shiftl_spec_high'; try lia.
      rewrite PeanoNat.Nat.ones_spec_high; lia. 
    - rewrite (PeanoNat.Nat.ones_spec_low m); try lia.
      destruct (Compare_dec.le_gt_dec (m - off) n). 
      + rewrite PeanoNat.Nat.shiftl_spec_high'; try lia. 
        rewrite PeanoNat.Nat.ones_spec_low; try lia.
      + rewrite PeanoNat.Nat.ones_spec_low; try lia.
  Qed.
    
  Lemma put_few_bits_nil : forall m off a0,
      off <= m ->
      a0 < Nat.pow 2 m -> 
      put_few_bits m off 0 a0 0 = a0.
  Proof.
    intros. unfold put_few_bits, mask, mask0. 
    simpl_0_bit.    
    assert (m - (off + 0) - (m - off - 0) = 0). { lia. } 
    rewrite H1. simpl_0_bit. 
(* (Nat.lor (Nat.shiftl (PeanoNat.Nat.ones off) (m - off)) (PeanoNat.Nat.ones (m - off))) *)
    simpl_nat.
    rewrite lor_ones_shiftl; auto.
    rewrite PeanoNat.Nat.land_comm, PeanoNat.Nat.land_ones,
      PeanoNat.Nat.mod_small;
      auto.
  Qed.

  Lemma valid_pair_eq_len : forall bf bf' p1 p2,
      buf_len bf = buf_len bf' ->
      EQ.valid_pos_pair bf p1 p2 -> EQ.valid_pos_pair bf' p1 p2.
  Proof.
    intros. unfold EQ.valid_pos_pair, BA.len in *. rewrite <- H.  auto.
  Qed.
    
  (* we first have to see if the new-version of put-n-bits runs,
     restructure the code a bit, such that it is inside the function.

     Then, we continue the proofs. 
   *)

  (*
    |---|---|---|---|---|
          a       b      
          
    Here is how it works
   *)

  Lemma bytebuffer_slice_helper : forall (bf : ByteBuffer) (pos : BytePos)
                                         (n : nat) (a b : nat),
      Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 + byte_pos pos <= buf_len bf ->
      a <= b ->
      byte_pos pos * 8 <= a ->
      b <= (byte_pos pos + (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8)) * 8 ->
      AbsArray.slice (BProp.to_bits bf) a b =
        AbsArray.slice
          (AbsArray.slice (BProp.to_bits bf)
             (byte_pos pos * 8)
             ((byte_pos pos + (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8)) * 8))
          (a - byte_pos pos * 8)
          (b - byte_pos pos * 8).
  Proof.
    intros. 
    erewrite AbsArray.slice_smaller.
    shelve.
    - apply H1.
    - apply H0.
    - apply H2.
    - rewrite BProp.to_bits_len. unfold BA.len.
      lia.
      Unshelve. auto.
  Qed.
      
  Lemma put_n_bits_non_inter : forall (n : nat),
      encode_non_inter _ _ (put_n_bits n).
  Proof.
    intros.
    unfold encode_non_inter.  intros.
    simpl_put_n_bits H.
    inversion H.  subst.
    
    (* First, we consider the bytes outside

      | ---- | ---- | ---- | ---- | ---- |
               ^              ^
      In this case, byte 0 and byte 4 should not change.
      We first argue that. those before, and after the bytes read
      and written to  should not change
     *)
    eassert (G0 := (div_plus_one 7 (ByteIdx_to_nat (byte_off pos) + n))). 
    
    eassert (J0 := put_k_bytes_non_inter_helper _ _ _ _ _ E2).

    eassert (F1 :=  several_byte_equiv  bf bf'
                      (put_k_bytes_len _ _ _ _ _ E2)).

    rewrite PeanoNat.Nat.leb_le in E.
    assert (byte_pos pos <= buf_len bf).
    { unfold BA.to_nat, BA.len in E. lia. }

    assert (forall idx : nat, 0 <= idx -> idx < byte_pos pos -> byte_get bf idx = byte_get bf' idx).
    { intros. apply J0. auto. } 
    eassert (F2 := F1 
                     0 (byte_pos pos)
                     (PeanoNat.Nat.le_0_l _)
                     (PeanoNat.Nat.le_0_l _)
                     H0 H1).

    assert (forall idx : nat,
               Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 + byte_pos pos <= idx ->
               idx < buf_len bf -> byte_get bf idx = byte_get bf' idx).
    { intros.  apply J0. auto. }
    eassert (F3 := F1 
                     (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 + byte_pos pos)
                     (buf_len bf)
                     (PeanoNat.Nat.le_0_l _)
                     (read_k_bytes_len_le _ _ _ _ E1)
                     (le_n _)
                     H2). 

    (* Then, we argue that within the bytes read, they should remain
       the same in certain bit positions.

       We need to prove that put_k_bytes slice-equal the nat.
       Note we have read_k_equals_slice
     *)
          
    eassert (G1 := put_in_byte_left_non_inter
                     _
                     (ByteIdx_to_nat (byte_off pos))
                     n
                     n0
                     a
                     (read_k_bytes_le _ _ _ _ E1)
                     pf
                     G0
            ).
    eassert (G2 := put_in_byte_right_non_inter
                     (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                     (ByteIdx_to_nat (byte_off pos))
                     n
                     n0
                     a
                     G0
            ).
    assert (G3' := read_k_bytes_len_le _ _ _ _ E1). 
    rewrite PeanoNat.Nat.add_comm in G3'.
    eassert (G3 := read_k_equals_slice _ _ _ _ E1).

    assert (G4' := read_k_bytes_le _ _ _ _ E1). 
    eassert (G4 := put_k_equals_slice _ _ _ _ _
                     (put_few_bits_le _ _ _ _ _ G0 G4' pf) G3' E2).
     
    (* We could break the condictions down.
       Here, the thing we want to prove is that

       Equiv_b bf bf' (byte_pos pos) (pos) /\
       Equiv_b bf bf' (of_nat (to_nat pos + n)) m0
     *)
    (* That length bf' = length bf *)
    assert (L0 := put_k_bytes_len _ _ _ _ _ E2). 

 
    remember  (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8) as m0. 
    assert (EQ.equiv_b bf bf' (pos_con (byte_pos pos) I0) pos
              (pos_con (byte_pos pos) I0) pos /\
              EQ.equiv_b bf bf'
                (BA.of_nat (BA.to_nat pos + n)) (pos_con (byte_pos pos + m0) I0)
                (BA.of_nat (BA.to_nat pos + n)) (pos_con (byte_pos pos + m0) I0)).
    { unfold EQ.equiv_b, EQ.to_bool_list.

      (* Here, there is an easy lemma that we should have, is that
         if two buffers are of the same length, then
         valid_pair bf p1 p2 ->
         valid pair bf' p1 p2.
       *)
      assert (R13 : byte_pos pos * 8 <= (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos))).
      {  apply PeanoNat.Nat.le_add_r. }

      assert (EQ.valid_pos_pair bf {| byte_pos := byte_pos pos; byte_off := I0 |} pos).
      { unfold EQ.valid_pos_pair, BA.to_nat, BA.len. simpl. simpl_nat .

        split; auto; try lia.
      } 
      eassert (H4 := valid_pair_eq_len _ _ _ _ L0 H3).

      assert (EQ.valid_pos_pair bf (BA.of_nat (BA.to_nat pos + n))
                (pos_con (byte_pos pos + m0) I0)).
      { unfold EQ.valid_pos_pair.
        rewrite BProp.to_of_nat.
        unfold BA.to_nat, BA.len. simpl. simpl_nat.
        lia.
      }
      eassert (H6 := valid_pair_eq_len _ _ _ _ L0 H5).
      rewrite EQ.valid_pos_pair_dec in H3, H4, H5, H6.
      rewrite H3, H4, H5, H6.

      subst.
      assert (R14 : byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos) <=
                      (byte_pos pos +
                         (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8) ) * 8).
      { lia. } 
      
      rewrite PeanoNat.Nat.add_comm in G3'.
      eassert (R1 := bytebuffer_slice_helper _ _ _ _ _ G3'
                       R13 (PeanoNat.Nat.le_refl _) R14).
      
      assert (R22 :  (byte_pos pos * 8) <=
                       (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos) + n)).
      { rewrite <- PeanoNat.Nat.add_assoc.  apply PeanoNat.Nat.le_add_r. }
      assert (R23 : (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos) + n) <=
                      ((byte_pos pos +  (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8) ) * 8)).
      { lia. } 
      
      eassert (R2 :=  bytebuffer_slice_helper _ _ _ _ _ G3'
                        R23 R22 (PeanoNat.Nat.le_refl _)).
      rewrite L0 in G3'.
      
      eassert (R1' := bytebuffer_slice_helper _ _ _ _ _ G3'
                        R13 (PeanoNat.Nat.le_refl _) R14).
      eassert (R2' := bytebuffer_slice_helper _ _ _ _ _ G3'
                        R23 R22 (PeanoNat.Nat.le_refl _)).
 
      rewrite BProp.to_of_nat.
      unfold BA.to_nat. Opaque Nat.div. simpl. simpl_nat.  
      
      rewrite R1, R1', R2, R2'.
      remember  (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8) as m0. 
      rewrite <- G3, <- G4. 
      
      rewrite PeanoNat.Nat.sub_diag.
      rewrite PeanoNat.Nat.mul_add_distr_r.
      rewrite <- PeanoNat.Nat.add_assoc.
      repeat rewrite (PeanoNat.Nat.add_comm (byte_pos pos * 8)).
      repeat rewrite PeanoNat.Nat.add_sub.  
       
      rewrite G1, G2. auto.
    }
    destruct H3.
    split.
    - eapply EQ.equiv_b_append.
      + apply F2.
      + apply H3.
    - split.
      + eapply EQ.equiv_b_append.
        * apply H4.
        * unfold BProp.pos_end.
          rewrite PeanoNat.Nat.add_comm, <- L0.
          apply F3. 
      + unfold BProp.le_pos.
        rewrite BProp.to_of_nat.
        apply PeanoNat.Nat.le_add_r.
  Qed.

  Lemma put_n_bits_implies_valid_pos_pair : forall n bf bf' pos pos' a z, 
      put_n_bits n bf pos a = Some (bf', pos', z)->
      (EQ.valid_pos_pair bf' pos  (BA.of_nat (BA.to_nat pos + n))).
  Proof.
    intros.
    simpl_put_n_bits H; inversion H; subst. 
    eassert (G0 := (div_plus_one 7 (ByteIdx_to_nat (byte_off pos) + n))).
    assert (G1 := read_k_bytes_len_le _ _ _ _ E1).  
    unfold EQ.valid_pos_pair.
    rewrite BProp.to_of_nat.
    split.
    - apply PeanoNat.Nat.le_add_r.
    - eapply PeanoNat.Nat.le_trans.
      + unfold BA.to_nat.
        rewrite <- PeanoNat.Nat.add_assoc.
        apply PeanoNat.Nat.add_le_mono_l. apply G0.
      + unfold BA.len.
        assert (L0 := put_k_bytes_len _ _ _ _ _ E2).
        rewrite <- L0.
        lia. 
  Qed.
      
  Lemma put_n_bits_consistent : forall n, encode_consistent _ _ (put_n_bits n).
  Proof.
    intros. unfold encode_consistent. intros.
    
    assert (V1 := put_n_bits_implies_valid_pos_pair _ _ _ _ _ _ _ H).
    assert (V2 := put_n_bits_implies_valid_pos_pair _ _ _ _ _ _ _ H0).

    unfold EQ.equiv_b,  EQ.to_bool_list.
    rewrite EQ.valid_pos_pair_dec in V1, V2.

    simpl_put_n_bits H; inversion H; subst. 
    simpl_put_n_bits H0; inversion H0; subst. 
    
    rewrite V1, V2. 

    (* This is very similar to the previous proof *)
    eassert (G0 := (div_plus_one 7 (ByteIdx_to_nat (byte_off pos) + n))). 

    assert (G3' := read_k_bytes_len_le _ _ _ _ E1). 
    rewrite PeanoNat.Nat.add_comm in G3'.
    eassert (G3 := read_k_equals_slice _ _ _ _ E1).
    assert (G4' := read_k_bytes_le _ _ _ _ E1). 
    eassert (G4 := put_k_equals_slice _ _ _ _ _
                     (put_few_bits_le _ _ _ _ _ G0 G4' pf) G3' E2).

    eassert (G0' := (div_plus_one 7 (ByteIdx_to_nat (byte_off pos0) + n))). 
    assert (G1' := read_k_bytes_len_le _ _ _ _ E5). 
    rewrite PeanoNat.Nat.add_comm in G1'.
    eassert (G1 := read_k_equals_slice _ _ _ _  E5).
    assert (G2' := read_k_bytes_le _ _ _ _ E5).
    eassert (G2 := put_k_equals_slice _ _ _ _ _
                     (put_few_bits_le _ _ _ _ _ G0' G2' pf) G1' E6).

    repeat rewrite BProp.to_of_nat.
    unfold BA.to_nat.

    assert (L0 := put_k_bytes_len _ _ _ _ _ E2).
    assert (L1 := put_k_bytes_len _ _ _ _ _ E6).
    
    rewrite (bytebuffer_slice_helper bf' pos n
                      (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos))
                      (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos) + n));
      try lia. 
    rewrite (bytebuffer_slice_helper bf0' pos0 n
                      (byte_pos pos0 * 8 + ByteIdx_to_nat (byte_off pos0))
                      (byte_pos pos0 * 8 + ByteIdx_to_nat (byte_off pos0) + n));
      try lia. 

    - rewrite <- G2, <- G4.

      remember  (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8) as m0.
      remember  (Nat.div (ByteIdx_to_nat (byte_off pos0) + n + 7) 8) as m0'.
      repeat rewrite <- PeanoNat.Nat.add_assoc.
      repeat rewrite (PeanoNat.Nat.add_comm (byte_pos pos * 8)).
      repeat rewrite (PeanoNat.Nat.add_comm (byte_pos pos0 * 8)).
      repeat rewrite PeanoNat.Nat.add_sub.
      eapply put_in_byte_consistent; try lia.
  Qed.

  Ltac simpl_read_n_bits H :=
    unfold read_n_bits in H;
    destruct_if_in_new;
    unfold option_bind in H;
    destruct_match_new; inversion H. 

  (* There might be some problem with equiv_b.
   *)
  (* a <= b * 8 ->
   (a + 7) / 8 <= b
   Does this hold? 
 *)
  Lemma div_plus_one_le : forall n a b, a <= b * (S n) ->
                                        Nat.div (a + n) (S n) <= b.
  Proof.
    intros.
    rewrite (PeanoNat.Nat.Div0.div_le_mono _ (b * S n + n)); try lia.
    rewrite PeanoNat.Nat.div_add_l; try lia. 
    rewrite PeanoNat.Nat.div_small; lia. 
  Qed.

  Lemma read_k_bytes_hold : forall (k i : nat) (bf : ByteBuffer),
      k + i <= buf_len bf -> (exists a, read_k_bytes k i bf = Some a).
  Proof.
    intro k. induction k.
    - intros. simpl.  exists 0.
      simpl_nat_in.
      rewrite <- PeanoNat.Nat.leb_le in H. rewrite H. auto.
    - intros. rewrite PeanoNat.Nat.add_succ_comm in H.
      assert (G := IHk (S i) bf H).
      destruct G.
      simpl.
      unfold option_bind, byte_get_nat, option_bind. 

      assert (i < buf_len bf). { lia. }                                 
      destruct (byte_get_in_range i bf H1).
      rewrite H2.
      
      rewrite PeanoNat.Nat.add_1_r, H0.
      exists  (Nat.lor (Nat.shiftl (Byte.to_nat x0) (k * 8)) x).
      auto.
  Qed.

  Lemma nat_to_bl_ext : forall n a a',
      a < Nat.pow 2 n -> a' < Nat.pow 2 n ->
      nat_to_bool_list n a = nat_to_bool_list n a' ->
      a = a'.
  Proof.
    intros. unfold nat_to_bool_list in H1.
    apply List.rev_inj in H1.
    apply PeanoNat.Nat.bits_inj.
    unfold PeanoNat.Nat.eqf.  intros.
    destruct (Compare_dec.le_gt_dec n n0).
    { rewrite <- testbit_eq_le_pow in H, H0.
      rewrite H, H0; auto. }
    { repeat erewrite get_kth_equal_nat_bool.
      - f_equal.  apply H1.
      - auto.
      - auto.
    } 
  Qed.

  Ltac div_pos_helper H := 
    unfold BA.to_nat in H;
    rewrite <- PeanoNat.Nat.add_assoc in H;
    let HH := fresh "HH" in 
    assert (HH := H);
    apply PeanoNat.Nat.le_add_le_sub_l  in HH;
    rewrite <- PeanoNat.Nat.mul_sub_distr_r in HH;
    apply div_plus_one_le in HH; lia.
  
  Lemma read_n_bits_consistent : forall n, decode_consistent _ _ (read_n_bits n).
  Proof.
    unfold decode_consistent.
    
    intros.
    simpl_read_n_bits H; subst. 
    clear H.
    rewrite PeanoNat.Nat.leb_le in E. 
    
    split.
    - unfold BProp.le_pos.
      rewrite BProp.to_of_nat. lia.
    - intros.  assert (LE := EQ.equiv_b_eq_len H).
      unfold BProp.pos_to_len in LE.
      rewrite BProp.to_of_nat, PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub in LE.
      assert (LE2 := EQ.equiv_b_implies_valid_pair H).
      unfold EQ.valid_pos_pair in LE2. split_and.  

      assert (pos0' = BA.of_nat (BA.to_nat pos0 + n)).
      { rewrite <- (BProp.of_to_nat pos0').
        f_equal.  lia. } 
      clear LE.
      
      subst. 
      unfold EQ.equiv_b in H.
      destruct_match_false_new.
      unfold EQ.to_bool_list in E1, E2.
      repeat destruct_if_in_new. subst.
      clear E4. clear E3.
      inversion E1. inversion E2.  subst.  clear E2. clear E1. 

      repeat rewrite BProp.to_of_nat in *.
      
      unfold read_n_bits.
      assert (H3' := H3).
      rewrite <- PeanoNat.Nat.leb_le in H3'. 
      rewrite H3'. 
      
      unfold option_bind. 
      unfold BA.len in H3, H4.
      
      assert (K0 : (Nat.div (ByteIdx_to_nat (byte_off pos0) + n + 7) 8) + (byte_pos pos0)
                   <= buf_len bf0).
      { div_pos_helper H3. }
      
      assert (K1 : (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8) + (byte_pos pos)
                   <= buf_len bf).
      { div_pos_helper H4. }

      destruct (read_k_bytes_hold _ _ _ K0). 
      rewrite H. decode_eq.

      assert (G1 := read_k_equals_slice _ _ _ _ E0).
      assert (G3 := read_k_equals_slice _ _ _ _ H). 

      (* Here, i actually need to turn get-few-bits back into
       nat_to_bool_list. 
       *)
      
      eapply nat_to_bl_ext; try apply get_few_bits_le.

      assert (D1 := div_plus_one 7 (ByteIdx_to_nat (byte_off pos) + n)).
      assert (D2 := div_plus_one 7 (ByteIdx_to_nat (byte_off pos0) + n)). 
      repeat rewrite <- slice_equal_mask; auto. 
      
      rewrite G1, G3.

      unfold BA.to_nat in H5. 
      rewrite  (bytebuffer_slice_helper bf pos n),
        (bytebuffer_slice_helper bf0 pos0 n) in H5; try lia. 
      
      rewrite <- (PeanoNat.Nat.add_assoc (byte_pos pos0 * 8)),
        <- (PeanoNat.Nat.add_assoc (byte_pos pos * 8)) in H5. 
      repeat rewrite (PeanoNat.Nat.add_comm (byte_pos pos * 8)) in H5. 
      repeat rewrite (PeanoNat.Nat.add_comm (byte_pos pos0 * 8)) in H5. 
      repeat rewrite PeanoNat.Nat.add_sub in H5. 

      apply H5.
  Qed.

  Transparent Nat.mul. 
  (* Some helper lemma for byte.of_nat *)
  Lemma byte_of_nat_some : forall a : nat,
      a < Nat.pow 2 8 ->
      exists b, Byte.of_nat a = Some b.
  Proof.
    intros. simpl in H. unfold lt in H.  apply le_S_n in H.
    assert (G := Byte.to_of_nat_option_map a).
    rewrite <- PeanoNat.Nat.leb_le in H. rewrite H in G.
    unfold option_map in G. destruct_match_new.
    exists b. auto.
  Qed.
    
  (* Similar to read-k-bytes-hold *)
  Lemma put_k_bytes_hold : forall (k i : nat) (bf : ByteBuffer) (a : nat),
      (*a < Nat.pow 2 k -> *)
      k + i <= buf_len bf ->
      (exists bf',  put_k_bytes k i bf a = Some bf').
  Proof.
    intro k. induction k.
    - intros. simpl_nat_in. simpl.
      rewrite <- PeanoNat.Nat.leb_le in H. rewrite H.
      exists bf. auto.
    - intros. Opaque Nat.mul. simpl.
      Transparent Nat.mul.
      rewrite PeanoNat.Nat.shiftr_land.
      unfold mask0.
      simpl_nat. assert ((S k * 8 - 8) = k * 8). { lia. }
      rewrite H0. clear H0. 
      rewrite shiftr_shiftl.
      rewrite  PeanoNat.Nat.land_ones. 

      assert (Nat.pow 2 8 <> 0).
      { apply PeanoNat.Nat.pow_nonzero. auto. } 
      assert (U := PeanoNat.Nat.mod_upper_bound
                     (PeanoNat.Nat.shiftr a (k * 8))
                     (Nat.pow 2 8) H0).
      
      destruct (byte_of_nat_some _ U).
      rewrite H1. simpl.

      unfold option_bind.
      assert (i < buf_len bf). { lia. }
      destruct (byte_set_in_range i bf x H2). rewrite H3.
      assert (BL := byte_set_length _ _ _ _ H3).
      rewrite BL in H. 
               
      rewrite PeanoNat.Nat.add_succ_comm in H.      
      destruct (IHk (S i) _ (Nat.land a (PeanoNat.Nat.ones (k * 8))) H).
      rewrite PeanoNat.Nat.add_1_r. 
      rewrite H4. exists x1. trivial.
  Qed.
  
  Import Coq.Logic.ProofIrrelevance. 

  Lemma put_n_bits_len_longer : forall n, encode_len_longer (put_n_bits n).
  Proof.
    intros. unfold encode_len_longer. intros.
    unfold put_n_bits in *.
    destruct_if_in_new.
    destruct_match_dec. unfold option_bind in *.
    repeat destruct_enc. inversion H0.  subst.  clear_redu_all.
    
    assert (Nat.leb (BA.to_nat pos + n) (BA.len bf0) = true).
    { rewrite PeanoNat.Nat.leb_le in *.  lia. }
    rewrite H0.
    assert (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 + byte_pos pos <= buf_len bf0 ).
    { apply read_k_bytes_len_le in E1. unfold BA.len in H.  lia. } 
    eassert (G := read_k_bytes_hold
                    (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8)
                    (byte_pos pos) bf0
                    H1).
    destruct G. rewrite H2.
    (* put_k_bytes needs to have something that says
       it will return true. 
     *)
    eassert (G1 := put_k_bytes_hold _ _ _
                     (put_few_bits (Nat.div
                                      (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                        (ByteIdx_to_nat (byte_off pos)) n x a) H1).
    destruct G1.  rewrite H3.
    exists x0. encode_eq. 
  Qed.
    
  Lemma read_put_n_bits : forall (n : nat),
      format_correct_inj_same _ _ (put_n_bits n) (read_n_bits n).
  Proof.
    unfold format_correct_inj_same. intros.
    unfold read_n_bits in H.
    destruct_if_in_new. unfold option_bind in H.
    destruct_match_new.
    Opaque Nat.div.
    inversion H. subst.
    clear H.
        
    unfold put_n_bits.
    rewrite H0, E. 

    destruct_match_dec_goal; try lia.
    clear E1.  
    unfold option_bind. 

    assert (G10 := read_k_bytes_len_le _ _ _ _ E0).
    unfold BA.len in H0.
    rewrite PeanoNat.Nat.mul_cancel_r in H0; auto. 
    rewrite <- H0 in G10. 
    
    destruct (read_k_bytes_hold _ _ _ G10). rewrite H.
  (* Here, we also need something similar to read-k-hold,
     but for put-k-bytes. 
   *)
    destruct (put_k_bytes_hold _ _ _
                    (put_few_bits (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                       (ByteIdx_to_nat (byte_off pos)) n x
                       (get_few_bits (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                          (ByteIdx_to_nat (byte_off pos)) n n0))
                     G10). 
    rewrite H1.
    
    exists x0. split.
    - f_equal. f_equal. apply proof_irrelevance.
    - unfold EQ.equiv_b, EQ.to_bool_list.
      assert (EL :=  put_k_bytes_len _ _ _ _ _ H1).

      assert (G := div_plus_one 7 (ByteIdx_to_nat (byte_off pos) + n)). 
      assert (EQ.valid_pos_pair bf pos (BA.of_nat (BA.to_nat pos + n))).
      { unfold EQ.valid_pos_pair. rewrite BProp.to_of_nat. unfold BA.len, BA.to_nat.
        split; try lia. 
      } 
      assert (EQ.valid_pos_pair x0 pos (BA.of_nat (BA.to_nat pos + n))).
      { unfold EQ.valid_pos_pair. rewrite BProp.to_of_nat. unfold BA.len, BA.to_nat.
        split; try lia. 
      } 

      rewrite EQ.valid_pos_pair_dec in H2, H3. rewrite H2, H3.
      rewrite BProp.to_of_nat.

      erewrite (bytebuffer_slice_helper _ pos n); unfold BA.to_nat; try lia. 
      erewrite (bytebuffer_slice_helper x0 pos n); unfold BA.to_nat; try lia.

      assert (RS := read_k_equals_slice _ _ _ _ E0).

      assert (L1 := read_k_bytes_le _ _ _ _ H). 
      assert ( put_few_bits (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                 (ByteIdx_to_nat (byte_off pos)) n x
                 (get_few_bits (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                    (ByteIdx_to_nat (byte_off pos)) n n0) <
                 Nat.pow 2 (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)).
      { apply put_few_bits_le; auto. }

      rewrite PeanoNat.Nat.add_comm in G10. 
      eassert (PS := put_k_equals_slice _ _ _ _ _ H4 G10 H1). 

      rewrite <- RS, <- PS.
      rewrite <- (PeanoNat.Nat.add_assoc (byte_pos pos * 8)).
      repeat rewrite (PeanoNat.Nat.add_comm (byte_pos pos * 8)).
      repeat rewrite PeanoNat.Nat.add_sub. 

      repeat (rewrite slice_equal_mask; try lia).
      f_equal.
      rewrite get_put_few_bits; lia.
  Qed.
      
(*
  Unrelated:
  Add a flag to the actual parser that would determine which
  say whether the bitstring read is of the same version or not.

  If they are the same version, then we can have a stronger condiction
  that they are bijective. Otherwise, we only proof the weaker version.  

  I think that in most cases, they should be of the same version.

  About length, since if they are of different version, the bytebuffer
  might not be long enough. We can simply change the statement into

  exists min_len, forall bf0, min_len <= BA.len bf0, 
  exists bf0', exists pos0',
    encode bf0 0 a = Some (bf0', pos0', pf).

  This just means you can technically encode it, but does not put any
  restrictions. 
 *)

  Lemma read_n_bits_SameVer (n : nat) : 
      forall bf pos pos' flg z,
        read_n_bits n bf pos = Some (z, pos', flg ) ->
        flg = SameVer.
  Proof.
    intros. unfold read_n_bits in H.
    destruct_if_in_new. unfold option_bind in H.
    destruct_enc.  inversion H.  auto. 
  Qed.

  Lemma put_n_bits_pos_n n :
    forall {bf bf' pos pos' z pf},
      put_n_bits n bf pos z = Some (bf', pos', pf) ->
      BA.to_nat pos + n = BA.to_nat pos'.
  Proof.
    intros.
    unfold put_n_bits in H.
    destruct_if_in_new. destruct (Compare_dec.lt_dec z (Nat.pow 2 n)).
    - unfold option_bind in H. repeat  destruct_enc.
      inversion H.
      rewrite BProp.to_of_nat. lia.
    - inversion H.
  Qed.

    (* Here, we can put-n-bits as long as the remaning buffer 
     is longer than n. Now, we can actually form a put-n-bit
     out of thin air. The thing is that BA.len bf is dependent on 
     the position pos. But it should not be a big deal. 
 *)
  Lemma put_n_bits_valid_if n : forall bf pos a pf_a,
      BA.to_nat pos + n + 7 <= BA.len bf ->
      exists bf' pos', put_n_bits n bf pos a = Some (bf', pos', pf_a) /\ 
                         BA.to_nat pos' <= BA.to_nat pos + (n + 7).
  Proof.
    intros.
    assert ( BA.to_nat pos + n  <= BA.len bf). { lia. } 
    eassert (G00 := proj2 (PeanoNat.Nat.leb_le _ _) H0).
    eassert (G0 := proj2 (PeanoNat.Nat.ltb_lt _ _ ) pf_a). 
    unfold put_n_bits.
    rewrite G00.
    destruct (Compare_dec.lt_dec a (Nat.pow 2 n)); try lia.
    unfold option_bind.  

    assert (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8 + byte_pos pos <= buf_len bf ). 
    { unfold BA.to_nat in H.  unfold BA.len in H.
      assert (HE := PeanoNat.Nat.Div0.div_le_mono (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos) + n + 7) (buf_len bf * 8) 8 H). 
      assert (8 <> 0). { lia. } 

      assert (HE1 := PeanoNat.Nat.div_mul (buf_len bf) 8 H1).
      
      assert (HE3 := PeanoNat.Nat.div_add_l (byte_pos pos) 8
                       (ByteIdx_to_nat (byte_off pos) + n + 7) H1). 
      assert (byte_pos pos * 8 + ByteIdx_to_nat (byte_off pos) + n +
                7 = byte_pos pos * 8 +
                      (ByteIdx_to_nat (byte_off pos) + n + 7)). { lia. }
      rewrite H2 in HE. 
      
      rewrite HE3 in HE. lia. 
      
    } 
    eassert (G := read_k_bytes_hold
                    (Nat.div (ByteIdx_to_nat (byte_off pos) + n + 7) 8)
                    (byte_pos pos) bf
                    H1).
    destruct G.  rewrite H2.

    eassert (G1 := put_k_bytes_hold _ _ _
                     (put_few_bits (Nat.div
                                      (ByteIdx_to_nat (byte_off pos) + n + 7) 8 * 8)
                        (ByteIdx_to_nat (byte_off pos)) n x a)
                     H1).
    destruct G1.  rewrite H3.
    exists x0. exists (BA.of_nat (BA.to_nat pos + n)).
    split. 
    - encode_eq.
    - rewrite BProp.to_of_nat.  lia. 
  Qed.
  
    
  (* This could be applied through basic_encode_len_longer  *)
  Lemma read_put_n_bits_diff :  forall (n : nat),
      format_correct_inj_diff _ _ (put_n_bits n) (read_n_bits n)  (n_nat_to_len n).
  Proof.
    intros. 
    unfold format_correct_inj_diff. intros.
    assert (G := read_n_bits_SameVer _ _ _ _ _ _ H).  subst.
    exists (n + 7). intros.

    rewrite PeanoNat.Nat.add_assoc in H0. 
    eassert (G1 :=  put_n_bits_valid_if n bf0 _ _ pf H0).
    destruct_ex. split_and.
    right. 
    exists x. exists x0. 
    split; auto. 
  Qed.

  Lemma put_n_bits_to_len_correct : forall n : nat,
      format_to_len_correct  _ _ (put_n_bits n) (read_n_bits n) (n_nat_to_len n).
  Proof.
    unfold format_to_len_correct. split; intros. 
    - unfold n_nat_to_len. f_equal. unfold put_n_bits in H.
      destruct_if_in_new. unfold option_bind in H.
      destruct_match_dec_new. 
      repeat destruct_enc. inversion H.
      rewrite BProp.to_of_nat.  lia.
    - unfold n_nat_to_len.  exists n. auto.  
  Qed.
    
  Ltac rw_max_len N_LEN :=
    unfold read_n_nat, put_n_nat;
    unfold INT_MAX_LEN in N_LEN;
    rewrite <- PeanoNat.Nat.leb_le in N_LEN; rewrite N_LEN.
  
  Lemma basic_n_bit_format_correct n (pf_n : n <= INT_MAX_LEN)
    : format_correct (put_n_nat n) (read_n_nat n) (n_nat_to_len n).
  Proof.
    unfold format_correct.
    rw_max_len pf_n.
    split. apply put_n_bits_consistent.
    split. apply read_n_bits_consistent.
    split. apply put_n_bits_non_inter.
    split. apply put_read_n_bits.
    split. apply read_put_n_bits.
    split. apply read_put_n_bits_diff.
    apply put_n_bits_to_len_correct.
  Qed.

  Lemma read_n_nat_SameVer n :
    forall a bf pos pos' flg,
      (read_n_nat n) bf pos = Some (a, pos', flg) ->
      flg = SameVer.
  Proof.
    intros. unfold read_n_nat in H.
    destruct_if_in_new. 
    eapply read_n_bits_SameVer. apply H.
  Qed.
  
End BPP.

