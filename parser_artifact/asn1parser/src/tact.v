Require Import   
        Lia.

Ltac rewrite_lt_le :=
  match goal with
  | [ H : Nat.ltb ?x ?y = _ |- _ ]  =>
      let R_lt_le := fresh "Rl" in
      assert (R_lt_le := H);
      try rewrite (PeanoNat.Nat.ltb_lt) in H;
      try rewrite (PeanoNat.Nat.ltb_ge) in H
  | [ H : Nat.leb ?x ?y = _ |- _ ]  =>
      let R_lt_le := fresh "Rl" in
      assert (R_lt_le := H);
      try rewrite (PeanoNat.Nat.leb_le) in H;
      try rewrite (PeanoNat.Nat.leb_gt) in H
  end.

Ltac destruct_if_in :=
  match goal with
  | [ H : context[ (if ?X then _ else _) = _] |- _ ] =>
      let E := fresh "E" in
      destruct X eqn:E; simpl in *; try inversion H; subst
  end.

Ltac destruct_if_goal :=
  match goal with
  | [ |- context[ (if ?X then _ else _ )] ] =>
      let E := fresh "E" in 
      destruct X eqn:E; simpl; subst; auto
  end.

Ltac destruct_match :=
  match goal with
  | [ H : context[ match ?X with
                   | Some _ => _
                   | None  => _
                   end = Some _ ] |- _ ] =>
      let E := fresh "E" in 
      destruct X eqn:E; try inversion H; try discriminate
  end. 

Ltac destruct_match_goal :=
  match goal with
  | [ |- context[ match ?X with
                    | Some _ => _
                    | None  => _
                    end ] ] =>
      let E := fresh "E" in 
      destruct X eqn:E
  end.

Ltac split_and :=
  repeat match goal with
    | [ H :  ?a /\ ?b  |- _ ] =>
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        destruct H as [H0 H1]
    end.

Ltac destruct_match_false :=
  repeat match goal with
    | [ H : context[ match ?X with
                     | Some _ => _
                     | None  => False
                     end ] |- _ ] =>
        let E := fresh "E" in 
        destruct X eqn:E; try destruct H
    end.

Ltac destruct_match_dec :=
  match goal with
  | [ H : context[ match ?X with
                   | left _ => _
                   | right _  => _
                   end = Some _ ] |- _ ] =>
      let E := fresh "E" in 
      destruct X eqn:E; try inversion H; try discriminate; try subst
  end. 

Ltac destruct_match_dec_goal :=
  match goal with
  | [ |- context[ match ?X with
                  | left _ => _
                  | right _  => _
                  end = Some _ ] ] =>
      let E := fresh "E" in 
      destruct X eqn:E; auto; try discriminate
  end. 

Ltac destruct_let :=
  match goal with
  | [ H : context [ let (_, _) := ?c in _ ] |- _ ] =>
      destruct c
  end.  

Ltac destruct_let_goal :=
  match goal with
  | [ |- context [ let (_, _) := ?c in _ ] ] =>
      destruct c
  end.  

Ltac destruct_exists H :=
  match type of H with
  | exists _, _ =>
      let x := fresh "x" in
      let H' := fresh "H" in 
      destruct H as [x H']; try (destruct_exists H')
  | _ => idtac
  end.


Ltac destruct_if_in_new :=
  match goal with
  | [ H : context[ (if ?X then _ else _) = _] |- _ ] =>
      let E := fresh "E" in
      destruct X eqn:E; try discriminate
  end.

Ltac destruct_match_dec_new :=
  match goal with
  | [ H : context[ match ?X with
                   | left _ => _
                   | right _  => _
                   end = Some _ ] |- _ ] =>
      let E := fresh "E" in 
      destruct X eqn:E; try discriminate
  end. 

Ltac destruct_match_new :=
  match goal with
  | [ H : context[ match ?X with
                   | Some _ => _
                   | None  => _
                   end = Some _ ] |- _ ] =>
      let E := fresh "E" in 
      destruct X eqn:E; try discriminate
  end.

Ltac clear_redu :=
  match goal with
  | [ H : context[ Some (?x, ?y, ?z1) = Some (?x, ?y, ?z2) ] |- _ ] =>
      match (type of z1) with
      | ?T => 
          match (type of z2) with
          | T => clear H
          | _ => idtac
          end
      | _ => idtac
      end
  end.

Ltac clear_redu_d :=
  match goal with
  | [ H : context[ Some (exist ?R ?x _ , ?p) = Some (exist ?R ?x _, ?p) ] |- _ ] =>
      clear H
  end.

Ltac clear_redu_all := repeat clear_redu; repeat clear_redu_d.

Ltac simpl_0_bit :=
  repeat match goal with
    | [ |- context[ Nat.land 0 _ ] ] => rewrite PeanoNat.Nat.land_0_l
    | [ |- context[ Nat.land _ 0 ] ] => rewrite PeanoNat.Nat.land_0_r
    | [ |- context[ Nat.lor 0 _ ] ] => rewrite PeanoNat.Nat.lor_0_l
    | [ |- context[ Nat.lor _ 0 ] ] => rewrite PeanoNat.Nat.lor_0_r
    | [ |- context[ Nat.shiftr 0 _] ] => rewrite PeanoNat.Nat.shiftr_0_l
    | [ |- context[ Nat.shiftr _ 0] ] => rewrite PeanoNat.Nat.shiftr_0_r
    | [ |- context[ Nat.shiftl 0 _] ] => rewrite PeanoNat.Nat.shiftl_0_l
    | [ |- context[ Nat.shiftl _ 0] ] => rewrite PeanoNat.Nat.shiftl_0_r
    end.

Ltac simpl_nat :=
  repeat match goal with
    | [ |- context[ 0 + _ ] ] => rewrite PeanoNat.Nat.add_0_l
    | [ |- context[ _ + 0 ] ] => rewrite PeanoNat.Nat.add_0_r
    | [ |- context[ 0 * _ ] ] => rewrite PeanoNat.Nat.mul_0_l
    | [ |- context[ _ * 0 ] ] => rewrite PeanoNat.Nat.mul_0_r
    | [ |- context[ 1 * _ ] ] => rewrite PeanoNat.Nat.mul_1_l
    | [ |- context[ _ * 1 ] ] => rewrite PeanoNat.Nat.mul_1_r
    | [ |- context[ 0 <= _] ] => apply PeanoNat.Nat.le_0_l
    | [ |- context[ _ - 0 ] ] => rewrite PeanoNat.Nat.sub_0_r
    | [ |- context[ 0 - _ ] ] => rewrite PeanoNat.Nat.sub_0_l
    end.

Ltac simpl_nat_in :=
  repeat match goal with
    | [ H : context[ 0 + _ ] |- _ ] => rewrite PeanoNat.Nat.add_0_l in H
    | [ H : context[ _ + 0 ] |- _ ] => rewrite PeanoNat.Nat.add_0_r in H
    | [ H : context[ 0 * _ ] |- _ ] => rewrite PeanoNat.Nat.mul_0_l in H
    | [ H : context[ _ * 0 ] |- _ ] => rewrite PeanoNat.Nat.mul_0_r in H
    | [ H : context[ 1 * _ ] |- _ ] => rewrite PeanoNat.Nat.mul_1_l in H 
    | [ H : context[ _ * 1 ] |- _ ] => rewrite PeanoNat.Nat.mul_1_r in H
    | [ H : context[ _ - 0 ] |- _ ] => rewrite PeanoNat.Nat.sub_0_r in H
    | [ H : context[ 0 - _ ] |- _ ] => rewrite PeanoNat.Nat.sub_0_l in H
    end.

Require Import ProofIrrelevance.

Ltac encode_eq := f_equal; f_equal; apply proof_irrelevance.
Ltac decode_eq := f_equal; f_equal; f_equal; apply subset_eq_compat; auto.

Ltac destruct_enc := destruct_match_new; repeat destruct_let.

Ltac destruct_ex :=
  repeat (match goal with
          | [ H : exists _ , _ |- _ ] => destruct H
          end).
