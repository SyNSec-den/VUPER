Require Import
          ASN1Parser.tact
          ASN1Parser.AbsArray
          ASN1Parser.Array.BitRep.

Require Import  Coq.Logic.FunctionalExtensionality. 
 
Require Import Lia.

(* Same as PeanoNat.Nat.ones *)
Definition mask0 (m off n : nat) :=
  (Nat.shiftl (PeanoNat.Nat.ones n) (m - off - n)).

Definition mask (m off n : nat) :=
  Nat.lor (mask0 m 0 off) (mask0 m (off + n) (m - off - n)). 

(* Here, we put a (n-bit) from off to a byte a0.
     So we assume a0 is 8 bit, i.e., a0 < 255;
     and a is n-bit, i.e., a < pow 2 n. 
     And off + n <= 8.
     
     We need to update put_few_bits such that it could
     theoretically work with a m-bit integer a0, that we can
     write a n-bit integer a into it. Starting from off-bit

     implicitly we assume
     off + n <= m
     a0 < 2 ^ m, a < 2 ^ n.
 *)
Definition put_few_bits (m : nat) (off n : nat) (a0 : nat) (a : nat)  :=
  (Nat.lor (Nat.land (mask m off n) a0)
     (Nat.shiftl a (m - off - n))).

(* Here, I can read n-bits from a from position off  *)
Definition get_few_bits (m : nat) (off n : nat) (a : nat) :=
  (Nat.land (PeanoNat.Nat.ones n) (Nat.shiftr a (m - off - n))).


(* Here, i can equal len bf because we can very much be at
the end of the buffer *)
Fixpoint put_k_bytes (k i : nat) (bf : ByteBuffer) (a : nat) : option ByteBuffer :=
  match k with
  | 0 =>
      if (Nat.leb i (buf_len bf))
      then Some bf
      else None
  | S k' =>
      b <-opt Byte.of_nat (Nat.shiftr (Nat.land a (mask0 (k * 8) 0 8)) (k' * 8)) ;;
      bf' <-opt byte_set bf i b ;;
      put_k_bytes k' (i + 1) bf' (Nat.land a (PeanoNat.Nat.ones (k' * 8)))
  end.

Fixpoint read_k_bytes (k : nat) (i : nat) (bf : ByteBuffer) : option nat :=
  match k with
  | 0 =>
      if (Nat.leb i (buf_len bf))
      then Some 0
      else None
  | S k' =>
      b <-opt bf [[ i ]] ;;
      n0 <-opt read_k_bytes k' (i + 1) bf ;;
      Some (Nat.lor (Nat.shiftl b (k' * 8)) n0)
  end.

Require Import ASN1Parser.Formats.Comb.

Definition put_n_bits (n : nat)
  : Serialize nat (fun z => z < Nat.pow 2 n) :=
  fun bf pos a =>
    let new_pos_nat := BA.to_nat pos + n in
    if (Nat.leb (new_pos_nat) (BA.len bf)) then
      match (Compare_dec.lt_dec a (Nat.pow 2 n)) with
      | left pf =>
          let new_pos := BA.of_nat new_pos_nat in
          let off :=  ByteIdx_to_nat (byte_off pos) in
          let num_bits :=  ByteIdx_to_nat (byte_off pos) + n in
          let num_bytes := (Nat.div (num_bits + 7) 8) in
          (* We could prove that num_bytes shall be smaller than
                 56. Or, num-bits is smaller than n + 8.
           *)
          a0 <-opt (read_k_bytes (num_bytes) (byte_pos pos) bf) ;;
          let a1 := put_few_bits (num_bytes * 8) off n a0 a in 
          bf' <-opt put_k_bytes num_bytes (byte_pos pos) bf a1 ;;
          Some (bf', new_pos, pf)
               
      | right _ => None
      end
    else None.

Lemma get_few_bits_le : forall (m off n a : nat),
    get_few_bits m off n a < Nat.pow 2 n.
Proof.
  intros.
  unfold get_few_bits.
  rewrite PeanoNat.Nat.land_comm, PeanoNat.Nat.land_ones.
  apply PeanoNat.Nat.mod_upper_bound.
  apply PeanoNat.Nat.pow_nonzero.
  auto.
Qed.

Definition read_n_bits (n : nat)
  : Parse nat (fun z => z < Nat.pow 2 n) :=
  fun bf pos =>
    let new_pos_nat := BA.to_nat pos + n in
    if (Nat.leb (new_pos_nat) (BA.len bf)) then
      let new_pos := BA.of_nat new_pos_nat in
      let off :=  ByteIdx_to_nat (byte_off pos) in
      let num_bits := off + n in
      let num_bytes := (Nat.div (num_bits + 7) 8) in

      a0 <-opt (read_k_bytes (num_bytes) (byte_pos pos) bf) ;;
      Some (exist _ (get_few_bits (num_bytes * 8) off n a0)
              ( get_few_bits_le (num_bytes * 8) off n _ ),
          new_pos, SameVer)
    else None.

Definition put_n_nat (n : nat) 
  : Serialize nat (fun z => z < Nat.pow 2 n) :=
  fun bf pos a =>
    if (Nat.leb n 48) then
      put_n_bits n bf pos a
    else
      None.
  
Definition read_n_nat (n : nat)
  : Parse nat (fun z => z < Nat.pow 2 n) :=
  fun bf pos => 
    if (Nat.leb n 48) then
      read_n_bits n bf pos
    else
      None.

Definition n_nat_to_len (n : nat) : nat -> option nat :=
  fun _ => Some n.
