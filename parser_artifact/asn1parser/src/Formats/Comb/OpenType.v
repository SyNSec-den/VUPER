Require Import
          ASN1Parser.Formats.Comb
          ASN1Parser.Formats.CombFormat
          ASN1Parser.Array.ByteBuffer
          ASN1Parser.Array.BitRep
          ASN1Parser.Formats.Term.Boolean
          ASN1Parser.Formats.Comb.HelperComb.

(* Since we need open type in Choice Extension as well,
   we separate it into a new file. 
 *)

(* This function would return how many bytes is needed *)
Definition get_remaining_bits n : nat :=
  (get_byte_len n) * 8 - n. 


(* Here, we need to calculate the length upfront because
   the length could be encoded into 1 or 2 bytes.
 *)
Require Import ASN1Parser.Formats.Term.LengthDet.

Definition det_enc := T_Serial _ _ uncons_len_det_format.
Definition det_dec := T_Parse _ _ uncons_len_det_format.

Definition open_typ_serialize {A : Set} {P : A -> Prop}
  (ser : Serialize A P) (get_len_ser : A -> option nat)
  : Serialize A P := 
  fun bf pos a =>
    opt_bind (get_len_ser a)
      (fun n =>
         match (det_enc bf pos (get_byte_len n)) with
         | Some (bf', pos', _ ) =>
             match (ser bf' pos' a) with
             | Some (bf'', pos'', pf') =>
                 let n' := (BA.to_nat pos'' - BA.to_nat pos') in
                 if (Nat.eqb n n') then
                   let remaining_len := get_remaining_bits n in
                   match (put_n_nat (remaining_len) bf'' pos'' 0) with
                   | Some (bf''', pos''', _) => 
                       Some (bf''', pos''', pf')
                   | None => None
                   end
                 else None
             | None => None
             end
         | None => None
         end  
      ).

(* In order for these to be correct, we will need to prove that
   get_len_ser is correct in terms of its length.

   The problem is we can only generate these function using
   unconventional means. 
 *)

Definition skip_some_bits (n : nat) :=
  match (Compare_dec.le_dec n 48) with
  | left pf_le => 
      (read_n_nat n )
  | right _ => fail_parse
  end.

Definition open_typ_parse {A : Set} {P : A -> Prop}
  (par : Parse A P)
  : Parse A P :=
  fun bf pos => 
    match det_dec bf pos with
    (* here we get the length of bytes *)
    | Some (exist _ n _, pos1, _) =>
        match (par bf pos1) with
        | Some (exist _ a pf_a, pos2, flg) =>
            (* Here, we are checking if the encoding actually 
                 has the correct length. We don't have to be too
                 strict. if it exceeds the open_type restriction,
                 we fail it
             *)
            let pos1_nat := BA.to_nat pos1 in
            let pos2_nat := BA.to_nat pos2 in 
            let bits_read := (pos2_nat -  pos1_nat) in
            if (Nat.eqb (get_byte_len bits_read) n) then
              bind_parse (skip_some_bits (n * 8 - bits_read))
                (fun zs _ _ =>
                   if (Nat.eqb zs 0) then 
                     return_parse (exist P a pf_a) flg
                   else
                     fail_parse)
                bf pos2
            else None
        | None => None
        end
    | None => None
    end.

Definition get_bit_len_8 n :=
  match n with
  | Some n' => Some ((get_byte_len n') * 8)
  | None => None
  end.

(*Eval compute in get_bit_len_8 (Some 14). *)


(* Here, I only read the open type to skip it. 
     Change the read_n_nat into read n bytes.

     Coz obviously if we have n * 8 <= 48 ->
     n <= 6. I can only read 6 bytes. It cannot
     handle a long message.

     So we have to have designated function to skip
     bytes. 
 *)
Lemma skip_byte_helper : 8 <= INT_MAX_LEN.
  unfold INT_MAX_LEN.  Lia.lia.
Qed.

Require Import ASN1Parser.Formats.Term.Unit.

Definition skip_1_byte : Parse unit (fun _ => True) :=
  bind_parse 
    (read_n_nat 8)
    (fun _ _ _ => read_unit).

Fixpoint skip_n_bytes (n : nat) : Parse unit (fun _ => True) := 
  match n with
  | 0 => read_unit
  | S m => bind_parse (skip_n_bytes m)
             (fun _ _ _ => skip_1_byte)
  end.
      
Definition open_type_skip_parse : Parse unit (fun _ => True) :=
  bind_parse (det_dec)
    (fun n _ _ =>
       bind_parse (skip_n_bytes n)
         (fun _ _ _ => read_unit)).

(* The length of a open type, 
   1. The length of len-det
   2. The byte-aligned length of the thing
 *)
Definition open_type_to_len {A : Set} (tl : A -> option nat) (a : A) : option nat
  :=
  opt_bind (tl a)
    (fun n =>
       (* Here n means number of bits *)
       let nb := (get_byte_len n) in
       opt_bind (T_to_len _ _ uncons_len_det_format nb)
         (fun n' => 
            Some (n' + (nb * 8)))).
