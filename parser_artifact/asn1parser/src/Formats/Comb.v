Require Import
  ASN1Parser.AbsArray
  ASN1Parser.Array.BitRep.

Module EQ := EquivBits_Impl BA BProp.

Inductive Flg :=
| SameVer
| DiffVer.

Definition flg_add : Flg -> Flg -> Flg :=
  fun f1 f2 => 
    match f1, f2 with
    | SameVer, SameVer => SameVer
    | _, _ => DiffVer
    end.

Definition add_opt (n1 n2 : option nat) : option nat :=
  match n1, n2 with
  | Some n1', Some n2' => Some (n1' + n2')
  | _, _ => None
  end.

Definition INT_MAX_LEN := 48. 

Definition dec_P {A : Set} (P : A -> Prop) := forall a : A, sumbool (P a) (~(P a)).

Definition sumbool_app {A B : Set} {P1 : A -> Prop} {P2 : A -> B -> Prop}
      : dec_P P1 -> (forall a : A, P1 a -> dec_P (P2 a)) ->
        dec_P (fun z => P1 (fst z) /\ (P2 (fst z) (snd z))). 
  unfold dec_P in *. intros. 
  destruct a. simpl.
  destruct (H a).
  - destruct (H0 a p b).
    + left. auto.
    + right. intro. destruct H1. auto.
  - right. intro. destruct H1. auto.
Defined.

Definition sumbool_and1  {P1 P2 : Prop}
  : sumbool P1 (~P1) -> sumbool P2 (~P2)
    -> sumbool (P1 /\ P2) (~(P1 /\ P2)). 
  intros.
  destruct H; destruct H0; try (right; intro; destruct H; auto; discriminate).
  left. auto.
Defined.

Definition Serialize (A : Set) (Pr : A -> Prop) : Type :=
  BA.Buffer -> BA.Pos ->
  forall a : A, option (BA.Buffer * BA.Pos * Pr a).

Definition Parse (A : Set) (Pr : A -> Prop) : Type := 
  BA.Buffer -> BA.Pos ->
  option (sig Pr * BA.Pos * Flg).


Definition encode_cond_type := forall (A : Set) (Pr : A -> Prop)
  (s : Serialize A Pr), Prop.

Definition decode_cond_type := forall  (A : Set) (Pr : A -> Prop)
  (p : Parse A Pr), Prop.

Definition en_decode_cond_type :=
  forall (A : Set) (Pr : A -> Prop) (s : Serialize A Pr) (p : Parse A Pr), Prop.

Definition en_de_tl_cond_type :=
  forall (A : Set) (Pr : A -> Prop) (s : Serialize A Pr) (p : Parse A Pr) (tl : A -> option nat), Prop.

Definition encode_non_inter : encode_cond_type :=
  fun {A : Set} {Pr : A -> Prop} (encode : Serialize A Pr) =>
    forall (a : A) (bf bf' : BA.Buffer) (pos pos' : BA.Pos) (pf : Pr a),
      encode bf pos a = Some (bf', pos', pf) ->
      (EQ.equiv_b bf bf' BProp.pos_zero pos BProp.pos_zero pos /\
         EQ.equiv_b bf bf' pos' (BProp.pos_end bf) pos' (BProp.pos_end bf') /\
         BProp.le_pos pos pos').

Definition encode_consistent : encode_cond_type :=
  fun {A : Set} {Pr : A -> Prop} (encode : Serialize A Pr) =>
    forall (a : A) (bf bf' : BA.Buffer) (pos pos' : BA.Pos)
      (bf0 bf0' : BA.Buffer) (pos0 pos0' : BA.Pos) (pf : Pr a),
      
      encode bf pos a = Some (bf', pos', pf) ->
      encode bf0 pos0 a = Some (bf0', pos0', pf) ->
      EQ.equiv_b bf' bf0' pos pos' pos0 pos0'.

Definition decode_consistent : decode_cond_type :=  fun  {A : Set} {Pr : A -> Prop}
  (decode : Parse A Pr) => 
    forall (a : A) (bf : BA.Buffer) (pos pos' : BA.Pos) (pf : Pr a) (flg : Flg),
      decode bf pos = Some (exist Pr a pf, pos', flg) ->
      (BProp.le_pos pos pos') /\
        (forall bf0 pos0 pos0',
          EQ.equiv_b bf bf0 pos pos' pos0 pos0' ->
         decode bf0 pos0 = Some (exist Pr a pf, pos0', flg)).

(* The decoder should of the same version *)
Definition format_correct_surj : en_decode_cond_type :=
  fun {A : Set} {P : A -> Prop}
  (encode : Serialize A P) (decode : Parse A P) => 
  forall (a : A) (bf bf' : BA.Buffer) (pos pos': BA.Pos) (pf : P a),  
    encode bf pos a = Some (bf', pos', pf) ->
    decode bf' pos = Some (exist P a pf, pos', SameVer).

(* This is a bit more complicated. If they are the same version, then
   the encode should work. If not, 
 *)
Definition format_correct_inj_same : en_decode_cond_type :=
  fun {A : Set} {P : A -> Prop}
      (encode : Serialize A P) (decode : Parse A P)  =>
  forall (a : A) (bf : BA.Buffer) (pos pos' : BA.Pos) (pf : P a),
    (decode bf pos = Some (exist P a pf, pos', SameVer)) ->
    (forall (bf0 : BA.Buffer),
        BA.len bf0 = BA.len bf ->
        (exists bf0' : BA.Buffer,
            encode bf0 pos a = Some (bf0', pos', pf) /\
              EQ.equiv_b bf bf0' pos pos' pos pos')).

Definition encode_len_longer {A : Set} {P : A -> Prop}
  (encode : Serialize A P) :=
  forall (a : A) (bf bf' : BA.Buffer) (pos pos' : BA.Pos)
    (bf0  : BA.Buffer) (pf : P a),

    BA.len bf <= BA.len bf0 -> 
    encode bf pos a = Some (bf', pos', pf) ->
    exists bf0', encode bf0 pos a = Some (bf0', pos', pf). 

(* Here, doesnt matter if the flg is different or same,
   there is some encoding if we can decode it correctly. 
 *)
Definition get_byte_len n : nat :=
  (Nat.div (n + 7) 8).

Definition format_correct_inj_diff : en_de_tl_cond_type :=
  fun {A : Set} {P : A -> Prop}
      (encode : Serialize A P) (decode : Parse A P)
      (get_len : A -> option nat) => 
    forall (a : A) (bf : BA.Buffer) (pos pos' : BA.Pos) (pf : P a) (flg : Flg),
      (decode bf pos = Some (exist P a pf, pos', flg)) ->
      (exists min_len : nat,
          (forall (pos0 : BA.Pos) (bf0 : BA.Buffer),
              BA.to_nat pos0 + min_len <= BA.len bf0 ->
              (~ (match (get_len a) with
                  | Some a' => get_byte_len a' < Nat.pow 2 14
                  | None => True
                  end)) \/
                (exists (bf0' : BA.Buffer) (pos0' : BA.Pos),
                    (encode bf0 pos0 a = Some (bf0', pos0', pf) /\
                       BA.to_nat pos0' <= BA.to_nat pos0 + min_len)))).

Definition format_to_len_correct : en_de_tl_cond_type :=
  fun {A : Set} {P : A -> Prop} (encode : Serialize A P)
      (decode : Parse A P)
      (to_len : A -> option nat) =>
    (forall (a : A) (bf bf' : BA.Buffer) (pos pos' : BA.Pos) (pf : P a),
      encode bf pos a = Some (bf', pos', pf) -> 
      to_len a = Some (BA.to_nat pos' - BA.to_nat pos)) /\ 
      (forall a bf pos pos' pf flg,
          decode bf pos = Some (exist _ a pf, pos', flg) ->
          exists n, to_len a = Some n).

(* This is the combined correctness definition *)
Definition format_correct  {A : Set} {P : A -> Prop}
  (enc : Serialize A P) (dec : Parse A P) (to_len : A -> option nat) :=
  encode_consistent A P enc /\ decode_consistent A P dec /\
    encode_non_inter A P enc /\
    format_correct_surj A P enc dec /\ format_correct_inj_same A P enc dec /\
    format_correct_inj_diff A P enc dec to_len /\
    format_to_len_correct A P enc dec to_len. 

(* So a correct format is simply a T_Format *)
Record T_Format (T : Set) (T_Cond : T -> Prop)  :=
  mk_format { 
      T_Serial : Serialize T T_Cond ;
      T_Parse : Parse T T_Cond ;
      T_to_len : T -> option nat ;
      T_Correct : format_correct T_Serial T_Parse T_to_len
    }.

(* Here, we simply have parser/serializer combinators, we don't 
   try to use a AbsFormat anymore. Because it is ineffective for 
   the list combinator. 

   We will first write the combinators here, and then 
   the Proofs in CombProp.v
 *)
    
(* For bind_parse, we have two versions, one where flg is ignored,
   the other where flg is considered. 
 *)
(*Definition bindf_parse {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (ParA : Parse A Pa) (f : forall (a : A), Pa a -> Parse B Pb)
  : Parse B Pb :=
  fun bf pos =>
    match (ParA bf pos) with
    | Some (exist _ a pf_Pa, pos', _) =>
        (f a pf_Pa) bf pos' 
    | None => None
    end.
*)

Definition bind_parse  {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (ParA : Parse A Pa)
  (f : forall a : A, Pa a -> Flg -> Parse B Pb) : Parse B Pb :=
  fun (bf : BA.Buffer)
      (pos : BA.Pos) =>
    match ParA bf pos with
    | Some (exist _ a pf_Pa, pos', flg) => f a pf_Pa flg bf pos'
    | None => None
    end.

Definition proj_parse {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (pa : Parse A Pa) (f : A -> B)
  (imp : forall a : A, Pa a -> Pb (f a))
  : Parse B Pb :=
  fun bf pos =>
    match (pa bf pos) with
    | Some (exist _ a pf0, pos', flg) =>
        Some (exist Pb (f a) (imp a pf0), pos', flg)
    | None => None
    end.

Definition return_parse {A : Set} {P : A -> Prop} (a : sig P) (flg : Flg) : Parse A P :=
  fun _ pos => Some (a, pos, flg).

Definition restrict_parse  {A : Set} {P R: A -> Prop} 
  (r_dec : dec_P R)
  (pa : Parse A P) : Parse A R :=
  fun bf pos =>
    match (pa bf pos) with
    | Some (exist _ a _, pos', flg) =>
        match r_dec a with
        | left pf_r => Some (exist R a pf_r, pos', flg)
        | right _ => None
        end
    | None => None
    end.

(* Definitions for serialize *)
Definition restrict_serialize {A : Set} {P R: A -> Prop}
  (r_dec : dec_P R)  (s : Serialize A P)
  : Serialize A R :=
  fun bf pos a =>
    match r_dec a  with
    | left pf  => match s bf pos a with
                 | Some (bf', pos', _) => Some (bf', pos', pf)
                 | None => None
                 end
    | right _ => None
    end.

Definition proj_serialize {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop}
  (s : Serialize A P1) (f : B -> A)
  (p2_dec : dec_P P2)
  : Serialize B P2 :=
  fun bf pos b =>
    match p2_dec b with
    | left pf => match s bf pos (f b) with
                | Some (bf', pos', _) => Some (bf', pos', pf)
                | None => None
                end
    | right _ => None
    end.


(* The problem here is that sb is not good enough, 
     We already know that serialize A satisfy the property that 
     it only takes a which satisfies P. 
 *)
Definition sigma_serialize {A B : Set} {P1 : A -> Prop} (sa : Serialize A P1)
  (P2 : A -> B -> Prop)
  (sb : forall a : A, P1 a -> Serialize B (P2 a))
  : Serialize (A * B) (fun z => P1 (fst z) /\ (P2 (fst z) (snd z))) :=
  fun bf pos z =>
    match sa bf pos (fst z) with
    | Some (bf', pos', pf_P1) =>
        match sb (fst z) pf_P1 bf' pos' (snd z) with
        | Some (bf'', pos'', pf_P2) => Some (bf'', pos'', conj pf_P1 pf_P2)
        | None => None
        end
    | None => None
    end.

Definition append_serialize
  {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop}
  (sa : Serialize A P1) (sb : Serialize B P2)
  :  Serialize (A * B) (fun z => P1 (fst z) /\ P2 (snd z)) :=
  fun bf pos z =>
    match sa bf pos (fst z) with
    | Some (bf', pos', pf_P1) =>
        match sb bf' pos' (snd z) with
        | Some (bf'', pos'', pf_P2) => Some (bf'', pos'', conj pf_P1 pf_P2)
        | None => None
        end
    | None => None
    end.

Definition sigma_parse
  {A B : Set} {P1 : A -> Prop}
  (par1 : Parse A P1)
  (P2 : A -> B -> Prop)
  (pser2 : forall (a : A), P1 a -> Parse B (P2 a)) :=
  (bind_parse par1
     (fun a pf_Pa flg1 =>
        bind_parse (pser2 a pf_Pa)
          (fun b pf_Pb flg2 =>
             return_parse
               (exist
                  (fun z => P1 (fst z) /\ P2 (fst z) (snd z))
                  (a, b)
                  (conj pf_Pa pf_Pb))
               (flg_add flg1 flg2)))).

Definition append_parse
  {A B : Set}  {P1 : A -> Prop} {P2 : B -> Prop}
  (par1 : Parse A P1)
  (par2 : Parse B P2) := 
  (bind_parse par1
     (fun a pf_Pa flg1 =>
        bind_parse par2
          (fun b pf_Pb flg2 =>
             return_parse
               (exist
                  (fun z => P1 (fst z) /\ P2 (snd z))
                  (a, b)
                  (conj pf_Pa pf_Pb))
               (flg_add flg1 flg2)))).

Definition sigma_to_len
  {A A' : Set} 
  (tl1 : A -> option nat)
  (tl2 : forall (a : A), (A' -> option nat)) :=
  (fun z : A * A' =>
     add_opt (tl1 (fst z))
           (tl2 (fst z) (snd z))).

Definition append_to_len
  {A A' : Set} 
  (tl1 : A -> option nat)
  (tl2 : A' -> option nat) := 
  (fun z : A * A' =>
     add_opt (tl1 (fst z))
           (tl2 (snd z))).      


Lemma get_byte_len_mono n m : n <= m -> get_byte_len n <= get_byte_len m.
  intros. unfold get_byte_len.
  apply PeanoNat.Nat.Div0.div_le_mono. Lia.lia.
Qed.
