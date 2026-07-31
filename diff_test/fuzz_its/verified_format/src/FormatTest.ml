
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type empty_set = |

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

type comparison =
| Eq
| Lt
| Gt

(** val id : __ -> __ **)

let id x =
  x

type 'a sig0 =
| Exist of 'a

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type char_list = char list
(** val pow : int -> int -> int **)

let rec pow n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Stdlib.Int.succ 0)
    (fun m0 -> ( * ) n0 (pow n0 m0))
    m



module Nat =
 struct
  (** val pred : int -> int **)

  let pred n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun u -> u)
      n0

  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n0

  (** val double : int -> int **)

  let double n0 =
    add n0 n0

  (** val mul : int -> int -> int **)

  let rec mul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n0

  (** val even : int -> bool **)

  let rec even n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n1)
      n0

  (** val odd : int -> bool **)

  let odd n0 =
    negb (even n0)

  (** val div2 : int -> int **)

  let div2 = fun n -> n/2

  (** val shiftl : int -> int -> int **)

  let rec shiftl a n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n1 -> double (shiftl a n1))
      n0

  (** val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int **)

  let rec bitwise op n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op (odd a) (odd b) then Stdlib.Int.succ 0 else 0)
        (mul (Stdlib.Int.succ (Stdlib.Int.succ 0))
          (bitwise op n' (div2 a) (div2 b))))
      n0

  (** val lnot : int -> int -> int **)

  let lnot a n0 =
    Int.logxor a (BigArrayExtr.nat_ones n0)
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n0

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op (+) x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module N =
 struct
  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val pow_pos : int -> int -> int **)

  let pow_pos z0 =
    Pos.iter (mul z0) 1

  (** val pow : int -> int -> int **)

  let pow x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> pow_pos x p)
      (fun _ -> 0)
      y

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
 end

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n1 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n1 l0))
    n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec =
  (<=)

(** val le_dec : int -> int -> bool **)

let le_dec =
  le_gt_dec



(** val z_le_dec : int -> int -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let option_bind a f =
  match a with
  | Some a' -> f a'
  | None -> None

(** val byte_get_nat : BigArrayExtr.byte_buf -> int -> int option **)

let byte_get_nat bf index =
  option_bind (BigArrayExtr.get bf index) (fun b -> Some (Char.code b))

type byteIdx =
| I0
| I1
| I2
| I3
| I4
| I5
| I6
| I7

(** val byteIdx_to_nat : byteIdx -> int **)

let byteIdx_to_nat = function
| I0 -> 0
| I1 -> Stdlib.Int.succ 0
| I2 -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| I3 -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| I4 -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| I5 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| I6 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| I7 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val nat_to_ByteIdx : int -> byteIdx **)

let nat_to_ByteIdx n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> I0)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> I1)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> I2)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> I3)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> I4)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> I5)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> I6)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> I7)
                  (fun _ -> I7)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

type bytePos = { byte_pos : int; byte_off : byteIdx }

module BA =
 struct
  type coq_Buffer = BigArrayExtr.byte_buf

  (** val len : coq_Buffer -> int **)

  let len bf =
    ( * ) (BigArrayExtr.buf_len bf) (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))

  type coq_Pos = bytePos

  (** val to_nat : coq_Pos -> int **)

  let to_nat pos =
    (+)
      (( * ) pos.byte_pos (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))))))) (byteIdx_to_nat pos.byte_off)

  (** val of_nat : int -> coq_Pos **)

  let of_nat n0 =
    { byte_pos =
      ((/) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))))))); byte_off =
      (nat_to_ByteIdx
        ((mod) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))))))))) }
 end

type flg =
| SameVer
| DiffVer

(** val flg_add : flg -> flg -> flg **)

let flg_add f1 f2 =
  match f1 with
  | SameVer -> f2
  | DiffVer -> DiffVer

(** val add_opt : int option -> int option -> int option **)

let add_opt n1 n2 =
  match n1 with
  | Some n1' -> (match n2 with
                 | Some n2' -> Some ((+) n1' n2')
                 | None -> None)
  | None -> None

type 'a dec_P = 'a -> bool

(** val sumbool_and1 : bool -> bool -> bool **)

let sumbool_and1 x x0 =
  if x then x0 else false

type 'a serialize =
  BA.coq_Buffer -> BA.coq_Pos -> 'a -> ((BA.coq_Buffer * BA.coq_Pos) * __)
  option

type 'a parse =
  BA.coq_Buffer -> BA.coq_Pos -> (('a sig0 * BA.coq_Pos) * flg) option

(** val get_byte_len : int -> int **)

let get_byte_len n0 =
  (/)
    ((+) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))

type 't t_Format = { t_Serial : 't serialize; t_Parse : 't parse;
                     t_to_len : ('t -> int option) }

(** val bind_parse :
    'a1 parse -> ('a1 -> __ -> flg -> 'a2 parse) -> 'a2 parse **)

let bind_parse parA f bf pos =
  match parA bf pos with
  | Some p ->
    let (p0, flg0) = p in
    let (s, pos') = p0 in let Exist a = s in f a __ flg0 bf pos'
  | None -> None

(** val proj_parse : 'a1 parse -> ('a1 -> 'a2) -> 'a2 parse **)

let proj_parse pa f bf pos =
  match pa bf pos with
  | Some p ->
    let (p0, flg0) = p in
    let (s, pos') = p0 in let Exist a = s in Some (((Exist (f a)), pos'), flg0)
  | None -> None

(** val return_parse : 'a1 sig0 -> flg -> 'a1 parse **)

let return_parse a flg0 _ pos =
  Some ((a, pos), flg0)

(** val restrict_parse : 'a1 dec_P -> 'a1 parse -> 'a1 parse **)

let restrict_parse r_dec pa bf pos =
  match pa bf pos with
  | Some p ->
    let (p0, flg0) = p in
    let (s, pos') = p0 in
    let Exist a = s in if r_dec a then Some (((Exist a), pos'), flg0) else None
  | None -> None

(** val restrict_serialize : 'a1 dec_P -> 'a1 serialize -> 'a1 serialize **)

let restrict_serialize r_dec s bf pos a =
  if r_dec a
  then (match s bf pos a with
        | Some p -> let (p0, _) = p in Some (p0, __)
        | None -> None)
  else None

(** val proj_serialize :
    'a1 serialize -> ('a2 -> 'a1) -> 'a2 dec_P -> 'a2 serialize **)

let proj_serialize s f p2_dec bf pos b =
  if p2_dec b
  then (match s bf pos (f b) with
        | Some p -> let (p0, _) = p in Some (p0, __)
        | None -> None)
  else None

(** val sigma_serialize :
    'a1 serialize -> ('a1 -> __ -> 'a2 serialize) -> ('a1 * 'a2) serialize **)

let sigma_serialize sa sb bf pos z0 =
  match sa bf pos (fst z0) with
  | Some p ->
    let (p0, _) = p in
    let (bf', pos') = p0 in
    (match sb (fst z0) __ bf' pos' (snd z0) with
     | Some p1 -> let (p2, _) = p1 in Some (p2, __)
     | None -> None)
  | None -> None

(** val append_serialize :
    'a1 serialize -> 'a2 serialize -> ('a1 * 'a2) serialize **)

let append_serialize sa sb bf pos z0 =
  match sa bf pos (fst z0) with
  | Some p ->
    let (p0, _) = p in
    let (bf', pos') = p0 in
    (match sb bf' pos' (snd z0) with
     | Some p1 -> let (p2, _) = p1 in Some (p2, __)
     | None -> None)
  | None -> None

(** val sigma_parse :
    'a1 parse -> ('a1 -> __ -> 'a2 parse) -> ('a1 * 'a2) parse **)

let sigma_parse par1 pser2 =
  bind_parse par1 (fun a _ flg1 ->
    bind_parse (pser2 a __) (fun b _ flg2 ->
      return_parse (Exist (a, b)) (flg_add flg1 flg2)))

(** val append_parse : 'a1 parse -> 'a2 parse -> ('a1 * 'a2) parse **)

let append_parse par1 par2 =
  bind_parse par1 (fun a _ flg1 ->
    bind_parse par2 (fun b _ flg2 ->
      return_parse (Exist (a, b)) (flg_add flg1 flg2)))

(** val mask0 : int -> int -> int -> int **)

let mask0 m off n0 =
  Int.shift_left (BigArrayExtr.nat_ones n0) ((-) ((-) m off) n0)

(** val mask : int -> int -> int -> int **)

let mask m off n0 =
  Int.logor (mask0 m 0 off) (mask0 m ((+) off n0) ((-) ((-) m off) n0))

(** val put_few_bits : int -> int -> int -> int -> int -> int **)

let put_few_bits m off n0 a0 a =
  Int.logor (Int.logand (mask m off n0) a0)
    (Int.shift_left a ((-) ((-) m off) n0))

(** val get_few_bits : int -> int -> int -> int -> int **)

let get_few_bits m off n0 a =
  Int.logand (BigArrayExtr.nat_ones n0)
    (Int.shift_right a ((-) ((-) m off) n0))

(** val put_k_bytes :
    int -> int -> BigArrayExtr.byte_buf -> int -> BigArrayExtr.byte_buf option **)

let rec put_k_bytes k i bf a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    if (<=) i (BigArrayExtr.buf_len bf) then Some bf else None)
    (fun k' ->
    option_bind
      (BigArrayExtr.byte_of_nat
        (Int.shift_right
          (Int.logand a
            (mask0
              (( * ) k (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) 0
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
          (( * ) k' (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))) (fun b ->
      option_bind (BigArrayExtr.set bf i b) (fun bf' ->
        put_k_bytes k' ((+) i (Stdlib.Int.succ 0)) bf'
          (Int.logand a
            (BigArrayExtr.nat_ones
              (( * ) k' (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))
    k

(** val read_k_bytes : int -> int -> BigArrayExtr.byte_buf -> int option **)

let rec read_k_bytes k i bf =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    if (<=) i (BigArrayExtr.buf_len bf) then Some 0 else None)
    (fun k' ->
    option_bind (byte_get_nat bf i) (fun b ->
      option_bind (read_k_bytes k' ((+) i (Stdlib.Int.succ 0)) bf) (fun n0 ->
        Some
        (Int.logor
          (Int.shift_left b
            (( * ) k' (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) n0))))
    k

(** val put_n_bits : int -> int serialize **)

let put_n_bits n0 bf pos a =
  let new_pos_nat = (+) (BA.to_nat pos) n0 in
  if (<=) new_pos_nat (BA.len bf)
  then if (<) a (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) n0)
       then let new_pos = BA.of_nat new_pos_nat in
            let off = byteIdx_to_nat pos.byte_off in
            let num_bits = (+) (byteIdx_to_nat pos.byte_off) n0 in
            let num_bytes =
              (/)
                ((+) num_bits (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ 0))))))))
            in
            option_bind (read_k_bytes num_bytes pos.byte_pos bf) (fun a0 ->
              let a1 =
                put_few_bits
                  (( * ) num_bytes (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))))))))) off n0 a0 a
              in
              option_bind (put_k_bytes num_bytes pos.byte_pos bf a1)
                (fun bf' -> Some ((bf', new_pos), __)))
       else None
  else None

(** val read_n_bits : int -> int parse **)

let read_n_bits n0 bf pos =
  let new_pos_nat = (+) (BA.to_nat pos) n0 in
  if (<=) new_pos_nat (BA.len bf)
  then let new_pos = BA.of_nat new_pos_nat in
       let off = byteIdx_to_nat pos.byte_off in
       let num_bits = (+) off n0 in
       let num_bytes =
         (/)
           ((+) num_bits (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
       in
       option_bind (read_k_bytes num_bytes pos.byte_pos bf) (fun a0 -> Some
         (((Exist
         (get_few_bits
           (( * ) num_bytes (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) off n0 a0)),
         new_pos), SameVer))
  else None

(** val put_n_nat : int -> int serialize **)

let put_n_nat n0 bf pos a =
  if (<=) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))
  then put_n_bits n0 bf pos a
  else None

(** val read_n_nat : int -> int parse **)

let read_n_nat n0 bf pos =
  if (<=) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))
  then read_n_bits n0 bf pos
  else None

(** val n_nat_to_len : int -> int -> int option **)

let n_nat_to_len n0 _ =
  Some n0

(** val basic_n_bit_format : int -> int t_Format **)

let basic_n_bit_format n0 =
  { t_Serial = (put_n_nat n0); t_Parse = (read_n_nat n0); t_to_len =
    (n_nat_to_len n0) }

(** val proj_format :
    'a2 t_Format -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 dec_P -> 'a1 t_Format **)

let proj_format b_format f f_inv p1_dec =
  { t_Serial = (proj_serialize b_format.t_Serial f p1_dec); t_Parse =
    (proj_parse b_format.t_Parse f_inv); t_to_len = (fun a ->
    b_format.t_to_len (f a)) }

(** val sigma_format :
    'a1 t_Format -> ('a1 -> 'a2 t_Format) -> ('a1 * 'a2) t_Format **)

let sigma_format s fs =
  { t_Serial = (sigma_serialize s.t_Serial (fun a _ -> (fs a).t_Serial));
    t_Parse = (sigma_parse s.t_Parse (fun a _ -> (fs a).t_Parse)); t_to_len =
    (fun z0 ->
    add_opt (s.t_to_len (fst z0)) ((fs (fst z0)).t_to_len (snd z0))) }

(** val append_format :
    'a1 t_Format -> 'a2 t_Format -> ('a1 * 'a2) t_Format **)

let append_format s1 s2 =
  { t_Serial = (append_serialize s1.t_Serial s2.t_Serial); t_Parse =
    (append_parse s1.t_Parse s2.t_Parse); t_to_len = (fun z0 ->
    add_opt (s1.t_to_len (fst z0)) (s2.t_to_len (snd z0))) }

(** val restrict_format : 'a1 t_Format -> ('a1 -> bool) -> 'a1 t_Format **)

let restrict_format s r_dec =
  { t_Serial = (restrict_serialize r_dec s.t_Serial); t_Parse =
    (restrict_parse r_dec s.t_Parse); t_to_len = s.t_to_len }

(** val put_unit : unit serialize **)

let put_unit bf pos _ =
  if le_dec (BA.to_nat pos) (BA.len bf) then Some ((bf, pos), __) else None

(** val read_unit : unit parse **)

let read_unit bf pos =
  if le_dec (BA.to_nat pos) (BA.len bf)
  then Some (((Exist ()), pos), SameVer)
  else None

(** val unit_to_len : unit -> int option **)

let unit_to_len _ =
  Some 0

(** val unit_format : unit t_Format **)

let unit_format =
  { t_Serial = put_unit; t_Parse = read_unit; t_to_len = (fun _ -> Some 0) }

(** val put_fixed_item :
    'a1 -> BA.coq_Buffer -> BA.coq_Pos -> ((BA.coq_Buffer * BA.coq_Pos) * __)
    option **)

let put_fixed_item _ bf pos =
  match put_unit bf pos () with
  | Some p -> let (p0, _) = p in Some (p0, __)
  | None -> None

(** val read_fixed_item : 'a1 sig0 -> 'a1 parse **)

let read_fixed_item a bf pos =
  match read_unit bf pos with
  | Some p ->
    let (p0, _) = p in let (_, pos') = p0 in Some ((a, pos'), SameVer)
  | None -> None

(** val list_serial : 'a1 serialize -> int -> 'a1 list serialize **)

let rec list_serial ser n0 bf pos la =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match la with
    | [] -> put_fixed_item [] bf pos
    | _ :: _ -> None)
    (fun m ->
    match la with
    | [] -> None
    | h :: t ->
      (match ser bf pos h with
       | Some p ->
         let (p0, _) = p in
         let (bf', pos') = p0 in
         (match list_serial ser m bf' pos' t with
          | Some p1 -> let (p2, _) = p1 in Some (p2, __)
          | None -> None)
       | None -> None))
    n0

(** val list_parse : 'a1 parse -> int -> 'a1 list parse **)

let rec list_parse par n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> read_fixed_item (Exist []))
    (fun m ->
    bind_parse par (fun h _ flg0 ->
      bind_parse (list_parse par m) (fun t _ flg2 ->
        return_parse (Exist (h :: t)) (flg_add flg0 flg2))))
    n0

(** val list_to_len : ('a1 -> int option) -> int -> 'a1 list -> int option **)

let rec list_to_len a_to_len n0 la =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match la with
              | [] -> Some 0
              | _ :: _ -> None)
    (fun m ->
    match la with
    | [] -> None
    | h :: t -> add_opt (a_to_len h) (list_to_len a_to_len m t))
    n0

(** val list_format : 'a1 t_Format -> int -> 'a1 list t_Format **)

let list_format fmt n0 =
  { t_Serial = (list_serial fmt.t_Serial n0); t_Parse =
    (list_parse fmt.t_Parse n0); t_to_len = (list_to_len fmt.t_to_len n0) }

(** val bool_format : bool t_Format **)

let bool_format =
  { t_Serial =
    (proj_serialize (put_n_nat (Stdlib.Int.succ 0)) (fun b ->
      if b then Stdlib.Int.succ 0 else 0) (fun _ -> true)); t_Parse =
    (proj_parse (read_n_nat (Stdlib.Int.succ 0)) (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun _ -> true)
        n0)); t_to_len = (fun _ -> Some (Stdlib.Int.succ 0)) }

(** val to_bit_sz : int -> int **)

let to_bit_sz n0 =
  (+) (BigArrayExtr.log2 n0) (Stdlib.Int.succ 0)

(** val nat_format : int -> int t_Format **)

let nat_format n0 =
  restrict_format (basic_n_bit_format (to_bit_sz n0)) (fun a -> le_dec a n0)

(** val nat_enum_format : int -> int t_Format **)

let nat_enum_format n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    proj_format unit_format (fun _ -> ()) (fun _ -> 0) (fun z0 -> le_dec z0 0))
    (fun n1 -> nat_format (Stdlib.Int.succ n1))
    n0

(** val nat_range_format : int -> int -> int t_Format **)

let nat_range_format lb ub =
  proj_format (nat_format ((-) ub lb)) (fun z0 -> (-) z0 lb) (fun z0 ->
    (+) z0 lb) (fun a -> sumbool_and1 (le_dec lb a) (le_dec a ub))

(** val small_integer_format : int t_Format **)

let small_integer_format =
  restrict_format
    (basic_n_bit_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))) (fun n0 ->
    le_dec n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val sumbool_neg : bool -> bool **)

let sumbool_neg = function
| true -> false
| false -> true

(** val sumbool_or1 : bool -> bool -> bool **)

let sumbool_or1 x x0 =
  if x then true else x0

(** val choose_norm_ext_format :
    'a1 t_Format -> 'a1 t_Format -> 'a1 dec_P -> 'a1 dec_P -> (bool * 'a1)
    t_Format **)

let choose_norm_ext_format fmt_normal fmt_ext p_dec p_ext_dec =
  sigma_format bool_format (fun a ->
    if a
    then restrict_format fmt_ext (fun a0 ->
           sumbool_and1 (sumbool_neg (p_dec a0)) (p_ext_dec a0))
    else fmt_normal)

(** val normal_ext_format_dec : 'a1 dec_P -> 'a1 dec_P -> 'a1 dec_P **)

let normal_ext_format_dec p_dec p_ext_dec a =
  sumbool_or1 (p_dec a) (sumbool_and1 (sumbool_neg (p_dec a)) (p_ext_dec a))

(** val normal_ext_format :
    'a1 t_Format -> 'a1 t_Format -> 'a1 dec_P -> 'a1 dec_P -> 'a1 t_Format **)

let normal_ext_format fmt_normal fmt_ext p_dec p_ext_dec =
  proj_format (choose_norm_ext_format fmt_normal fmt_ext p_dec p_ext_dec)
    (fun z0 -> if p_dec z0 then (false, z0) else (true, z0)) snd
    (normal_ext_format_dec p_dec p_ext_dec)

(** val choose_len_det_helper3 : bool -> int -> bool **)

let choose_len_det_helper3 a a0 =
  if a
  then sumbool_and1
         (le_dec
           (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) a0)
         ((<) a0
           (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0))))))))))))))))
  else (<) a0
         (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))

(** val choose_len_det_format : bool -> int t_Format **)

let choose_len_det_format a =
  restrict_format
    (basic_n_bit_format
      (if a
       then Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))
       else Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
    (choose_len_det_helper3 a)

(** val bit_len_format : (bool * int) t_Format **)

let bit_len_format =
  sigma_format bool_format choose_len_det_format

(** val uncons_len_det_format : int t_Format **)

let uncons_len_det_format =
  proj_format bit_len_format (fun n0 ->
    if (<) n0
         (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
    then (false, n0)
    else (true, n0)) snd (fun n0 ->
    (<) n0
      (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))))))))))))))

(** val choose_norm_small_det : bool -> int t_Format **)

let choose_norm_small_det = function
| true ->
  restrict_format uncons_len_det_format (fun a ->
    sumbool_and1
      (le_dec (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) a)
      ((<) a
        (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))))))))))))))))
| false ->
  nat_range_format (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val bit_norm_small_len_format : (bool * int) t_Format **)

let bit_norm_small_len_format =
  sigma_format bool_format choose_norm_small_det

(** val normally_small_len_det_format : int t_Format **)

let normally_small_len_det_format =
  proj_format bit_norm_small_len_format (fun n0 ->
    if (&&) ((<=) (Stdlib.Int.succ 0) n0)
         ((<=) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ
           0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    then (false, n0)
    else (true, n0)) snd (fun n0 ->
    sumbool_and1 (le_dec (Stdlib.Int.succ 0) n0)
      ((<) n0
        (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))))))))))))))))

(** val small_enc : int serialize **)

let small_enc =
  normally_small_len_det_format.t_Serial

(** val small_dec : int parse **)

let small_dec =
  normally_small_len_det_format.t_Parse

(** val len_det_ranged_ext : int -> int -> int t_Format **)

let len_det_ranged_ext lb ub =
  normal_ext_format (nat_range_format lb ub) uncons_len_det_format (fun a ->
    sumbool_and1 (le_dec lb a) (le_dec a ub)) (fun a ->
    (<) a
      (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))))))))))))))

(** val z_range_dec : int -> int -> int -> bool **)

let z_range_dec lb ub a =
  sumbool_and1 (z_le_dec lb a) (z_le_dec a ub)

(** val ranged_int_format : int -> int -> int t_Format **)

let ranged_int_format lb ub =
  proj_format (nat_format (BigArrayExtr.int_id (Z.sub ub lb))) (fun z0 ->
    BigArrayExtr.int_id (Z.sub z0 lb)) (fun n0 ->
    Z.add (BigArrayExtr.int_id n0) lb) (z_range_dec lb ub)

(** val sz_to_num_octets : int -> int **)

let sz_to_num_octets sz =
  (+)
    ((/) sz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ 0)

(** val to_2_complement : int -> int -> int **)

let to_2_complement sz n0 =
  (+) (Nat.lnot n0 sz) (Stdlib.Int.succ 0)

type nat_T = int sig0

(** val compare_lt_le_dec : int -> int -> int -> bool **)

let compare_lt_le_dec lb ub x =
  sumbool_and1 (le_dec lb x) (le_dec x ub)

(** val z_to_nat_bin : int -> nat_T * int **)

let z_to_nat_bin z0 =
  if Z.ltb z0 0
  then let n0 = BigArrayExtr.int_id (Z.opp z0) in
       let sz = to_bit_sz ((-) n0 (Stdlib.Int.succ 0)) in
       let num_octets = sz_to_num_octets sz in
       if compare_lt_le_dec (Stdlib.Int.succ 0) (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) num_octets
       then ((Exist num_octets),
              (to_2_complement
                (( * ) num_octets (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))
                n0))
       else ((Exist (Stdlib.Int.succ 0)), 0)
  else let n0 = BigArrayExtr.int_id z0 in
       let sz = to_bit_sz n0 in
       let num_octets = sz_to_num_octets sz in
       if compare_lt_le_dec (Stdlib.Int.succ 0) (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) num_octets
       then ((Exist num_octets), n0)
       else ((Exist (Stdlib.Int.succ 0)), 0)

(** val nat_bin_to_z : (nat_T * int) -> int **)

let nat_bin_to_z = function
| (num_octets, n0) ->
  let sz =
    ( * ) (let Exist a = num_octets in a) (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
  in
  if (<) n0
       (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) ((-) sz (Stdlib.Int.succ 0)))
  then BigArrayExtr.int_id n0
  else Z.opp (BigArrayExtr.int_id (to_2_complement sz n0))

(** val int_len_det : int t_Format **)

let int_len_det =
  restrict_format
    (basic_n_bit_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))) (fun a ->
    compare_lt_le_dec (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))) a)

(** val int_len_det_sig : nat_T t_Format **)

let int_len_det_sig =
  proj_format int_len_det (fun z0 -> let Exist a = z0 in a) (fun x ->
    if compare_lt_le_dec (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         0)))))) x
    then Exist x
    else Exist (Stdlib.Int.succ 0)) (fun _ -> true)

(** val restrict_nat_pair_dec : int -> int -> bool **)

let restrict_nat_pair_dec sz a =
  let b = (=) sz (Stdlib.Int.succ 0) in
  if b
  then sumbool_and1 (le_dec 0 a)
         ((<) a
           (pow (Stdlib.Int.succ (Stdlib.Int.succ 0))
             (( * ) sz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))
  else sumbool_and1
         (le_dec
           (pow (Stdlib.Int.succ (Stdlib.Int.succ 0))
             ((-)
               (( * ) ((-) sz (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ 0))) a)
         ((<) a
           ((-)
             (pow (Stdlib.Int.succ (Stdlib.Int.succ 0))
               (( * ) sz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
             (pow (Stdlib.Int.succ (Stdlib.Int.succ 0))
               ((-)
                 (( * ) ((-) sz (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ 0)))))

(** val restrict_nat_pair : int -> int t_Format **)

let restrict_nat_pair sz =
  restrict_format
    (basic_n_bit_format
      (( * ) sz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))) (restrict_nat_pair_dec sz)

(** val nat_pair_format : (nat_T * int) t_Format **)

let nat_pair_format =
  sigma_format int_len_det_sig (fun z0 ->
    restrict_nat_pair (let Exist a = z0 in a))

(** val int_format : int t_Format **)

let int_format =
  proj_format nat_pair_format z_to_nat_bin nat_bin_to_z (fun z0 ->
    sumbool_and1
      (z_le_dec
        (Z.opp
          (Z.pow ((fun p->2*p) 1) ((fun p->1+2*p) ((fun p->1+2*p)
            ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))) z0)
      (z_le_dec z0
        (Z.sub
          (Z.pow ((fun p->2*p) 1) ((fun p->1+2*p) ((fun p->1+2*p)
            ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))) 1)))

(** val int_format_ranged_ext : int -> int -> int t_Format **)

let int_format_ranged_ext lb ub =
  normal_ext_format (ranged_int_format lb ub) int_format (fun a ->
    sumbool_and1 (z_le_dec lb a) (z_le_dec a ub)) (fun a ->
    sumbool_and1
      (z_le_dec
        (Z.opp
          (Z.pow ((fun p->2*p) 1) ((fun p->1+2*p) ((fun p->1+2*p)
            ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))) a)
      (z_le_dec a
        (Z.sub
          (Z.pow ((fun p->2*p) 1) ((fun p->1+2*p) ((fun p->1+2*p)
            ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))) 1)))

(** val of_nat_non_opt : int -> char **)

let of_nat_non_opt a =
  match BigArrayExtr.byte_of_nat a with
  | Some b -> b
  | None -> '\x00'

(** val byte_format : char t_Format **)

let byte_format =
  proj_format
    (basic_n_bit_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))) Char.code of_nat_non_opt (fun _ -> true)

(** val byte_list_format : int -> char list t_Format **)

let byte_list_format n0 =
  list_format byte_format n0

type octet_string = char list

(** val octet_string_no_cons_format : char list t_Format **)

let octet_string_no_cons_format =
  proj_format (sigma_format uncons_len_det_format byte_list_format) (fun bs ->
    ((length bs), bs)) snd (fun bs ->
    (<) (length bs)
      (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))))))))))))))

(** val octet_string_ranged_format : int -> int -> char list t_Format **)

let octet_string_ranged_format lb ub =
  proj_format
    (sigma_format (ranged_int_format lb ub) (fun n0 ->
      byte_list_format (BigArrayExtr.int_id n0))) (fun bs ->
    ((BigArrayExtr.int_id (length bs)), bs)) snd (fun bs ->
    sumbool_and1 (z_le_dec lb (BigArrayExtr.int_id (length bs)))
      (z_le_dec (BigArrayExtr.int_id (length bs)) ub))

(** val list_bool_format : int -> bool list t_Format **)

let list_bool_format n0 =
  restrict_format (list_format bool_format n0) (fun bl -> (=) (length bl) n0)

(** val bool_list_serialize : int -> bool list serialize **)

let bool_list_serialize n0 =
  (list_bool_format n0).t_Serial

(** val bool_list_parse : int -> bool list parse **)

let bool_list_parse n0 =
  (list_bool_format n0).t_Parse

type bit_string = int * (char list * int)

type bit_string_fixed = int * (char list * int)

(** val get_list_len : int -> int **)

let get_list_len n0 =
  (/) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))

(** val get_tail_len : int -> int **)

let get_tail_len n0 =
  (mod) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))

(** val bit_string_len_prop_dec : int -> (char list * int) -> bool **)

let bit_string_len_prop_dec n0 = function
| (l, n1) ->
  sumbool_and1 ((=) (length l) (get_list_len n0))
    ((<) n1 (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (get_tail_len n0)))

(** val bit_string_format : int -> (char list * int) t_Format **)

let bit_string_format n0 =
  restrict_format
    (append_format (byte_list_format (get_list_len n0))
      (basic_n_bit_format (get_tail_len n0))) (bit_string_len_prop_dec n0)

(** val ranged_nat_format : int -> int -> int t_Format **)

let ranged_nat_format lb ub =
  proj_format (ranged_int_format lb ub) BigArrayExtr.int_id
    BigArrayExtr.int_id (fun n0 ->
    sumbool_and1 (z_le_dec lb (BigArrayExtr.int_id n0))
      (z_le_dec (BigArrayExtr.int_id n0) ub))

(** val bit_string_ranged_format :
    int -> int -> (int * (char list * int)) t_Format **)

let bit_string_ranged_format lb ub =
  sigma_format (ranged_nat_format lb ub) bit_string_format

(** val fixed_nat_format : int -> int t_Format **)

let fixed_nat_format n0 =
  proj_format unit_format (fun _ -> ()) (fun _ -> n0) (fun z0 -> (=) z0 n0)

(** val bit_string_fixed_format : int -> (int * (char list * int)) t_Format **)

let bit_string_fixed_format n0 =
  sigma_format (fixed_nat_format (BigArrayExtr.int_id n0)) bit_string_format

(** val bool_enc : bool serialize **)

let bool_enc =
  bool_format.t_Serial

(** val opt_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let opt_bind a_opt f =
  match a_opt with
  | Some a' -> f a'
  | None -> None

(** val fail_parse : 'a1 parse **)

let fail_parse _ _ =
  None

(** val opt_serialize : 'a1 serialize -> 'a1 option serialize **)

let opt_serialize ser bf pos = function
| Some a' -> ser bf pos a'
| None -> put_unit bf pos ()

(** val opt_parse : 'a1 parse -> bool -> 'a1 option parse **)

let opt_parse par = function
| true -> bind_parse par (fun a _ flg0 -> return_parse (Exist (Some a)) flg0)
| false -> return_parse (Exist None) SameVer

(** val put_fixed_item0 :
    'a1 -> BA.coq_Buffer -> BA.coq_Pos -> ((BA.coq_Buffer * BA.coq_Pos) * __)
    option **)

let put_fixed_item0 _ bf pos =
  match put_unit bf pos () with
  | Some p -> let (p0, _) = p in Some (p0, __)
  | None -> None

(** val dft_serialize :
    'a1 serialize -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 serialize **)

let dft_serialize ser eqb_dec dft bf pos a =
  if eqb_dec dft a then put_fixed_item0 dft bf pos else ser bf pos a

(** val dft_parse :
    'a1 parse -> 'a1 -> ('a1 -> 'a1 -> bool) -> bool -> 'a1 parse **)

let dft_parse par dft eqb_dec = function
| true ->
  bind_parse par (fun a _ flg0 ->
    if eqb_dec dft a then fail_parse else return_parse (Exist a) flg0)
| false -> return_parse (Exist dft) SameVer

(** val append_parse0 : 'a1 parse -> 'a2 parse -> ('a1 * 'a2) parse **)

let append_parse0 parse1 parse2 =
  bind_parse parse1 (fun a _ flg1 ->
    bind_parse parse2 (fun b _ flg2 ->
      return_parse (Exist (a, b)) (flg_add flg1 flg2)))

(** val prepend_serialize :
    ('a2 -> 'a1) -> 'a1 serialize -> 'a2 serialize -> 'a2 serialize **)

let prepend_serialize f serA serB bf pos b =
  match append_serialize serA serB bf pos ((f b), b) with
  | Some p -> let (p0, _) = p in Some (p0, __)
  | None -> None

(** val prepend_serialize_fixed :
    'a1 -> 'a1 serialize -> 'a2 serialize -> 'a2 serialize **)

let prepend_serialize_fixed v serA serB bf pos b =
  match append_serialize serA serB bf pos (v, b) with
  | Some p -> let (p0, _) = p in Some (p0, __)
  | None -> None

(** val length2 : 'a1 list -> int **)

let rec length2 = function
| [] -> 0
| _ :: t -> Stdlib.Int.succ (length2 t)

(** val proj2_serialize :
    'a2 serialize -> ('a2 -> 'a1) -> ('a1 -> 'a2) -> 'a1 serialize **)

let proj2_serialize s _ f bf pos a =
  match s bf pos (f a) with
  | Some p -> let (p0, _) = p in Some (p0, __)
  | None -> None

(** val proj2_format :
    'a2 t_Format -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 t_Format **)

let proj2_format b_format f f_inv =
  { t_Serial = (proj2_serialize b_format.t_Serial f_inv f); t_Parse =
    (proj_parse b_format.t_Parse f_inv); t_to_len = (fun a ->
    b_format.t_to_len (f a)) }

(** val seq_of_format : 'a1 t_Format -> int -> int -> 'a1 list t_Format **)

let seq_of_format fmt lb ub =
  proj2_format
    (sigma_format (ranged_nat_format lb ub) (fun n0 -> list_format fmt n0))
    (fun bs -> ((length bs), bs)) snd

(** val length_value_format :
    'a1 t_Format -> int t_Format -> 'a1 list t_Format **)

let length_value_format fmt len_fmt =
  proj2_format (sigma_format len_fmt (fun n0 -> list_format fmt n0))
    (fun bs -> ((length bs), bs)) snd

(** val seq_of_fixed_format : 'a1 t_Format -> int -> 'a1 list t_Format **)

let seq_of_fixed_format fmt n0 =
  list_format fmt (BigArrayExtr.int_id n0)

(** val seq_of_ext_format : 'a1 t_Format -> int -> int -> 'a1 list t_Format **)

let seq_of_ext_format fmt lb ub =
  length_value_format fmt (len_det_ranged_ext lb ub)

(** val num_to_ascii : int -> char **)

let num_to_ascii n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ' ')
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> '0')
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> '1')
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> '2')
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> '3')
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> '4')
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> '5')
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> '6')
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> '7')
                    (fun n9 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> '8')
                      (fun n10 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> '9')
                        (fun _ -> ' ')
                        n10)
                      n9)
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val ascii_to_num : char -> int **)

let ascii_to_num a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then if b1
              then if b2
                   then 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))))))
                             else 0
                        else 0
              else if b2
                   then 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))
                             else 0
                        else 0
         else if b1
              then if b2
                   then 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))))
                             else 0
                        else 0
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))))))))
                             else 0
                        else 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ 0)
                             else 0
                        else 0
    else if b0
         then if b1
              then if b2
                   then 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                             else 0
                        else 0
              else if b2
                   then 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))
                             else 0
                        else 0
         else if b1
              then if b2
                   then 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))
                             else 0
                        else 0
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6
                                       then 0
                                       else Stdlib.Int.succ (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))))
                             else 0
                        else 0
                   else if b3
                        then if b4
                             then if b5
                                  then 0
                                  else if b6 then 0 else Stdlib.Int.succ 0
                             else 0
                        else 0)
    a

(** val numeric_string_dec : char dec_P **)

let numeric_string_dec a =
  sumbool_or1 ((=) a ' ')
    (sumbool_or1 ((=) a '0')
      (sumbool_or1 ((=) a '1')
        (sumbool_or1 ((=) a '2')
          (sumbool_or1 ((=) a '3')
            (sumbool_or1 ((=) a '4')
              (sumbool_or1 ((=) a '5')
                (sumbool_or1 ((=) a '6')
                  (sumbool_or1 ((=) a '7')
                    (sumbool_or1 ((=) a '8') ((=) a '9'))))))))))

(** val numeric_string__Format : char t_Format **)

let numeric_string__Format =
  proj_format
    (nat_range_format 0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))
    ascii_to_num num_to_ascii numeric_string_dec

(** val ia5_string__Format : char t_Format **)

let ia5_string__Format =
  proj_format
    (nat_range_format 0
      ((-)
        (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (Stdlib.Int.succ 0)))
    Char.code Char.chr (fun a ->
    (<) (Char.code a)
      (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

(** val utf8_string__Format : string t_Format **)

let utf8_string__Format =
  proj_format octet_string_no_cons_format
    (fun s -> List.init (String.length s) (fun i -> s.[i]))
    (fun l ->
      let a = Array.of_list l in
      String.init (Array.length a) (fun i -> a.(i)))
    (fun s ->
    (<) (String.length s)
      (pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))))))))))))))

type ('x, 'f) list_to_prod = __

type typ =
| Typ_cons

type typ_set = __

type ('x, 'f) list_to_prod_set = __

type get_formats = (typ, typ_set t_Format) list_to_prod

type get_serial_prod = (typ, typ_set serialize) list_to_prod

type get_parse_prod = (typ, typ_set parse) list_to_prod

type get_to_len_prod = (typ, typ_set -> int option) list_to_prod

(** val fmt_to_prod :
    typ list -> get_formats -> (__ -> __ -> __ t_Format -> 'a1) -> 'a1 ->
    (typ, 'a1) list_to_prod **)

let rec fmt_to_prod l fmts t_X x_unit =
  match l with
  | [] -> Obj.magic x_unit
  | _ :: l0 ->
    let (t, l1) = Obj.magic fmts in
    Obj.magic ((t_X __ __ t), (fmt_to_prod l0 l1 t_X x_unit))

(** val fmt_to_prod_no_cond :
    typ list -> get_formats -> (__ -> __ -> __ t_Format -> 'a1) -> 'a1 ->
    (typ, 'a1) list_to_prod **)

let rec fmt_to_prod_no_cond l fmts t_X x_unit =
  match l with
  | [] -> Obj.magic x_unit
  | _ :: l0 ->
    let (t, l1) = Obj.magic fmts in
    Obj.magic ((t_X __ __ t), (fmt_to_prod_no_cond l0 l1 t_X x_unit))

type choice = (int, typ_set) sigT

(** val put_empty : empty_set serialize **)

let put_empty _ _ _ =
  assert false (* absurd case *)

(** val read_empty : empty_set parse **)

let read_empty _ _ =
  None

(** val empty_to_len : empty_set -> int option **)

let empty_to_len _ =
  assert false (* absurd case *)

(** val empty_format : empty_set t_Format **)

let empty_format =
  { t_Serial = put_empty; t_Parse = read_empty; t_to_len = empty_to_len }

(** val get_remaining_bits : int -> int **)

let get_remaining_bits n0 =
  (-)
    (( * ) (get_byte_len n0) (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) n0

(** val det_enc : int serialize **)

let det_enc =
  uncons_len_det_format.t_Serial

(** val det_dec : int parse **)

let det_dec =
  uncons_len_det_format.t_Parse

(** val open_typ_serialize :
    'a1 serialize -> ('a1 -> int option) -> 'a1 serialize **)

let open_typ_serialize ser get_len_ser bf pos a =
  opt_bind (get_len_ser a) (fun n0 ->
    match det_enc bf pos (get_byte_len n0) with
    | Some p ->
      let (p0, _) = p in
      let (bf', pos') = p0 in
      (match ser bf' pos' a with
       | Some p1 ->
         let (p2, _) = p1 in
         let (bf'', pos'') = p2 in
         let n' = (-) (BA.to_nat pos'') (BA.to_nat pos') in
         if (=) n0 n'
         then let remaining_len = get_remaining_bits n0 in
              (match put_n_nat remaining_len bf'' pos'' 0 with
               | Some p3 -> let (p4, _) = p3 in Some (p4, __)
               | None -> None)
         else None
       | None -> None)
    | None -> None)

(** val skip_some_bits : int -> int parse **)

let skip_some_bits n0 =
  if le_dec n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))
  then read_n_nat n0
  else fail_parse

(** val open_typ_parse : 'a1 parse -> 'a1 parse **)

let open_typ_parse par bf pos =
  match det_dec bf pos with
  | Some p ->
    let (p0, _) = p in
    let (s, pos1) = p0 in
    let Exist n0 = s in
    (match par bf pos1 with
     | Some p1 ->
       let (p2, flg0) = p1 in
       let (s0, pos2) = p2 in
       let pos1_nat = BA.to_nat pos1 in
       let pos2_nat = BA.to_nat pos2 in
       let bits_read = (-) pos2_nat pos1_nat in
       if (=) (get_byte_len bits_read) n0
       then bind_parse
              (skip_some_bits
                ((-)
                  (( * ) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) bits_read))
              (fun zs _ _ ->
              if (=) zs 0 then return_parse s0 flg0 else fail_parse) bf pos2
       else None
     | None -> None)
  | None -> None

(** val skip_1_byte : unit parse **)

let skip_1_byte =
  bind_parse
    (read_n_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))) (fun _ _ _ -> read_unit)

(** val skip_n_bytes : int -> unit parse **)

let rec skip_n_bytes n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> read_unit)
    (fun m -> bind_parse (skip_n_bytes m) (fun _ _ _ -> skip_1_byte))
    n0

(** val open_type_skip_parse : unit parse **)

let open_type_skip_parse =
  bind_parse det_dec (fun n0 _ _ ->
    bind_parse (skip_n_bytes n0) (fun _ _ _ -> read_unit))

(** val open_type_to_len : ('a1 -> int option) -> 'a1 -> int option **)

let open_type_to_len tl a =
  opt_bind (tl a) (fun n0 ->
    let nb = get_byte_len n0 in
    opt_bind (uncons_len_det_format.t_to_len nb) (fun n' -> Some
      ((+) n'
        (( * ) nb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0))))))))))))

type seq_elem =
| Nor
| Opt
| Dft of __ * (__ -> __ -> bool)

type seq_elem_to_type = __

type seq_type = (seq_elem, seq_elem_to_type) list_to_prod_set

(** val bit_list_len : seq_elem list -> int **)

let bit_list_len l =
  fold_right (fun h ->
    match h with
    | Nor -> Obj.magic id
    | _ -> (fun x -> Stdlib.Int.succ x)) 0 l

(** val seq_type_to_bit_list : seq_elem list -> seq_type -> bool list **)

let rec seq_type_to_bit_list l x =
  match l with
  | [] -> []
  | y :: l0 ->
    let (s, l1) = Obj.magic x in
    (match y with
     | Nor -> seq_type_to_bit_list l0 l1
     | Opt ->
       (match s with
        | Some _ -> true
        | None -> false) :: (seq_type_to_bit_list l0 l1)
     | Dft (default, eqb_dec) ->
       (if Obj.magic eqb_dec default s then false else true) :: (seq_type_to_bit_list
                                                                  l0 l1))

type seq_elem_to_set = __

type seq_elem_to_serial = seq_elem_to_set serialize

type seq_elem_to_parse = seq_elem_to_set parse

type seq_elem_to_format = seq_elem_to_set t_Format

type seq_format_prod = (seq_elem, seq_elem_to_format) list_to_prod

type seq_serial_prod = (seq_elem, seq_elem_to_serial) list_to_prod

type seq_to_len_prod = (seq_elem, seq_elem_to_set -> int option) list_to_prod

(** val seq_serialize_latter :
    seq_elem list -> seq_serial_prod -> seq_type serialize **)

let rec seq_serialize_latter l ser =
  match l with
  | [] -> Obj.magic put_unit
  | y :: l0 ->
    (match y with
     | Nor ->
       Obj.magic append_serialize (fst (Obj.magic ser))
         (seq_serialize_latter l0 (snd (Obj.magic ser)))
     | Opt ->
       Obj.magic append_serialize (opt_serialize (fst (Obj.magic ser)))
         (seq_serialize_latter l0 (snd (Obj.magic ser)))
     | Dft (default, eqb_dec) ->
       Obj.magic append_serialize
         (dft_serialize (fst (Obj.magic ser)) eqb_dec default)
         (seq_serialize_latter l0 (snd (Obj.magic ser))))

(** val seq_serialize :
    seq_elem list -> seq_serial_prod -> seq_type serialize **)

let seq_serialize l ser =
  prepend_serialize (seq_type_to_bit_list l)
    (bool_list_serialize (bit_list_len l)) (seq_serialize_latter l ser)

type seq_parse_prod = (seq_elem, seq_elem_to_parse) list_to_prod

(** val seq_parse_latter :
    seq_elem list -> seq_parse_prod -> bool list -> seq_type parse **)

let rec seq_parse_latter l par bl =
  match l with
  | [] -> Obj.magic read_unit
  | y :: l0 ->
    (match y with
     | Nor ->
       Obj.magic append_parse0 (fst (Obj.magic par))
         (seq_parse_latter l0 (snd (Obj.magic par)) bl)
     | Opt ->
       (match bl with
        | [] -> fail_parse
        | b :: l1 ->
          Obj.magic append_parse0 (opt_parse (fst (Obj.magic par)) b)
            (seq_parse_latter l0 (snd (Obj.magic par)) l1))
     | Dft (default, eqb_dec) ->
       (match bl with
        | [] -> fail_parse
        | b :: l1 ->
          Obj.magic append_parse0
            (dft_parse (fst (Obj.magic par)) default eqb_dec b)
            (seq_parse_latter l0 (snd (Obj.magic par)) l1)))

(** val seq_parse : seq_elem list -> seq_parse_prod -> seq_type parse **)

let seq_parse l par =
  bind_parse (bool_list_parse (bit_list_len l)) (fun bl _ _ ->
    seq_parse_latter l par bl)

(** val seq_to_len_latter :
    seq_elem list -> seq_to_len_prod -> seq_type -> int option **)

let rec seq_to_len_latter l tl c =
  match l with
  | [] -> Some 0
  | y :: l0 ->
    (match y with
     | Nor ->
       add_opt (fst (Obj.magic tl) (fst (Obj.magic c)))
         (seq_to_len_latter l0 (snd (Obj.magic tl)) (snd (Obj.magic c)))
     | Opt ->
       let (s, l1) = Obj.magic c in
       add_opt (match s with
                | Some a -> fst (Obj.magic tl) a
                | None -> Some 0)
         (seq_to_len_latter l0 (snd (Obj.magic tl)) l1)
     | Dft (default, eqb_dec) ->
       let (s, l1) = Obj.magic c in
       add_opt (if eqb_dec default s then Some 0 else fst (Obj.magic tl) s)
         (seq_to_len_latter l0 (snd (Obj.magic tl)) l1))

(** val seq_to_len :
    seq_elem list -> seq_to_len_prod -> seq_type -> int option **)

let seq_to_len l tl c =
  add_opt (Some (bit_list_len l)) (seq_to_len_latter l tl c)

type ext_elem_to_type = typ_set option

type ('x, 'f, 'default) list_to_prod_dft = __

type seq_ext_type = (typ, ext_elem_to_type, unit) list_to_prod_dft

(** val ext_serialize_latter :
    typ list -> get_serial_prod -> get_to_len_prod -> seq_ext_type serialize **)

let rec ext_serialize_latter l ser len_prod =
  match l with
  | [] -> Obj.magic put_unit
  | _ :: l0 ->
    Obj.magic append_serialize
      (opt_serialize
        (open_typ_serialize (fst (Obj.magic ser)) (fst (Obj.magic len_prod))))
      (ext_serialize_latter l0 (snd (Obj.magic ser))
        (snd (Obj.magic len_prod)))

(** val check_all_none_bool : typ list -> seq_ext_type -> bool **)

let rec check_all_none_bool l s =
  match l with
  | [] -> true
  | _ :: l0 ->
    let (e, l1) = Obj.magic s in
    (match e with
     | Some _ -> false
     | None -> check_all_none_bool l0 l1)

(** val check_all_none_dec : typ list -> seq_ext_type dec_P **)

let check_all_none_dec ext a =
  let b = check_all_none_bool ext a in if b then true else false

(** val opt_bool : 'a1 option -> bool **)

let opt_bool = function
| Some _ -> true
| None -> false

(** val ext_to_bit_list : typ list -> seq_ext_type -> bool list **)

let rec ext_to_bit_list l s =
  match l with
  | [] -> []
  | _ :: l0 ->
    (opt_bool (fst (Obj.magic s))) :: (ext_to_bit_list l0 (snd (Obj.magic s)))

(** val ext_serialize :
    typ list -> get_serial_prod -> get_to_len_prod -> seq_ext_type serialize **)

let ext_serialize ext ser len_prod =
  prepend_serialize (fun _ -> length2 ext) small_enc
    (prepend_serialize (fun z0 -> ext_to_bit_list ext z0)
      (bool_list_serialize (length2 ext))
      (ext_serialize_latter ext ser len_prod))

(** val to_parse_latter_eq :
    typ list -> get_parse_prod -> bool list -> seq_ext_type parse **)

let rec to_parse_latter_eq l par bl =
  match l with
  | [] -> Obj.magic read_unit
  | _ :: l0 ->
    (match bl with
     | [] -> fail_parse
     | b :: l1 ->
       Obj.magic append_parse0
         (opt_parse (open_typ_parse (fst (Obj.magic par))) b)
         (to_parse_latter_eq l0 (snd (Obj.magic par)) l1))

(** val ext_all_none : typ list -> seq_ext_type **)

let rec ext_all_none = function
| [] -> Obj.magic ()
| _ :: l0 -> Obj.magic (None, (ext_all_none l0))

(** val to_parse_none : typ list -> seq_ext_type parse **)

let to_parse_none ext' =
  bind_parse read_unit (fun _ _ _ ->
    return_parse (Exist (ext_all_none ext')) DiffVer)

(** val to_parse_latter_le :
    typ list -> get_parse_prod -> bool list -> seq_ext_type parse **)

let rec to_parse_latter_le l par bl =
  match l with
  | [] -> Obj.magic read_unit
  | y :: l0 ->
    (match bl with
     | [] -> to_parse_none (y :: l0)
     | b :: l1 ->
       Obj.magic append_parse0
         (opt_parse (open_typ_parse (fst (Obj.magic par))) b)
         (to_parse_latter_le l0 (snd (Obj.magic par)) l1))

(** val to_parse_skip : int -> bool list -> unit parse **)

let rec to_parse_skip n0 bl =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> read_unit)
    (fun m ->
    match bl with
    | [] -> fail_parse
    | h :: tbl ->
      if h
      then bind_parse open_type_skip_parse (fun _ _ _ -> to_parse_skip m tbl)
      else to_parse_skip m tbl)
    n0

(** val to_parse_latter_ge :
    typ list -> get_parse_prod -> bool list -> seq_ext_type parse **)

let to_parse_latter_ge ext par bl =
  let n0 = length2 ext in
  let l0 = firstn n0 bl in
  bind_parse (to_parse_latter_eq ext par l0) (fun e _ _ ->
    bind_parse (to_parse_skip ((-) (length bl) n0) (skipn n0 bl))
      (fun _ _ _ -> return_parse (Exist e) DiffVer))

type three_split =
| Left3
| Middle3
| Right3

(** val lt_le_eq_dec : int -> int -> bool **)

let lt_le_eq_dec n0 m =
  if (<=) m n0 then false else true

(** val lt_eq_lt_dec_new : int -> int -> three_split **)

let lt_eq_lt_dec_new n0 m =
  if (<=) n0 m then if lt_le_eq_dec n0 m then Left3 else Middle3 else Right3

(** val ext_parse : typ list -> get_parse_prod -> seq_ext_type parse **)

let ext_parse ext par =
  bind_parse small_dec (fun n0 _ _ ->
    bind_parse (bool_list_parse n0) (fun bl _ _ ->
      match lt_eq_lt_dec_new (length bl) (length2 ext) with
      | Left3 -> to_parse_latter_le ext par bl
      | Middle3 -> to_parse_latter_eq ext par bl
      | Right3 -> to_parse_latter_ge ext par bl))

(** val seq_ext_to_len_latter :
    typ list -> get_to_len_prod -> seq_ext_type -> int option **)

let rec seq_ext_to_len_latter l tl s =
  match l with
  | [] -> Some 0
  | _ :: l0 ->
    let (e, l1) = Obj.magic s in
    let (o, l2) = Obj.magic tl in
    add_opt (match e with
             | Some t -> open_type_to_len o t
             | None -> Some 0) (seq_ext_to_len_latter l0 l2 l1)

(** val seq_ext_to_len :
    typ list -> get_to_len_prod -> seq_ext_type -> int option **)

let seq_ext_to_len ext tl s =
  let len_e = length2 ext in
  add_opt (normally_small_len_det_format.t_to_len len_e)
    (add_opt (Some len_e) (seq_ext_to_len_latter ext tl s))

(** val seq_ext_serialize :
    seq_elem list -> seq_serial_prod -> typ list -> get_serial_prod ->
    get_to_len_prod -> (seq_type * seq_ext_type) serialize **)

let seq_ext_serialize l ser ext ser_ext len_prod bf pos z0 =
  let seq_enc = seq_serialize l ser in
  if check_all_none_dec ext (snd z0)
  then (match bool_enc bf pos false with
        | Some p ->
          let (p0, _) = p in
          let (bf', pos') = p0 in
          (match seq_enc bf' pos' (fst z0) with
           | Some p1 -> let (p2, _) = p1 in Some (p2, __)
           | None -> None)
        | None -> None)
  else (match bool_enc bf pos true with
        | Some p ->
          let (p0, _) = p in
          let (bf', pos') = p0 in
          (match seq_enc bf' pos' (fst z0) with
           | Some p1 ->
             let (p2, _) = p1 in
             let (bf'', pos'') = p2 in
             (match ext_serialize ext ser_ext len_prod bf'' pos'' (snd z0) with
              | Some p3 -> let (p4, _) = p3 in Some (p4, __)
              | None -> None)
           | None -> None)
        | None -> None)

(** val seq_ext_parse :
    seq_elem list -> seq_parse_prod -> typ list -> get_parse_prod ->
    (seq_type * seq_ext_type) parse **)

let seq_ext_parse l par ext par_ext =
  let seq_dec = seq_parse l par in
  bind_parse bool_format.t_Parse (fun b _ _ ->
    if b
    then bind_parse seq_dec (fun sa _ flg1 ->
           bind_parse (ext_parse ext par_ext) (fun se _ flg2 ->
             if check_all_none_dec ext se
             then fail_parse
             else return_parse (Exist (sa, se)) (flg_add flg1 flg2)))
    else bind_parse seq_dec (fun sa _ flg1 ->
           return_parse (Exist (sa, (ext_all_none ext))) flg1))

(** val seq_ext_to_len0 :
    seq_elem list -> seq_to_len_prod -> typ list -> get_to_len_prod ->
    (seq_type * seq_ext_type) -> int option **)

let seq_ext_to_len0 l tl ext tl_ext z0 =
  add_opt (Some (Stdlib.Int.succ 0))
    (add_opt (seq_to_len l tl (fst z0)) (seq_ext_to_len ext tl_ext (snd z0)))

(** val fmt_to_seq_prod :
    seq_elem list -> seq_format_prod -> (__ -> __ -> __ t_Format -> 'a1) ->
    'a1 -> (seq_elem, 'a1) list_to_prod **)

let rec fmt_to_seq_prod l fmts t_X x_unit =
  match l with
  | [] -> Obj.magic x_unit
  | _ :: l0 ->
    let (s, l1) = Obj.magic fmts in
    Obj.magic ((t_X __ __ s), (fmt_to_seq_prod l0 l1 t_X x_unit))

(** val fmt_to_seq_prod_no_cond :
    seq_elem list -> seq_format_prod -> (__ -> __ -> __ t_Format -> 'a1) ->
    'a1 -> (seq_elem, 'a1) list_to_prod **)

let rec fmt_to_seq_prod_no_cond l fmts t_X x_unit =
  match l with
  | [] -> Obj.magic x_unit
  | _ :: l0 ->
    let (s, l1) = Obj.magic fmts in
    Obj.magic ((t_X __ __ s), (fmt_to_seq_prod_no_cond l0 l1 t_X x_unit))

(** val seq_format : seq_elem list -> seq_format_prod -> seq_type t_Format **)

let seq_format l fmts =
  { t_Serial =
    (seq_serialize l
      (fmt_to_seq_prod l fmts (Obj.magic (fun _ _ t -> t.t_Serial)) put_unit));
    t_Parse =
    (seq_parse l
      (fmt_to_seq_prod l fmts (Obj.magic (fun _ _ t -> t.t_Parse)) read_unit));
    t_to_len =
    (seq_to_len l
      (fmt_to_seq_prod_no_cond l fmts (fun _ _ t -> t.t_to_len) (fun _ -> Some
        0))) }

(** val seq_ext_format :
    seq_elem list -> seq_format_prod -> typ list -> get_formats ->
    (seq_type * seq_ext_type) t_Format **)

let seq_ext_format l fmt ext fmt_ext =
  { t_Serial =
    (seq_ext_serialize l
      (fmt_to_seq_prod l fmt (Obj.magic (fun _ _ t -> t.t_Serial)) put_unit)
      ext
      (fmt_to_prod ext fmt_ext (Obj.magic (fun _ _ t -> t.t_Serial)) put_unit)
      (fmt_to_prod_no_cond ext fmt_ext (Obj.magic (fun _ _ t -> t.t_to_len))
        unit_to_len)); t_Parse =
    (seq_ext_parse l
      (fmt_to_seq_prod l fmt (Obj.magic (fun _ _ t -> t.t_Parse)) read_unit)
      ext
      (fmt_to_prod ext fmt_ext (Obj.magic (fun _ _ t -> t.t_Parse)) read_unit));
    t_to_len =
    (seq_ext_to_len0 l
      (fmt_to_seq_prod_no_cond l fmt (Obj.magic (fun _ _ t -> t.t_to_len))
        unit_to_len) ext
      (fmt_to_prod_no_cond ext fmt_ext (Obj.magic (fun _ _ t -> t.t_to_len))
        unit_to_len)) }

(** val proj3_format :
    'a2 t_Format -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 t_Format **)

let proj3_format s f f_inv =
  proj_format s f f_inv (fun _ -> true)

(** val unit__Format : unit t_Format **)

let unit__Format =
  unit_format

(** val bool__Format : bool t_Format **)

let bool__Format =
  bool_format

(** val sum_serial :
    'a1 serialize -> 'a2 serialize -> ('a1, 'a2) sum serialize **)

let sum_serial sa sb bf pos = function
| Inl a -> prepend_serialize_fixed false bool_format.t_Serial sa bf pos a
| Inr b -> prepend_serialize_fixed true bool_format.t_Serial sb bf pos b

(** val sum_parse : 'a1 parse -> 'a2 parse -> ('a1, 'a2) sum parse **)

let sum_parse sa sb =
  bind_parse bool_format.t_Parse (fun b0 _ _ ->
    if b0
    then bind_parse sb (fun b _ flg0 -> return_parse (Exist (Inr b)) flg0)
    else bind_parse sa (fun a _ flg0 -> return_parse (Exist (Inl a)) flg0))

(** val sum_to_len :
    ('a1 -> int option) -> ('a2 -> int option) -> ('a1, 'a2) sum -> int option **)

let sum_to_len sa sb z0 =
  add_opt (Some (Stdlib.Int.succ 0))
    (match z0 with
     | Inl a -> sa a
     | Inr b -> sb b)

(** val sum_format :
    'a1 t_Format -> 'a2 t_Format -> ('a1, 'a2) sum t_Format **)

let sum_format sa sb =
  { t_Serial = (sum_serial sa.t_Serial sb.t_Serial); t_Parse =
    (sum_parse sa.t_Parse sb.t_Parse); t_to_len =
    (sum_to_len sa.t_to_len sb.t_to_len) }

type stationID__Type = int

(** val stationID__Format : int t_Format **)

let stationID__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    1)))))))))))))))))))))))))))))))

type itsPduHeader__Type = { itsPduHeader__protocolVersion : int;
                            itsPduHeader__messageID : int;
                            itsPduHeader__stationID : stationID__Type }

(** val itsPduHeader__list : seq_elem list **)

let itsPduHeader__list =
  Nor :: (Nor :: (Nor :: []))

(** val itsPduHeader__protocolVersion__Format : int t_Format **)

let itsPduHeader__protocolVersion__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

(** val itsPduHeader__messageID__Format : int t_Format **)

let itsPduHeader__messageID__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type itsPduHeader__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val itsPduHeader__Format_list : itsPduHeader__Format_Type **)

let itsPduHeader__Format_list =
  ((Obj.magic itsPduHeader__protocolVersion__Format),
    ((Obj.magic itsPduHeader__messageID__Format),
    ((Obj.magic stationID__Format), (Obj.magic unit_format))))

(** val itsPduHeader__list__Format : seq_type t_Format **)

let itsPduHeader__list__Format =
  seq_format itsPduHeader__list (Obj.magic itsPduHeader__Format_list)

(** val itsPduHeader__F1 :
    itsPduHeader__Type -> int * (int * (stationID__Type * unit)) **)

let itsPduHeader__F1 z0 =
  (z0.itsPduHeader__protocolVersion, (z0.itsPduHeader__messageID,
    (z0.itsPduHeader__stationID, ())))

(** val itsPduHeader__F2 : seq_type -> itsPduHeader__Type **)

let itsPduHeader__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { itsPduHeader__protocolVersion = i0; itsPduHeader__messageID = i1;
  itsPduHeader__stationID = i2 }

(** val itsPduHeader__Format : itsPduHeader__Type t_Format **)

let itsPduHeader__Format =
  proj2_format itsPduHeader__list__Format (Obj.magic itsPduHeader__F1)
    itsPduHeader__F2

type generationDeltaTime__Type = int

(** val generationDeltaTime__Format : int t_Format **)

let generationDeltaTime__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    1)))))))))))))))

type stationType__Type = int

(** val stationType__Format : int t_Format **)

let stationType__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type latitude__Type = int

(** val latitude__Format : int t_Format **)

let latitude__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    1)))))))))))))))))))))))))))))) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    1)))))))))))))))))))))))))))))

type longitude__Type = int

(** val longitude__Format : int t_Format **)

let longitude__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    1))))))))))))))))))))))))))))))) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1))))))))))))))))))))))))))))))

type semiAxisLength__Type = int

(** val semiAxisLength__Format : int t_Format **)

let semiAxisLength__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    1)))))))))))

type headingValue__Type = int

(** val headingValue__Format : int t_Format **)

let headingValue__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))

type posConfidenceEllipse__Type = { posConfidenceEllipse__semiMajorConfidence : 
                                    semiAxisLength__Type;
                                    posConfidenceEllipse__semiMinorConfidence : 
                                    semiAxisLength__Type;
                                    posConfidenceEllipse__semiMajorOrientation : 
                                    headingValue__Type }

(** val posConfidenceEllipse__list : seq_elem list **)

let posConfidenceEllipse__list =
  Nor :: (Nor :: (Nor :: []))

type posConfidenceEllipse__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val posConfidenceEllipse__Format_list :
    posConfidenceEllipse__Format_Type **)

let posConfidenceEllipse__Format_list =
  ((Obj.magic semiAxisLength__Format), ((Obj.magic semiAxisLength__Format),
    ((Obj.magic headingValue__Format), (Obj.magic unit_format))))

(** val posConfidenceEllipse__list__Format : seq_type t_Format **)

let posConfidenceEllipse__list__Format =
  seq_format posConfidenceEllipse__list
    (Obj.magic posConfidenceEllipse__Format_list)

(** val posConfidenceEllipse__F1 :
    posConfidenceEllipse__Type ->
    semiAxisLength__Type * (semiAxisLength__Type * (headingValue__Type * unit)) **)

let posConfidenceEllipse__F1 z0 =
  (z0.posConfidenceEllipse__semiMajorConfidence,
    (z0.posConfidenceEllipse__semiMinorConfidence,
    (z0.posConfidenceEllipse__semiMajorOrientation, ())))

(** val posConfidenceEllipse__F2 : seq_type -> posConfidenceEllipse__Type **)

let posConfidenceEllipse__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { posConfidenceEllipse__semiMajorConfidence = i0;
  posConfidenceEllipse__semiMinorConfidence = i1;
  posConfidenceEllipse__semiMajorOrientation = i2 }

(** val posConfidenceEllipse__Format : posConfidenceEllipse__Type t_Format **)

let posConfidenceEllipse__Format =
  proj2_format posConfidenceEllipse__list__Format
    (Obj.magic posConfidenceEllipse__F1) posConfidenceEllipse__F2

type altitudeValue__Type = int

(** val altitudeValue__Format : int t_Format **)

let altitudeValue__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))))))))))))
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    1)))))))))))))))))))

type altitudeConfidence__Type =
| AltitudeConfidence__alt_000_01
| AltitudeConfidence__alt_000_02
| AltitudeConfidence__alt_000_05
| AltitudeConfidence__alt_000_10
| AltitudeConfidence__alt_000_20
| AltitudeConfidence__alt_000_50
| AltitudeConfidence__alt_001_00
| AltitudeConfidence__alt_002_00
| AltitudeConfidence__alt_005_00
| AltitudeConfidence__alt_010_00
| AltitudeConfidence__alt_020_00
| AltitudeConfidence__alt_050_00
| AltitudeConfidence__alt_100_00
| AltitudeConfidence__alt_200_00
| AltitudeConfidence__outOfRange
| AltitudeConfidence__unavailable

(** val altitudeConfidence__nat__Format : int t_Format **)

let altitudeConfidence__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))

(** val altitudeConfidence__F1 : altitudeConfidence__Type -> int **)

let altitudeConfidence__F1 = function
| AltitudeConfidence__alt_000_01 -> 0
| AltitudeConfidence__alt_000_02 -> Stdlib.Int.succ 0
| AltitudeConfidence__alt_000_05 -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| AltitudeConfidence__alt_000_10 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| AltitudeConfidence__alt_000_20 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| AltitudeConfidence__alt_000_50 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| AltitudeConfidence__alt_001_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| AltitudeConfidence__alt_002_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
| AltitudeConfidence__alt_005_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))
| AltitudeConfidence__alt_010_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))
| AltitudeConfidence__alt_020_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))
| AltitudeConfidence__alt_050_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
| AltitudeConfidence__alt_100_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))
| AltitudeConfidence__alt_200_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))
| AltitudeConfidence__outOfRange ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))
| AltitudeConfidence__unavailable ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))

(** val altitudeConfidence__F2 : int -> altitudeConfidence__Type **)

let altitudeConfidence__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> AltitudeConfidence__alt_000_01)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> AltitudeConfidence__alt_000_02)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> AltitudeConfidence__alt_000_05)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> AltitudeConfidence__alt_000_10)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> AltitudeConfidence__alt_000_20)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> AltitudeConfidence__alt_000_50)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> AltitudeConfidence__alt_001_00)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> AltitudeConfidence__alt_002_00)
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> AltitudeConfidence__alt_005_00)
                    (fun n9 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> AltitudeConfidence__alt_010_00)
                      (fun n10 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> AltitudeConfidence__alt_020_00)
                        (fun n11 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> AltitudeConfidence__alt_050_00)
                          (fun n12 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ ->
                            AltitudeConfidence__alt_100_00)
                            (fun n13 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ ->
                              AltitudeConfidence__alt_200_00)
                              (fun n14 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ ->
                                AltitudeConfidence__outOfRange)
                                (fun n15 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ ->
                                  AltitudeConfidence__unavailable)
                                  (fun _ -> AltitudeConfidence__alt_000_01)
                                  n15)
                                n14)
                              n13)
                            n12)
                          n11)
                        n10)
                      n9)
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val altitudeConfidence__Format : altitudeConfidence__Type t_Format **)

let altitudeConfidence__Format =
  proj3_format altitudeConfidence__nat__Format altitudeConfidence__F1
    altitudeConfidence__F2

type altitude__Type = { altitude__altitudeValue : altitudeValue__Type;
                        altitude__altitudeConfidence : altitudeConfidence__Type }

(** val altitude__list : seq_elem list **)

let altitude__list =
  Nor :: (Nor :: [])

type altitude__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val altitude__Format_list : altitude__Format_Type **)

let altitude__Format_list =
  ((Obj.magic altitudeValue__Format), ((Obj.magic altitudeConfidence__Format),
    (Obj.magic unit_format)))

(** val altitude__list__Format : seq_type t_Format **)

let altitude__list__Format =
  seq_format altitude__list (Obj.magic altitude__Format_list)

(** val altitude__F1 :
    altitude__Type -> altitudeValue__Type * (altitudeConfidence__Type * unit) **)

let altitude__F1 z0 =
  (z0.altitude__altitudeValue, (z0.altitude__altitudeConfidence, ()))

(** val altitude__F2 : seq_type -> altitude__Type **)

let altitude__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { altitude__altitudeValue = i0; altitude__altitudeConfidence = i1 }

(** val altitude__Format : altitude__Type t_Format **)

let altitude__Format =
  proj2_format altitude__list__Format (Obj.magic altitude__F1) altitude__F2

type referencePosition__Type = { referencePosition__latitude : latitude__Type;
                                 referencePosition__longitude : longitude__Type;
                                 referencePosition__positionConfidenceEllipse : 
                                 posConfidenceEllipse__Type;
                                 referencePosition__altitude : altitude__Type }

(** val referencePosition__list : seq_elem list **)

let referencePosition__list =
  Nor :: (Nor :: (Nor :: (Nor :: [])))

type referencePosition__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

(** val referencePosition__Format_list : referencePosition__Format_Type **)

let referencePosition__Format_list =
  ((Obj.magic latitude__Format), ((Obj.magic longitude__Format),
    ((Obj.magic posConfidenceEllipse__Format), ((Obj.magic altitude__Format),
    (Obj.magic unit_format)))))

(** val referencePosition__list__Format : seq_type t_Format **)

let referencePosition__list__Format =
  seq_format referencePosition__list (Obj.magic referencePosition__Format_list)

(** val referencePosition__F1 :
    referencePosition__Type ->
    latitude__Type * (longitude__Type * (posConfidenceEllipse__Type * (altitude__Type * unit))) **)

let referencePosition__F1 z0 =
  (z0.referencePosition__latitude, (z0.referencePosition__longitude,
    (z0.referencePosition__positionConfidenceEllipse,
    (z0.referencePosition__altitude, ()))))

(** val referencePosition__F2 : seq_type -> referencePosition__Type **)

let referencePosition__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, _) = p0 in
  { referencePosition__latitude = i0; referencePosition__longitude = i1;
  referencePosition__positionConfidenceEllipse = i2;
  referencePosition__altitude = i3 }

(** val referencePosition__Format : referencePosition__Type t_Format **)

let referencePosition__Format =
  proj2_format referencePosition__list__Format
    (Obj.magic referencePosition__F1) referencePosition__F2

type basicContainer__Type = { basicContainer__stationType : stationType__Type;
                              basicContainer__referencePosition : referencePosition__Type }

(** val basicContainer__root_list : seq_elem list **)

let basicContainer__root_list =
  Nor :: (Nor :: [])

(** val basicContainer__ext_list : typ list **)

let basicContainer__ext_list =
  []

type basicContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val basicContainer__root_Format_list : basicContainer__root_Format_Type **)

let basicContainer__root_Format_list =
  ((Obj.magic stationType__Format), ((Obj.magic referencePosition__Format),
    (Obj.magic unit_format)))

type basicContainer__ext_Format_Type = unit t_Format

(** val basicContainer__ext_Format_list : basicContainer__ext_Format_Type **)

let basicContainer__ext_Format_list =
  unit__Format

type basicContainer__list_type = seq_type * seq_ext_type

(** val basicContainer__list_format : basicContainer__list_type t_Format **)

let basicContainer__list_format =
  seq_ext_format basicContainer__root_list
    (Obj.magic basicContainer__root_Format_list) basicContainer__ext_list
    (Obj.magic basicContainer__ext_Format_list)

(** val basicContainer__F1 :
    basicContainer__Type -> basicContainer__list_type **)

let basicContainer__F1 z0 =
  ((Obj.magic (z0.basicContainer__stationType,
     (z0.basicContainer__referencePosition, ()))), (Obj.magic ()))

(** val basicContainer__F2 :
    basicContainer__list_type -> basicContainer__Type **)

let basicContainer__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, _) = l in
  { basicContainer__stationType = j0; basicContainer__referencePosition = j1 }

(** val basicContainer__Format : basicContainer__Type t_Format **)

let basicContainer__Format =
  proj2_format basicContainer__list_format basicContainer__F1
    basicContainer__F2

type headingConfidence__Type = int

(** val headingConfidence__Format : int t_Format **)

let headingConfidence__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

type heading__Type = { heading__headingValue : headingValue__Type;
                       heading__headingConfidence : headingConfidence__Type }

(** val heading__list : seq_elem list **)

let heading__list =
  Nor :: (Nor :: [])

type heading__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val heading__Format_list : heading__Format_Type **)

let heading__Format_list =
  ((Obj.magic headingValue__Format), ((Obj.magic headingConfidence__Format),
    (Obj.magic unit_format)))

(** val heading__list__Format : seq_type t_Format **)

let heading__list__Format =
  seq_format heading__list (Obj.magic heading__Format_list)

(** val heading__F1 :
    heading__Type -> headingValue__Type * (headingConfidence__Type * unit) **)

let heading__F1 z0 =
  (z0.heading__headingValue, (z0.heading__headingConfidence, ()))

(** val heading__F2 : seq_type -> heading__Type **)

let heading__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { heading__headingValue = i0; heading__headingConfidence = i1 }

(** val heading__Format : heading__Type t_Format **)

let heading__Format =
  proj2_format heading__list__Format (Obj.magic heading__F1) heading__F2

type speedValue__Type = int

(** val speedValue__Format : int t_Format **)

let speedValue__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))

type speedConfidence__Type = int

(** val speedConfidence__Format : int t_Format **)

let speedConfidence__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

type speed__Type = { speed__speedValue : speedValue__Type;
                     speed__speedConfidence : speedConfidence__Type }

(** val speed__list : seq_elem list **)

let speed__list =
  Nor :: (Nor :: [])

type speed__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val speed__Format_list : speed__Format_Type **)

let speed__Format_list =
  ((Obj.magic speedValue__Format), ((Obj.magic speedConfidence__Format),
    (Obj.magic unit_format)))

(** val speed__list__Format : seq_type t_Format **)

let speed__list__Format =
  seq_format speed__list (Obj.magic speed__Format_list)

(** val speed__F1 :
    speed__Type -> speedValue__Type * (speedConfidence__Type * unit) **)

let speed__F1 z0 =
  (z0.speed__speedValue, (z0.speed__speedConfidence, ()))

(** val speed__F2 : seq_type -> speed__Type **)

let speed__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in { speed__speedValue = i0; speed__speedConfidence = i1 }

(** val speed__Format : speed__Type t_Format **)

let speed__Format =
  proj2_format speed__list__Format (Obj.magic speed__F1) speed__F2

type driveDirection__Type =
| DriveDirection__forward
| DriveDirection__backward
| DriveDirection__unavailable

(** val driveDirection__nat__Format : int t_Format **)

let driveDirection__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val driveDirection__F1 : driveDirection__Type -> int **)

let driveDirection__F1 = function
| DriveDirection__forward -> 0
| DriveDirection__backward -> Stdlib.Int.succ 0
| DriveDirection__unavailable -> Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val driveDirection__F2 : int -> driveDirection__Type **)

let driveDirection__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> DriveDirection__forward)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> DriveDirection__backward)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> DriveDirection__unavailable)
        (fun _ -> DriveDirection__forward)
        n2)
      n1)
    n0

(** val driveDirection__Format : driveDirection__Type t_Format **)

let driveDirection__Format =
  proj3_format driveDirection__nat__Format driveDirection__F1
    driveDirection__F2

type vehicleLengthValue__Type = int

(** val vehicleLengthValue__Format : int t_Format **)

let vehicleLengthValue__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))

type vehicleLengthConfidenceIndication__Type =
| VehicleLengthConfidenceIndication__noTrailerPresent
| VehicleLengthConfidenceIndication__trailerPresentWithKnownLength
| VehicleLengthConfidenceIndication__trailerPresentWithUnknownLength
| VehicleLengthConfidenceIndication__trailerPresenceIsUnknown
| VehicleLengthConfidenceIndication__unavailable

(** val vehicleLengthConfidenceIndication__nat__Format : int t_Format **)

let vehicleLengthConfidenceIndication__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))

(** val vehicleLengthConfidenceIndication__F1 :
    vehicleLengthConfidenceIndication__Type -> int **)

let vehicleLengthConfidenceIndication__F1 = function
| VehicleLengthConfidenceIndication__noTrailerPresent -> 0
| VehicleLengthConfidenceIndication__trailerPresentWithKnownLength ->
  Stdlib.Int.succ 0
| VehicleLengthConfidenceIndication__trailerPresentWithUnknownLength ->
  Stdlib.Int.succ (Stdlib.Int.succ 0)
| VehicleLengthConfidenceIndication__trailerPresenceIsUnknown ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| VehicleLengthConfidenceIndication__unavailable ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val vehicleLengthConfidenceIndication__F2 :
    int -> vehicleLengthConfidenceIndication__Type **)

let vehicleLengthConfidenceIndication__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> VehicleLengthConfidenceIndication__noTrailerPresent)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      VehicleLengthConfidenceIndication__trailerPresentWithKnownLength)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        VehicleLengthConfidenceIndication__trailerPresentWithUnknownLength)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          VehicleLengthConfidenceIndication__trailerPresenceIsUnknown)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> VehicleLengthConfidenceIndication__unavailable)
            (fun _ -> VehicleLengthConfidenceIndication__noTrailerPresent)
            n4)
          n3)
        n2)
      n1)
    n0

(** val vehicleLengthConfidenceIndication__Format :
    vehicleLengthConfidenceIndication__Type t_Format **)

let vehicleLengthConfidenceIndication__Format =
  proj3_format vehicleLengthConfidenceIndication__nat__Format
    vehicleLengthConfidenceIndication__F1 vehicleLengthConfidenceIndication__F2

type vehicleLength__Type = { vehicleLength__vehicleLengthValue : vehicleLengthValue__Type;
                             vehicleLength__vehicleLengthConfidenceIndication : 
                             vehicleLengthConfidenceIndication__Type }

(** val vehicleLength__list : seq_elem list **)

let vehicleLength__list =
  Nor :: (Nor :: [])

type vehicleLength__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val vehicleLength__Format_list : vehicleLength__Format_Type **)

let vehicleLength__Format_list =
  ((Obj.magic vehicleLengthValue__Format),
    ((Obj.magic vehicleLengthConfidenceIndication__Format),
    (Obj.magic unit_format)))

(** val vehicleLength__list__Format : seq_type t_Format **)

let vehicleLength__list__Format =
  seq_format vehicleLength__list (Obj.magic vehicleLength__Format_list)

(** val vehicleLength__F1 :
    vehicleLength__Type ->
    vehicleLengthValue__Type * (vehicleLengthConfidenceIndication__Type * unit) **)

let vehicleLength__F1 z0 =
  (z0.vehicleLength__vehicleLengthValue,
    (z0.vehicleLength__vehicleLengthConfidenceIndication, ()))

(** val vehicleLength__F2 : seq_type -> vehicleLength__Type **)

let vehicleLength__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { vehicleLength__vehicleLengthValue = i0;
  vehicleLength__vehicleLengthConfidenceIndication = i1 }

(** val vehicleLength__Format : vehicleLength__Type t_Format **)

let vehicleLength__Format =
  proj2_format vehicleLength__list__Format (Obj.magic vehicleLength__F1)
    vehicleLength__F2

type vehicleWidth__Type = int

(** val vehicleWidth__Format : int t_Format **)

let vehicleWidth__Format =
  ranged_int_format 1 ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))

type longitudinalAccelerationValue__Type = int

(** val longitudinalAccelerationValue__Format : int t_Format **)

let longitudinalAccelerationValue__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))))
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))))

type accelerationConfidence__Type = int

(** val accelerationConfidence__Format : int t_Format **)

let accelerationConfidence__Format =
  ranged_int_format 0 ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))

type longitudinalAcceleration__Type = { longitudinalAcceleration__longitudinalAccelerationValue : 
                                        longitudinalAccelerationValue__Type;
                                        longitudinalAcceleration__longitudinalAccelerationConfidence : 
                                        accelerationConfidence__Type }

(** val longitudinalAcceleration__list : seq_elem list **)

let longitudinalAcceleration__list =
  Nor :: (Nor :: [])

type longitudinalAcceleration__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val longitudinalAcceleration__Format_list :
    longitudinalAcceleration__Format_Type **)

let longitudinalAcceleration__Format_list =
  ((Obj.magic longitudinalAccelerationValue__Format),
    ((Obj.magic accelerationConfidence__Format), (Obj.magic unit_format)))

(** val longitudinalAcceleration__list__Format : seq_type t_Format **)

let longitudinalAcceleration__list__Format =
  seq_format longitudinalAcceleration__list
    (Obj.magic longitudinalAcceleration__Format_list)

(** val longitudinalAcceleration__F1 :
    longitudinalAcceleration__Type ->
    longitudinalAccelerationValue__Type * (accelerationConfidence__Type * unit) **)

let longitudinalAcceleration__F1 z0 =
  (z0.longitudinalAcceleration__longitudinalAccelerationValue,
    (z0.longitudinalAcceleration__longitudinalAccelerationConfidence, ()))

(** val longitudinalAcceleration__F2 :
    seq_type -> longitudinalAcceleration__Type **)

let longitudinalAcceleration__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { longitudinalAcceleration__longitudinalAccelerationValue = i0;
  longitudinalAcceleration__longitudinalAccelerationConfidence = i1 }

(** val longitudinalAcceleration__Format :
    longitudinalAcceleration__Type t_Format **)

let longitudinalAcceleration__Format =
  proj2_format longitudinalAcceleration__list__Format
    (Obj.magic longitudinalAcceleration__F1) longitudinalAcceleration__F2

type curvatureValue__Type = int

(** val curvatureValue__Format : int t_Format **)

let curvatureValue__Format =
  ranged_int_format ((~-) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))

type curvatureConfidence__Type =
| CurvatureConfidence__onePerMeter_0_00002
| CurvatureConfidence__onePerMeter_0_0001
| CurvatureConfidence__onePerMeter_0_0005
| CurvatureConfidence__onePerMeter_0_002
| CurvatureConfidence__onePerMeter_0_01
| CurvatureConfidence__onePerMeter_0_1
| CurvatureConfidence__outOfRange
| CurvatureConfidence__unavailable

(** val curvatureConfidence__nat__Format : int t_Format **)

let curvatureConfidence__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val curvatureConfidence__F1 : curvatureConfidence__Type -> int **)

let curvatureConfidence__F1 = function
| CurvatureConfidence__onePerMeter_0_00002 -> 0
| CurvatureConfidence__onePerMeter_0_0001 -> Stdlib.Int.succ 0
| CurvatureConfidence__onePerMeter_0_0005 ->
  Stdlib.Int.succ (Stdlib.Int.succ 0)
| CurvatureConfidence__onePerMeter_0_002 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| CurvatureConfidence__onePerMeter_0_01 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| CurvatureConfidence__onePerMeter_0_1 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| CurvatureConfidence__outOfRange ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| CurvatureConfidence__unavailable ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val curvatureConfidence__F2 : int -> curvatureConfidence__Type **)

let curvatureConfidence__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> CurvatureConfidence__onePerMeter_0_00002)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> CurvatureConfidence__onePerMeter_0_0001)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> CurvatureConfidence__onePerMeter_0_0005)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> CurvatureConfidence__onePerMeter_0_002)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> CurvatureConfidence__onePerMeter_0_01)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> CurvatureConfidence__onePerMeter_0_1)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> CurvatureConfidence__outOfRange)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> CurvatureConfidence__unavailable)
                  (fun _ -> CurvatureConfidence__onePerMeter_0_00002)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val curvatureConfidence__Format : curvatureConfidence__Type t_Format **)

let curvatureConfidence__Format =
  proj3_format curvatureConfidence__nat__Format curvatureConfidence__F1
    curvatureConfidence__F2

type curvature__Type = { curvature__curvatureValue : curvatureValue__Type;
                         curvature__curvatureConfidence : curvatureConfidence__Type }

(** val curvature__list : seq_elem list **)

let curvature__list =
  Nor :: (Nor :: [])

type curvature__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val curvature__Format_list : curvature__Format_Type **)

let curvature__Format_list =
  ((Obj.magic curvatureValue__Format),
    ((Obj.magic curvatureConfidence__Format), (Obj.magic unit_format)))

(** val curvature__list__Format : seq_type t_Format **)

let curvature__list__Format =
  seq_format curvature__list (Obj.magic curvature__Format_list)

(** val curvature__F1 :
    curvature__Type ->
    curvatureValue__Type * (curvatureConfidence__Type * unit) **)

let curvature__F1 z0 =
  (z0.curvature__curvatureValue, (z0.curvature__curvatureConfidence, ()))

(** val curvature__F2 : seq_type -> curvature__Type **)

let curvature__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { curvature__curvatureValue = i0; curvature__curvatureConfidence = i1 }

(** val curvature__Format : curvature__Type t_Format **)

let curvature__Format =
  proj2_format curvature__list__Format (Obj.magic curvature__F1) curvature__F2

type curvatureCalculationMode__root__Type =
| CurvatureCalculationMode__root__yawRateUsed
| CurvatureCalculationMode__root__yawRateNotUsed
| CurvatureCalculationMode__root__unavailable

(** val curvatureCalculationMode__root__nat__Format : int t_Format **)

let curvatureCalculationMode__root__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val curvatureCalculationMode__root__F1 :
    curvatureCalculationMode__root__Type -> int **)

let curvatureCalculationMode__root__F1 = function
| CurvatureCalculationMode__root__yawRateUsed -> 0
| CurvatureCalculationMode__root__yawRateNotUsed -> Stdlib.Int.succ 0
| CurvatureCalculationMode__root__unavailable ->
  Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val curvatureCalculationMode__root__F2 :
    int -> curvatureCalculationMode__root__Type **)

let curvatureCalculationMode__root__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> CurvatureCalculationMode__root__yawRateUsed)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> CurvatureCalculationMode__root__yawRateNotUsed)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> CurvatureCalculationMode__root__unavailable)
        (fun _ -> CurvatureCalculationMode__root__yawRateUsed)
        n2)
      n1)
    n0

type curvatureCalculationMode__ext__Type = empty_set

type curvatureCalculationMode__Type =
  (curvatureCalculationMode__root__Type, curvatureCalculationMode__ext__Type)
  sum

(** val curvatureCalculationMode__root__Format :
    curvatureCalculationMode__root__Type t_Format **)

let curvatureCalculationMode__root__Format =
  proj3_format curvatureCalculationMode__root__nat__Format
    curvatureCalculationMode__root__F1 curvatureCalculationMode__root__F2

(** val curvatureCalculationMode__ext__Format :
    curvatureCalculationMode__ext__Type t_Format **)

let curvatureCalculationMode__ext__Format =
  empty_format

(** val curvatureCalculationMode__Format :
    curvatureCalculationMode__Type t_Format **)

let curvatureCalculationMode__Format =
  sum_format curvatureCalculationMode__root__Format
    curvatureCalculationMode__ext__Format

type yawRateValue__Type = int

(** val yawRateValue__Format : int t_Format **)

let yawRateValue__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1))))))))))))))

type yawRateConfidence__Type =
| YawRateConfidence__degSec_000_01
| YawRateConfidence__degSec_000_05
| YawRateConfidence__degSec_000_10
| YawRateConfidence__degSec_001_00
| YawRateConfidence__degSec_005_00
| YawRateConfidence__degSec_010_00
| YawRateConfidence__degSec_100_00
| YawRateConfidence__outOfRange
| YawRateConfidence__unavailable

(** val yawRateConfidence__nat__Format : int t_Format **)

let yawRateConfidence__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))

(** val yawRateConfidence__F1 : yawRateConfidence__Type -> int **)

let yawRateConfidence__F1 = function
| YawRateConfidence__degSec_000_01 -> 0
| YawRateConfidence__degSec_000_05 -> Stdlib.Int.succ 0
| YawRateConfidence__degSec_000_10 -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| YawRateConfidence__degSec_001_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| YawRateConfidence__degSec_005_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| YawRateConfidence__degSec_010_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| YawRateConfidence__degSec_100_00 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| YawRateConfidence__outOfRange ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
| YawRateConfidence__unavailable ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val yawRateConfidence__F2 : int -> yawRateConfidence__Type **)

let yawRateConfidence__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> YawRateConfidence__degSec_000_01)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> YawRateConfidence__degSec_000_05)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> YawRateConfidence__degSec_000_10)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> YawRateConfidence__degSec_001_00)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> YawRateConfidence__degSec_005_00)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> YawRateConfidence__degSec_010_00)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> YawRateConfidence__degSec_100_00)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> YawRateConfidence__outOfRange)
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> YawRateConfidence__unavailable)
                    (fun _ -> YawRateConfidence__degSec_000_01)
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val yawRateConfidence__Format : yawRateConfidence__Type t_Format **)

let yawRateConfidence__Format =
  proj3_format yawRateConfidence__nat__Format yawRateConfidence__F1
    yawRateConfidence__F2

type yawRate__Type = { yawRate__yawRateValue : yawRateValue__Type;
                       yawRate__yawRateConfidence : yawRateConfidence__Type }

(** val yawRate__list : seq_elem list **)

let yawRate__list =
  Nor :: (Nor :: [])

type yawRate__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val yawRate__Format_list : yawRate__Format_Type **)

let yawRate__Format_list =
  ((Obj.magic yawRateValue__Format), ((Obj.magic yawRateConfidence__Format),
    (Obj.magic unit_format)))

(** val yawRate__list__Format : seq_type t_Format **)

let yawRate__list__Format =
  seq_format yawRate__list (Obj.magic yawRate__Format_list)

(** val yawRate__F1 :
    yawRate__Type -> yawRateValue__Type * (yawRateConfidence__Type * unit) **)

let yawRate__F1 z0 =
  (z0.yawRate__yawRateValue, (z0.yawRate__yawRateConfidence, ()))

(** val yawRate__F2 : seq_type -> yawRate__Type **)

let yawRate__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { yawRate__yawRateValue = i0; yawRate__yawRateConfidence = i1 }

(** val yawRate__Format : yawRate__Type t_Format **)

let yawRate__Format =
  proj2_format yawRate__list__Format (Obj.magic yawRate__F1) yawRate__F2

type accelerationControl__Type = bit_string_fixed

(** val accelerationControl__Format : accelerationControl__Type t_Format **)

let accelerationControl__Format =
  bit_string_fixed_format ((fun p->1+2*p) ((fun p->1+2*p) 1))

type lanePosition__Type = int

(** val lanePosition__Format : int t_Format **)

let lanePosition__Format =
  ranged_int_format ((~-) 1) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))

type steeringWheelAngleValue__Type = int

(** val steeringWheelAngleValue__Format : int t_Format **)

let steeringWheelAngleValue__Format =
  ranged_int_format ((~-) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1))))))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1)))))))))

type steeringWheelAngleConfidence__Type = int

(** val steeringWheelAngleConfidence__Format : int t_Format **)

let steeringWheelAngleConfidence__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

type steeringWheelAngle__Type = { steeringWheelAngle__steeringWheelAngleValue : 
                                  steeringWheelAngleValue__Type;
                                  steeringWheelAngle__steeringWheelAngleConfidence : 
                                  steeringWheelAngleConfidence__Type }

(** val steeringWheelAngle__list : seq_elem list **)

let steeringWheelAngle__list =
  Nor :: (Nor :: [])

type steeringWheelAngle__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val steeringWheelAngle__Format_list : steeringWheelAngle__Format_Type **)

let steeringWheelAngle__Format_list =
  ((Obj.magic steeringWheelAngleValue__Format),
    ((Obj.magic steeringWheelAngleConfidence__Format),
    (Obj.magic unit_format)))

(** val steeringWheelAngle__list__Format : seq_type t_Format **)

let steeringWheelAngle__list__Format =
  seq_format steeringWheelAngle__list
    (Obj.magic steeringWheelAngle__Format_list)

(** val steeringWheelAngle__F1 :
    steeringWheelAngle__Type ->
    steeringWheelAngleValue__Type * (steeringWheelAngleConfidence__Type * unit) **)

let steeringWheelAngle__F1 z0 =
  (z0.steeringWheelAngle__steeringWheelAngleValue,
    (z0.steeringWheelAngle__steeringWheelAngleConfidence, ()))

(** val steeringWheelAngle__F2 : seq_type -> steeringWheelAngle__Type **)

let steeringWheelAngle__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { steeringWheelAngle__steeringWheelAngleValue = i0;
  steeringWheelAngle__steeringWheelAngleConfidence = i1 }

(** val steeringWheelAngle__Format : steeringWheelAngle__Type t_Format **)

let steeringWheelAngle__Format =
  proj2_format steeringWheelAngle__list__Format
    (Obj.magic steeringWheelAngle__F1) steeringWheelAngle__F2

type lateralAccelerationValue__Type = int

(** val lateralAccelerationValue__Format : int t_Format **)

let lateralAccelerationValue__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))))
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))))

type lateralAcceleration__Type = { lateralAcceleration__lateralAccelerationValue : 
                                   lateralAccelerationValue__Type;
                                   lateralAcceleration__lateralAccelerationConfidence : 
                                   accelerationConfidence__Type }

(** val lateralAcceleration__list : seq_elem list **)

let lateralAcceleration__list =
  Nor :: (Nor :: [])

type lateralAcceleration__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val lateralAcceleration__Format_list : lateralAcceleration__Format_Type **)

let lateralAcceleration__Format_list =
  ((Obj.magic lateralAccelerationValue__Format),
    ((Obj.magic accelerationConfidence__Format), (Obj.magic unit_format)))

(** val lateralAcceleration__list__Format : seq_type t_Format **)

let lateralAcceleration__list__Format =
  seq_format lateralAcceleration__list
    (Obj.magic lateralAcceleration__Format_list)

(** val lateralAcceleration__F1 :
    lateralAcceleration__Type ->
    lateralAccelerationValue__Type * (accelerationConfidence__Type * unit) **)

let lateralAcceleration__F1 z0 =
  (z0.lateralAcceleration__lateralAccelerationValue,
    (z0.lateralAcceleration__lateralAccelerationConfidence, ()))

(** val lateralAcceleration__F2 : seq_type -> lateralAcceleration__Type **)

let lateralAcceleration__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { lateralAcceleration__lateralAccelerationValue = i0;
  lateralAcceleration__lateralAccelerationConfidence = i1 }

(** val lateralAcceleration__Format : lateralAcceleration__Type t_Format **)

let lateralAcceleration__Format =
  proj2_format lateralAcceleration__list__Format
    (Obj.magic lateralAcceleration__F1) lateralAcceleration__F2

type verticalAccelerationValue__Type = int

(** val verticalAccelerationValue__Format : int t_Format **)

let verticalAccelerationValue__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))))
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))))

type verticalAcceleration__Type = { verticalAcceleration__verticalAccelerationValue : 
                                    verticalAccelerationValue__Type;
                                    verticalAcceleration__verticalAccelerationConfidence : 
                                    accelerationConfidence__Type }

(** val verticalAcceleration__list : seq_elem list **)

let verticalAcceleration__list =
  Nor :: (Nor :: [])

type verticalAcceleration__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val verticalAcceleration__Format_list :
    verticalAcceleration__Format_Type **)

let verticalAcceleration__Format_list =
  ((Obj.magic verticalAccelerationValue__Format),
    ((Obj.magic accelerationConfidence__Format), (Obj.magic unit_format)))

(** val verticalAcceleration__list__Format : seq_type t_Format **)

let verticalAcceleration__list__Format =
  seq_format verticalAcceleration__list
    (Obj.magic verticalAcceleration__Format_list)

(** val verticalAcceleration__F1 :
    verticalAcceleration__Type ->
    verticalAccelerationValue__Type * (accelerationConfidence__Type * unit) **)

let verticalAcceleration__F1 z0 =
  (z0.verticalAcceleration__verticalAccelerationValue,
    (z0.verticalAcceleration__verticalAccelerationConfidence, ()))

(** val verticalAcceleration__F2 : seq_type -> verticalAcceleration__Type **)

let verticalAcceleration__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { verticalAcceleration__verticalAccelerationValue = i0;
  verticalAcceleration__verticalAccelerationConfidence = i1 }

(** val verticalAcceleration__Format : verticalAcceleration__Type t_Format **)

let verticalAcceleration__Format =
  proj2_format verticalAcceleration__list__Format
    (Obj.magic verticalAcceleration__F1) verticalAcceleration__F2

type performanceClass__Type = int

(** val performanceClass__Format : int t_Format **)

let performanceClass__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) 1))

type protectedZoneID__Type = int

(** val protectedZoneID__Format : int t_Format **)

let protectedZoneID__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))))))))))))))))))))))

type cenDsrcTollingZoneID__Type = protectedZoneID__Type

(** val cenDsrcTollingZoneID__Format : int t_Format **)

let cenDsrcTollingZoneID__Format =
  protectedZoneID__Format

type cenDsrcTollingZone__Type = { cenDsrcTollingZone__protectedZoneLatitude : 
                                  latitude__Type;
                                  cenDsrcTollingZone__protectedZoneLongitude : 
                                  longitude__Type;
                                  cenDsrcTollingZone__cenDsrcTollingZoneID : 
                                  cenDsrcTollingZoneID__Type option }

(** val cenDsrcTollingZone__root_list : seq_elem list **)

let cenDsrcTollingZone__root_list =
  Nor :: (Nor :: (Opt :: []))

(** val cenDsrcTollingZone__ext_list : typ list **)

let cenDsrcTollingZone__ext_list =
  []

type cenDsrcTollingZone__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val cenDsrcTollingZone__root_Format_list :
    cenDsrcTollingZone__root_Format_Type **)

let cenDsrcTollingZone__root_Format_list =
  ((Obj.magic latitude__Format), ((Obj.magic longitude__Format),
    ((Obj.magic cenDsrcTollingZoneID__Format), (Obj.magic unit_format))))

type cenDsrcTollingZone__ext_Format_Type = unit t_Format

(** val cenDsrcTollingZone__ext_Format_list :
    cenDsrcTollingZone__ext_Format_Type **)

let cenDsrcTollingZone__ext_Format_list =
  unit__Format

type cenDsrcTollingZone__list_type = seq_type * seq_ext_type

(** val cenDsrcTollingZone__list_format :
    cenDsrcTollingZone__list_type t_Format **)

let cenDsrcTollingZone__list_format =
  seq_ext_format cenDsrcTollingZone__root_list
    (Obj.magic cenDsrcTollingZone__root_Format_list)
    cenDsrcTollingZone__ext_list
    (Obj.magic cenDsrcTollingZone__ext_Format_list)

(** val cenDsrcTollingZone__F1 :
    cenDsrcTollingZone__Type -> cenDsrcTollingZone__list_type **)

let cenDsrcTollingZone__F1 z0 =
  ((Obj.magic (z0.cenDsrcTollingZone__protectedZoneLatitude,
     (z0.cenDsrcTollingZone__protectedZoneLongitude,
     (z0.cenDsrcTollingZone__cenDsrcTollingZoneID, ())))), (Obj.magic ()))

(** val cenDsrcTollingZone__F2 :
    cenDsrcTollingZone__list_type -> cenDsrcTollingZone__Type **)

let cenDsrcTollingZone__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, _) = p in
  { cenDsrcTollingZone__protectedZoneLatitude = j0;
  cenDsrcTollingZone__protectedZoneLongitude = j1;
  cenDsrcTollingZone__cenDsrcTollingZoneID = j2 }

(** val cenDsrcTollingZone__Format : cenDsrcTollingZone__Type t_Format **)

let cenDsrcTollingZone__Format =
  proj2_format cenDsrcTollingZone__list_format cenDsrcTollingZone__F1
    cenDsrcTollingZone__F2

type basicVehicleContainerHighFrequency__Type = { basicVehicleContainerHighFrequency__heading : 
                                                  heading__Type;
                                                  basicVehicleContainerHighFrequency__speed : 
                                                  speed__Type;
                                                  basicVehicleContainerHighFrequency__driveDirection : 
                                                  driveDirection__Type;
                                                  basicVehicleContainerHighFrequency__vehicleLength : 
                                                  vehicleLength__Type;
                                                  basicVehicleContainerHighFrequency__vehicleWidth : 
                                                  vehicleWidth__Type;
                                                  basicVehicleContainerHighFrequency__longitudinalAcceleration : 
                                                  longitudinalAcceleration__Type;
                                                  basicVehicleContainerHighFrequency__curvature : 
                                                  curvature__Type;
                                                  basicVehicleContainerHighFrequency__curvatureCalculationMode : 
                                                  curvatureCalculationMode__Type;
                                                  basicVehicleContainerHighFrequency__yawRate : 
                                                  yawRate__Type;
                                                  basicVehicleContainerHighFrequency__accelerationControl : 
                                                  accelerationControl__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__lanePosition : 
                                                  lanePosition__Type option;
                                                  basicVehicleContainerHighFrequency__steeringWheelAngle : 
                                                  steeringWheelAngle__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__lateralAcceleration : 
                                                  lateralAcceleration__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__verticalAcceleration : 
                                                  verticalAcceleration__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__performanceClass : 
                                                  performanceClass__Type option;
                                                  basicVehicleContainerHighFrequency__cenDsrcTollingZone : 
                                                  cenDsrcTollingZone__Type
                                                  option }

(** val basicVehicleContainerHighFrequency__list : seq_elem list **)

let basicVehicleContainerHighFrequency__list =
  Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: [])))))))))))))))

type basicVehicleContainerHighFrequency__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))))))))

(** val basicVehicleContainerHighFrequency__Format_list :
    basicVehicleContainerHighFrequency__Format_Type **)

let basicVehicleContainerHighFrequency__Format_list =
  ((Obj.magic heading__Format), ((Obj.magic speed__Format),
    ((Obj.magic driveDirection__Format), ((Obj.magic vehicleLength__Format),
    ((Obj.magic vehicleWidth__Format),
    ((Obj.magic longitudinalAcceleration__Format),
    ((Obj.magic curvature__Format),
    ((Obj.magic curvatureCalculationMode__Format),
    ((Obj.magic yawRate__Format), ((Obj.magic accelerationControl__Format),
    ((Obj.magic lanePosition__Format),
    ((Obj.magic steeringWheelAngle__Format),
    ((Obj.magic lateralAcceleration__Format),
    ((Obj.magic verticalAcceleration__Format),
    ((Obj.magic performanceClass__Format),
    ((Obj.magic cenDsrcTollingZone__Format),
    (Obj.magic unit_format)))))))))))))))))

(** val basicVehicleContainerHighFrequency__list__Format :
    seq_type t_Format **)

let basicVehicleContainerHighFrequency__list__Format =
  seq_format basicVehicleContainerHighFrequency__list
    (Obj.magic basicVehicleContainerHighFrequency__Format_list)

(** val basicVehicleContainerHighFrequency__F1 :
    basicVehicleContainerHighFrequency__Type ->
    heading__Type * (speed__Type * (driveDirection__Type * (vehicleLength__Type * (vehicleWidth__Type * (longitudinalAcceleration__Type * (curvature__Type * (curvatureCalculationMode__Type * (yawRate__Type * (accelerationControl__Type
    option * (lanePosition__Type option * (steeringWheelAngle__Type
    option * (lateralAcceleration__Type option * (verticalAcceleration__Type
    option * (performanceClass__Type option * (cenDsrcTollingZone__Type
    option * unit))))))))))))))) **)

let basicVehicleContainerHighFrequency__F1 z0 =
  (z0.basicVehicleContainerHighFrequency__heading,
    (z0.basicVehicleContainerHighFrequency__speed,
    (z0.basicVehicleContainerHighFrequency__driveDirection,
    (z0.basicVehicleContainerHighFrequency__vehicleLength,
    (z0.basicVehicleContainerHighFrequency__vehicleWidth,
    (z0.basicVehicleContainerHighFrequency__longitudinalAcceleration,
    (z0.basicVehicleContainerHighFrequency__curvature,
    (z0.basicVehicleContainerHighFrequency__curvatureCalculationMode,
    (z0.basicVehicleContainerHighFrequency__yawRate,
    (z0.basicVehicleContainerHighFrequency__accelerationControl,
    (z0.basicVehicleContainerHighFrequency__lanePosition,
    (z0.basicVehicleContainerHighFrequency__steeringWheelAngle,
    (z0.basicVehicleContainerHighFrequency__lateralAcceleration,
    (z0.basicVehicleContainerHighFrequency__verticalAcceleration,
    (z0.basicVehicleContainerHighFrequency__performanceClass,
    (z0.basicVehicleContainerHighFrequency__cenDsrcTollingZone,
    ()))))))))))))))))

(** val basicVehicleContainerHighFrequency__F2 :
    seq_type -> basicVehicleContainerHighFrequency__Type **)

let basicVehicleContainerHighFrequency__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, p1) = p0 in
  let (i4, p2) = p1 in
  let (i5, p3) = p2 in
  let (i6, p4) = p3 in
  let (i7, p5) = p4 in
  let (i8, p6) = p5 in
  let (i9, p7) = p6 in
  let (i10, p8) = p7 in
  let (i11, p9) = p8 in
  let (i12, p10) = p9 in
  let (i13, p11) = p10 in
  let (i14, p12) = p11 in
  let (i15, _) = p12 in
  { basicVehicleContainerHighFrequency__heading = i0;
  basicVehicleContainerHighFrequency__speed = i1;
  basicVehicleContainerHighFrequency__driveDirection = i2;
  basicVehicleContainerHighFrequency__vehicleLength = i3;
  basicVehicleContainerHighFrequency__vehicleWidth = i4;
  basicVehicleContainerHighFrequency__longitudinalAcceleration = i5;
  basicVehicleContainerHighFrequency__curvature = i6;
  basicVehicleContainerHighFrequency__curvatureCalculationMode = i7;
  basicVehicleContainerHighFrequency__yawRate = i8;
  basicVehicleContainerHighFrequency__accelerationControl = i9;
  basicVehicleContainerHighFrequency__lanePosition = i10;
  basicVehicleContainerHighFrequency__steeringWheelAngle = i11;
  basicVehicleContainerHighFrequency__lateralAcceleration = i12;
  basicVehicleContainerHighFrequency__verticalAcceleration = i13;
  basicVehicleContainerHighFrequency__performanceClass = i14;
  basicVehicleContainerHighFrequency__cenDsrcTollingZone = i15 }

(** val basicVehicleContainerHighFrequency__Format :
    basicVehicleContainerHighFrequency__Type t_Format **)

let basicVehicleContainerHighFrequency__Format =
  proj2_format basicVehicleContainerHighFrequency__list__Format
    (Obj.magic basicVehicleContainerHighFrequency__F1)
    basicVehicleContainerHighFrequency__F2

type protectedZoneType__root__Type =
| ProtectedZoneType__root__permanentCenDsrcTolling

(** val protectedZoneType__root__nat__Format : int t_Format **)

let protectedZoneType__root__nat__Format =
  nat_enum_format 0

(** val protectedZoneType__root__F1 : protectedZoneType__root__Type -> int **)

let protectedZoneType__root__F1 _ =
  0

(** val protectedZoneType__root__F2 : int -> protectedZoneType__root__Type **)

let protectedZoneType__root__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ProtectedZoneType__root__permanentCenDsrcTolling)
    (fun _ -> ProtectedZoneType__root__permanentCenDsrcTolling)
    n0

type protectedZoneType__ext__Type =
| ProtectedZoneType__ext__temporaryCenDsrcTolling

(** val protectedZoneType__ext__F1 : protectedZoneType__ext__Type -> int **)

let protectedZoneType__ext__F1 _ =
  0

(** val protectedZoneType__ext__F2 : int -> protectedZoneType__ext__Type **)

let protectedZoneType__ext__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ProtectedZoneType__ext__temporaryCenDsrcTolling)
    (fun _ -> ProtectedZoneType__ext__temporaryCenDsrcTolling)
    n0

(** val protectedZoneType__ext__helper_format : int t_Format **)

let protectedZoneType__ext__helper_format =
  restrict_format small_integer_format (fun a -> le_dec a 0)

type protectedZoneType__Type =
  (protectedZoneType__root__Type, protectedZoneType__ext__Type) sum

(** val protectedZoneType__root__Format :
    protectedZoneType__root__Type t_Format **)

let protectedZoneType__root__Format =
  proj3_format protectedZoneType__root__nat__Format
    protectedZoneType__root__F1 protectedZoneType__root__F2

(** val protectedZoneType__ext__Format :
    protectedZoneType__ext__Type t_Format **)

let protectedZoneType__ext__Format =
  proj3_format protectedZoneType__ext__helper_format
    protectedZoneType__ext__F1 protectedZoneType__ext__F2

(** val protectedZoneType__Format : protectedZoneType__Type t_Format **)

let protectedZoneType__Format =
  sum_format protectedZoneType__root__Format protectedZoneType__ext__Format

type timestampIts__Type = int

(** val timestampIts__Format : int t_Format **)

let timestampIts__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))))))))))))))))))))))))))))

type protectedZoneRadius__Type = int

(** val protectedZoneRadius__Format : int t_Format **)

let protectedZoneRadius__Format =
  int_format_ranged_ext 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type protectedCommunicationZone__Type = { protectedCommunicationZone__protectedZoneType : 
                                          protectedZoneType__Type;
                                          protectedCommunicationZone__expiryTime : 
                                          timestampIts__Type option;
                                          protectedCommunicationZone__protectedZoneLatitude : 
                                          latitude__Type;
                                          protectedCommunicationZone__protectedZoneLongitude : 
                                          longitude__Type;
                                          protectedCommunicationZone__protectedZoneRadius : 
                                          protectedZoneRadius__Type option;
                                          protectedCommunicationZone__protectedZoneID : 
                                          protectedZoneID__Type option }

(** val protectedCommunicationZone__root_list : seq_elem list **)

let protectedCommunicationZone__root_list =
  Nor :: (Opt :: (Nor :: (Nor :: (Opt :: (Opt :: [])))))

(** val protectedCommunicationZone__ext_list : typ list **)

let protectedCommunicationZone__ext_list =
  []

type protectedCommunicationZone__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

(** val protectedCommunicationZone__root_Format_list :
    protectedCommunicationZone__root_Format_Type **)

let protectedCommunicationZone__root_Format_list =
  ((Obj.magic protectedZoneType__Format), ((Obj.magic timestampIts__Format),
    ((Obj.magic latitude__Format), ((Obj.magic longitude__Format),
    ((Obj.magic protectedZoneRadius__Format),
    ((Obj.magic protectedZoneID__Format), (Obj.magic unit_format)))))))

type protectedCommunicationZone__ext_Format_Type = unit t_Format

(** val protectedCommunicationZone__ext_Format_list :
    protectedCommunicationZone__ext_Format_Type **)

let protectedCommunicationZone__ext_Format_list =
  unit__Format

type protectedCommunicationZone__list_type = seq_type * seq_ext_type

(** val protectedCommunicationZone__list_format :
    protectedCommunicationZone__list_type t_Format **)

let protectedCommunicationZone__list_format =
  seq_ext_format protectedCommunicationZone__root_list
    (Obj.magic protectedCommunicationZone__root_Format_list)
    protectedCommunicationZone__ext_list
    (Obj.magic protectedCommunicationZone__ext_Format_list)

(** val protectedCommunicationZone__F1 :
    protectedCommunicationZone__Type -> protectedCommunicationZone__list_type **)

let protectedCommunicationZone__F1 z0 =
  ((Obj.magic (z0.protectedCommunicationZone__protectedZoneType,
     (z0.protectedCommunicationZone__expiryTime,
     (z0.protectedCommunicationZone__protectedZoneLatitude,
     (z0.protectedCommunicationZone__protectedZoneLongitude,
     (z0.protectedCommunicationZone__protectedZoneRadius,
     (z0.protectedCommunicationZone__protectedZoneID, ()))))))),
    (Obj.magic ()))

(** val protectedCommunicationZone__F2 :
    protectedCommunicationZone__list_type -> protectedCommunicationZone__Type **)

let protectedCommunicationZone__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, p1) = p0 in
  let (j4, p2) = p1 in
  let (j5, _) = p2 in
  { protectedCommunicationZone__protectedZoneType = j0;
  protectedCommunicationZone__expiryTime = j1;
  protectedCommunicationZone__protectedZoneLatitude = j2;
  protectedCommunicationZone__protectedZoneLongitude = j3;
  protectedCommunicationZone__protectedZoneRadius = j4;
  protectedCommunicationZone__protectedZoneID = j5 }

(** val protectedCommunicationZone__Format :
    protectedCommunicationZone__Type t_Format **)

let protectedCommunicationZone__Format =
  proj2_format protectedCommunicationZone__list_format
    protectedCommunicationZone__F1 protectedCommunicationZone__F2

type protectedCommunicationZonesRSU__Type =
  protectedCommunicationZone__Type list

(** val protectedCommunicationZonesRSU__Format :
    protectedCommunicationZonesRSU__Type t_Format **)

let protectedCommunicationZonesRSU__Format =
  seq_of_format protectedCommunicationZone__Format 1 ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))

type rSUContainerHighFrequency__Type = { rSUContainerHighFrequency__protectedCommunicationZonesRSU : 
                                         protectedCommunicationZonesRSU__Type
                                         option }

(** val rSUContainerHighFrequency__root_list : seq_elem list **)

let rSUContainerHighFrequency__root_list =
  Opt :: []

(** val rSUContainerHighFrequency__ext_list : typ list **)

let rSUContainerHighFrequency__ext_list =
  []

type rSUContainerHighFrequency__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

(** val rSUContainerHighFrequency__root_Format_list :
    rSUContainerHighFrequency__root_Format_Type **)

let rSUContainerHighFrequency__root_Format_list =
  ((Obj.magic protectedCommunicationZonesRSU__Format), (Obj.magic unit_format))

type rSUContainerHighFrequency__ext_Format_Type = unit t_Format

(** val rSUContainerHighFrequency__ext_Format_list :
    rSUContainerHighFrequency__ext_Format_Type **)

let rSUContainerHighFrequency__ext_Format_list =
  unit__Format

type rSUContainerHighFrequency__list_type = seq_type * seq_ext_type

(** val rSUContainerHighFrequency__list_format :
    rSUContainerHighFrequency__list_type t_Format **)

let rSUContainerHighFrequency__list_format =
  seq_ext_format rSUContainerHighFrequency__root_list
    (Obj.magic rSUContainerHighFrequency__root_Format_list)
    rSUContainerHighFrequency__ext_list
    (Obj.magic rSUContainerHighFrequency__ext_Format_list)

(** val rSUContainerHighFrequency__F1 :
    rSUContainerHighFrequency__Type -> rSUContainerHighFrequency__list_type **)

let rSUContainerHighFrequency__F1 z0 =
  ((Obj.magic (z0.rSUContainerHighFrequency__protectedCommunicationZonesRSU,
     ())), (Obj.magic ()))

(** val rSUContainerHighFrequency__F2 :
    rSUContainerHighFrequency__list_type -> rSUContainerHighFrequency__Type **)

let rSUContainerHighFrequency__F2 = function
| (s, _) ->
  let (j0, _) = Obj.magic s in
  { rSUContainerHighFrequency__protectedCommunicationZonesRSU = j0 }

(** val rSUContainerHighFrequency__Format :
    rSUContainerHighFrequency__Type t_Format **)

let rSUContainerHighFrequency__Format =
  proj2_format rSUContainerHighFrequency__list_format
    rSUContainerHighFrequency__F1 rSUContainerHighFrequency__F2

type highFrequencyContainer__root__Type =
| HighFrequencyContainer__root__basicVehicleContainerHighFrequency of 
   basicVehicleContainerHighFrequency__Type
| HighFrequencyContainer__root__rsuContainerHighFrequency of rSUContainerHighFrequency__Type

type highFrequencyContainer__ext__Type = empty_set

type highFrequencyContainer__Type =
  (highFrequencyContainer__root__Type, highFrequencyContainer__ext__Type) sum

(** val highFrequencyContainer__root__list__Format :
    (int, __) sigT t_Format **)

let highFrequencyContainer__root__list__Format =
  { t_Serial = (fun bf pos c ->
    match restrict_serialize (fun a ->
            le_dec a
              ((-) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
            (put_n_nat
              ((+)
                (BigArrayExtr.log2
                  ((-) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))) bf pos
            (let ExistT (a, _) = c in a) with
    | Some p ->
      let (p0, _) = p in
      let (bf', pos') = p0 in
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         Obj.magic basicVehicleContainerHighFrequency__Format.t_Serial bf'
           pos' (let ExistT (_, h) = c in h))
         (fun n0 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           Obj.magic rSUContainerHighFrequency__Format.t_Serial bf' pos'
             (let ExistT (_, h) = c in h))
           (fun n1 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> assert false (* absurd case *))
             (fun _ -> assert false (* absurd case *))
             n1)
           n0)
         (let ExistT (a, _) = c in a))
    | None -> None); t_Parse =
    (bind_parse
      (restrict_parse (fun a ->
        le_dec a
          ((-) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
        (read_n_nat
          ((+)
            (BigArrayExtr.log2
              ((-) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
            (Stdlib.Int.succ 0)))) (fun n0 _ _ ->
      bind_parse
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           Obj.magic basicVehicleContainerHighFrequency__Format.t_Parse)
           (fun n1 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ ->
             Obj.magic rSUContainerHighFrequency__Format.t_Parse)
             (fun n2 _ _ ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> None)
               (fun _ -> None)
               n2)
             n1)
           n0) (fun v _ flg0 -> return_parse (Exist (ExistT (n0, v))) flg0)));
    t_to_len = (fun c ->
    let ExistT (n0, a) = c in
    if (<=) n0 (Stdlib.Int.succ (Stdlib.Int.succ 0))
    then add_opt (Some
           ((+)
             (BigArrayExtr.log2
               ((-) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
             (Stdlib.Int.succ 0)))
           ((fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              Obj.magic basicVehicleContainerHighFrequency__Format.t_to_len a)
              (fun n1 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                Obj.magic rSUContainerHighFrequency__Format.t_to_len a)
                (fun n2 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> assert false (* absurd case *))
                  (fun _ -> assert false (* absurd case *))
                  n2)
                n1)
              n0)
    else None) }

(** val highFrequencyContainer__root__F1 :
    highFrequencyContainer__root__Type -> choice **)

let highFrequencyContainer__root__F1 = function
| HighFrequencyContainer__root__basicVehicleContainerHighFrequency t ->
  ExistT (0, (Obj.magic t))
| HighFrequencyContainer__root__rsuContainerHighFrequency t ->
  ExistT ((Stdlib.Int.succ 0), (Obj.magic t))

(** val highFrequencyContainer__root__F2 :
    choice -> highFrequencyContainer__root__Type **)

let highFrequencyContainer__root__F2 = function
| ExistT (x0, t0) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     HighFrequencyContainer__root__basicVehicleContainerHighFrequency
     (Obj.magic t0))
     (fun n0 ->
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> HighFrequencyContainer__root__rsuContainerHighFrequency
       (Obj.magic t0))
       (fun _ -> assert false (* absurd case *))
       n0)
     x0)

(** val highFrequencyContainer__root__Format :
    highFrequencyContainer__root__Type t_Format **)

let highFrequencyContainer__root__Format =
  proj2_format highFrequencyContainer__root__list__Format
    highFrequencyContainer__root__F1 highFrequencyContainer__root__F2

(** val highFrequencyContainer__ext__Format :
    highFrequencyContainer__ext__Type t_Format **)

let highFrequencyContainer__ext__Format =
  empty_format

(** val highFrequencyContainer__Format :
    highFrequencyContainer__Type t_Format **)

let highFrequencyContainer__Format =
  sum_format highFrequencyContainer__root__Format
    highFrequencyContainer__ext__Format

type vehicleRole__Type =
| VehicleRole__default
| VehicleRole__publicTransport
| VehicleRole__specialTransport
| VehicleRole__dangerousGoods
| VehicleRole__roadWork
| VehicleRole__rescue
| VehicleRole__emergency
| VehicleRole__safetyCar
| VehicleRole__agriculture
| VehicleRole__commercial
| VehicleRole__military
| VehicleRole__roadOperator
| VehicleRole__taxi
| VehicleRole__reserved1
| VehicleRole__reserved2
| VehicleRole__reserved3

(** val vehicleRole__nat__Format : int t_Format **)

let vehicleRole__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))

(** val vehicleRole__F1 : vehicleRole__Type -> int **)

let vehicleRole__F1 = function
| VehicleRole__default -> 0
| VehicleRole__publicTransport -> Stdlib.Int.succ 0
| VehicleRole__specialTransport -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| VehicleRole__dangerousGoods ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| VehicleRole__roadWork ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| VehicleRole__rescue ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| VehicleRole__emergency ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| VehicleRole__safetyCar ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
| VehicleRole__agriculture ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))
| VehicleRole__commercial ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))
| VehicleRole__military ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))
| VehicleRole__roadOperator ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
| VehicleRole__taxi ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))
| VehicleRole__reserved1 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))
| VehicleRole__reserved2 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))
| VehicleRole__reserved3 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))

(** val vehicleRole__F2 : int -> vehicleRole__Type **)

let vehicleRole__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> VehicleRole__default)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> VehicleRole__publicTransport)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> VehicleRole__specialTransport)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> VehicleRole__dangerousGoods)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> VehicleRole__roadWork)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> VehicleRole__rescue)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> VehicleRole__emergency)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> VehicleRole__safetyCar)
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> VehicleRole__agriculture)
                    (fun n9 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> VehicleRole__commercial)
                      (fun n10 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> VehicleRole__military)
                        (fun n11 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> VehicleRole__roadOperator)
                          (fun n12 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> VehicleRole__taxi)
                            (fun n13 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> VehicleRole__reserved1)
                              (fun n14 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> VehicleRole__reserved2)
                                (fun n15 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> VehicleRole__reserved3)
                                  (fun _ -> VehicleRole__default)
                                  n15)
                                n14)
                              n13)
                            n12)
                          n11)
                        n10)
                      n9)
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val vehicleRole__Format : vehicleRole__Type t_Format **)

let vehicleRole__Format =
  proj3_format vehicleRole__nat__Format vehicleRole__F1 vehicleRole__F2

type exteriorLights__Type = bit_string_fixed

(** val exteriorLights__Format : exteriorLights__Type t_Format **)

let exteriorLights__Format =
  bit_string_fixed_format ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

type deltaLatitude__Type = int

(** val deltaLatitude__Format : int t_Format **)

let deltaLatitude__Format =
  ranged_int_format ((~-) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1))))))))))))))))) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1)))))))))))))))))

type deltaLongitude__Type = int

(** val deltaLongitude__Format : int t_Format **)

let deltaLongitude__Format =
  ranged_int_format ((~-) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1))))))))))))))))) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1)))))))))))))))))

type deltaAltitude__Type = int

(** val deltaAltitude__Format : int t_Format **)

let deltaAltitude__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1)))))))))))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    1)))))))))))))

type deltaReferencePosition__Type = { deltaReferencePosition__deltaLatitude : 
                                      deltaLatitude__Type;
                                      deltaReferencePosition__deltaLongitude : 
                                      deltaLongitude__Type;
                                      deltaReferencePosition__deltaAltitude : 
                                      deltaAltitude__Type }

(** val deltaReferencePosition__list : seq_elem list **)

let deltaReferencePosition__list =
  Nor :: (Nor :: (Nor :: []))

type deltaReferencePosition__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val deltaReferencePosition__Format_list :
    deltaReferencePosition__Format_Type **)

let deltaReferencePosition__Format_list =
  ((Obj.magic deltaLatitude__Format), ((Obj.magic deltaLongitude__Format),
    ((Obj.magic deltaAltitude__Format), (Obj.magic unit_format))))

(** val deltaReferencePosition__list__Format : seq_type t_Format **)

let deltaReferencePosition__list__Format =
  seq_format deltaReferencePosition__list
    (Obj.magic deltaReferencePosition__Format_list)

(** val deltaReferencePosition__F1 :
    deltaReferencePosition__Type ->
    deltaLatitude__Type * (deltaLongitude__Type * (deltaAltitude__Type * unit)) **)

let deltaReferencePosition__F1 z0 =
  (z0.deltaReferencePosition__deltaLatitude,
    (z0.deltaReferencePosition__deltaLongitude,
    (z0.deltaReferencePosition__deltaAltitude, ())))

(** val deltaReferencePosition__F2 :
    seq_type -> deltaReferencePosition__Type **)

let deltaReferencePosition__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { deltaReferencePosition__deltaLatitude = i0;
  deltaReferencePosition__deltaLongitude = i1;
  deltaReferencePosition__deltaAltitude = i2 }

(** val deltaReferencePosition__Format :
    deltaReferencePosition__Type t_Format **)

let deltaReferencePosition__Format =
  proj2_format deltaReferencePosition__list__Format
    (Obj.magic deltaReferencePosition__F1) deltaReferencePosition__F2

type pathDeltaTime__Type = int

(** val pathDeltaTime__Format : int t_Format **)

let pathDeltaTime__Format =
  int_format_ranged_ext 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    1)))))))))))))))

type pathPoint__Type = { pathPoint__pathPosition : deltaReferencePosition__Type;
                         pathPoint__pathDeltaTime : pathDeltaTime__Type option }

(** val pathPoint__list : seq_elem list **)

let pathPoint__list =
  Nor :: (Opt :: [])

type pathPoint__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val pathPoint__Format_list : pathPoint__Format_Type **)

let pathPoint__Format_list =
  ((Obj.magic deltaReferencePosition__Format),
    ((Obj.magic pathDeltaTime__Format), (Obj.magic unit_format)))

(** val pathPoint__list__Format : seq_type t_Format **)

let pathPoint__list__Format =
  seq_format pathPoint__list (Obj.magic pathPoint__Format_list)

(** val pathPoint__F1 :
    pathPoint__Type -> deltaReferencePosition__Type * (pathDeltaTime__Type
    option * unit) **)

let pathPoint__F1 z0 =
  (z0.pathPoint__pathPosition, (z0.pathPoint__pathDeltaTime, ()))

(** val pathPoint__F2 : seq_type -> pathPoint__Type **)

let pathPoint__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { pathPoint__pathPosition = i0; pathPoint__pathDeltaTime = i1 }

(** val pathPoint__Format : pathPoint__Type t_Format **)

let pathPoint__Format =
  proj2_format pathPoint__list__Format (Obj.magic pathPoint__F1) pathPoint__F2

type pathHistory__Type = pathPoint__Type list

(** val pathHistory__Format : pathHistory__Type t_Format **)

let pathHistory__Format =
  seq_of_format pathPoint__Format 0 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))

type basicVehicleContainerLowFrequency__Type = { basicVehicleContainerLowFrequency__vehicleRole : 
                                                 vehicleRole__Type;
                                                 basicVehicleContainerLowFrequency__exteriorLights : 
                                                 exteriorLights__Type;
                                                 basicVehicleContainerLowFrequency__pathHistory : 
                                                 pathHistory__Type }

(** val basicVehicleContainerLowFrequency__list : seq_elem list **)

let basicVehicleContainerLowFrequency__list =
  Nor :: (Nor :: (Nor :: []))

type basicVehicleContainerLowFrequency__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val basicVehicleContainerLowFrequency__Format_list :
    basicVehicleContainerLowFrequency__Format_Type **)

let basicVehicleContainerLowFrequency__Format_list =
  ((Obj.magic vehicleRole__Format), ((Obj.magic exteriorLights__Format),
    ((Obj.magic pathHistory__Format), (Obj.magic unit_format))))

(** val basicVehicleContainerLowFrequency__list__Format : seq_type t_Format **)

let basicVehicleContainerLowFrequency__list__Format =
  seq_format basicVehicleContainerLowFrequency__list
    (Obj.magic basicVehicleContainerLowFrequency__Format_list)

(** val basicVehicleContainerLowFrequency__F1 :
    basicVehicleContainerLowFrequency__Type ->
    vehicleRole__Type * (exteriorLights__Type * (pathHistory__Type * unit)) **)

let basicVehicleContainerLowFrequency__F1 z0 =
  (z0.basicVehicleContainerLowFrequency__vehicleRole,
    (z0.basicVehicleContainerLowFrequency__exteriorLights,
    (z0.basicVehicleContainerLowFrequency__pathHistory, ())))

(** val basicVehicleContainerLowFrequency__F2 :
    seq_type -> basicVehicleContainerLowFrequency__Type **)

let basicVehicleContainerLowFrequency__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { basicVehicleContainerLowFrequency__vehicleRole = i0;
  basicVehicleContainerLowFrequency__exteriorLights = i1;
  basicVehicleContainerLowFrequency__pathHistory = i2 }

(** val basicVehicleContainerLowFrequency__Format :
    basicVehicleContainerLowFrequency__Type t_Format **)

let basicVehicleContainerLowFrequency__Format =
  proj2_format basicVehicleContainerLowFrequency__list__Format
    (Obj.magic basicVehicleContainerLowFrequency__F1)
    basicVehicleContainerLowFrequency__F2

type lowFrequencyContainer__root__Type =
| LowFrequencyContainer__root__basicVehicleContainerLowFrequency of basicVehicleContainerLowFrequency__Type

type lowFrequencyContainer__ext__Type = empty_set

type lowFrequencyContainer__Type =
  (lowFrequencyContainer__root__Type, lowFrequencyContainer__ext__Type) sum

(** val lowFrequencyContainer__root__F1 :
    lowFrequencyContainer__root__Type ->
    basicVehicleContainerLowFrequency__Type **)

let lowFrequencyContainer__root__F1 = function
| LowFrequencyContainer__root__basicVehicleContainerLowFrequency t -> t

(** val lowFrequencyContainer__root__F2 :
    basicVehicleContainerLowFrequency__Type ->
    lowFrequencyContainer__root__Type **)

let lowFrequencyContainer__root__F2 y =
  LowFrequencyContainer__root__basicVehicleContainerLowFrequency y

(** val lowFrequencyContainer__root__Format :
    lowFrequencyContainer__root__Type t_Format **)

let lowFrequencyContainer__root__Format =
  proj2_format basicVehicleContainerLowFrequency__Format
    lowFrequencyContainer__root__F1 lowFrequencyContainer__root__F2

(** val lowFrequencyContainer__ext__Format :
    lowFrequencyContainer__ext__Type t_Format **)

let lowFrequencyContainer__ext__Format =
  empty_format

(** val lowFrequencyContainer__Format :
    lowFrequencyContainer__Type t_Format **)

let lowFrequencyContainer__Format =
  sum_format lowFrequencyContainer__root__Format
    lowFrequencyContainer__ext__Format

type embarkationStatus__Type = bool

(** val embarkationStatus__Format : bool t_Format **)

let embarkationStatus__Format =
  bool__Format

type ptActivationType__Type = int

(** val ptActivationType__Format : int t_Format **)

let ptActivationType__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type ptActivationData__Type = octet_string

(** val ptActivationData__Format : ptActivationData__Type t_Format **)

let ptActivationData__Format =
  octet_string_ranged_format 1 ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1))))

type ptActivation__Type = { ptActivation__ptActivationType : ptActivationType__Type;
                            ptActivation__ptActivationData : ptActivationData__Type }

(** val ptActivation__list : seq_elem list **)

let ptActivation__list =
  Nor :: (Nor :: [])

type ptActivation__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val ptActivation__Format_list : ptActivation__Format_Type **)

let ptActivation__Format_list =
  ((Obj.magic ptActivationType__Format),
    ((Obj.magic ptActivationData__Format), (Obj.magic unit_format)))

(** val ptActivation__list__Format : seq_type t_Format **)

let ptActivation__list__Format =
  seq_format ptActivation__list (Obj.magic ptActivation__Format_list)

(** val ptActivation__F1 :
    ptActivation__Type ->
    ptActivationType__Type * (ptActivationData__Type * unit) **)

let ptActivation__F1 z0 =
  (z0.ptActivation__ptActivationType, (z0.ptActivation__ptActivationData, ()))

(** val ptActivation__F2 : seq_type -> ptActivation__Type **)

let ptActivation__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { ptActivation__ptActivationType = i0; ptActivation__ptActivationData = i1 }

(** val ptActivation__Format : ptActivation__Type t_Format **)

let ptActivation__Format =
  proj2_format ptActivation__list__Format (Obj.magic ptActivation__F1)
    ptActivation__F2

type publicTransportContainer__Type = { publicTransportContainer__embarkationStatus : 
                                        embarkationStatus__Type;
                                        publicTransportContainer__ptActivation : 
                                        ptActivation__Type option }

(** val publicTransportContainer__list : seq_elem list **)

let publicTransportContainer__list =
  Nor :: (Opt :: [])

type publicTransportContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val publicTransportContainer__Format_list :
    publicTransportContainer__Format_Type **)

let publicTransportContainer__Format_list =
  ((Obj.magic embarkationStatus__Format), ((Obj.magic ptActivation__Format),
    (Obj.magic unit_format)))

(** val publicTransportContainer__list__Format : seq_type t_Format **)

let publicTransportContainer__list__Format =
  seq_format publicTransportContainer__list
    (Obj.magic publicTransportContainer__Format_list)

(** val publicTransportContainer__F1 :
    publicTransportContainer__Type ->
    embarkationStatus__Type * (ptActivation__Type option * unit) **)

let publicTransportContainer__F1 z0 =
  (z0.publicTransportContainer__embarkationStatus,
    (z0.publicTransportContainer__ptActivation, ()))

(** val publicTransportContainer__F2 :
    seq_type -> publicTransportContainer__Type **)

let publicTransportContainer__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { publicTransportContainer__embarkationStatus = i0;
  publicTransportContainer__ptActivation = i1 }

(** val publicTransportContainer__Format :
    publicTransportContainer__Type t_Format **)

let publicTransportContainer__Format =
  proj2_format publicTransportContainer__list__Format
    (Obj.magic publicTransportContainer__F1) publicTransportContainer__F2

type specialTransportType__Type = bit_string_fixed

(** val specialTransportType__Format : specialTransportType__Type t_Format **)

let specialTransportType__Format =
  bit_string_fixed_format ((fun p->2*p) ((fun p->2*p) 1))

type lightBarSirenInUse__Type = bit_string_fixed

(** val lightBarSirenInUse__Format : lightBarSirenInUse__Type t_Format **)

let lightBarSirenInUse__Format =
  bit_string_fixed_format ((fun p->2*p) 1)

type specialTransportContainer__Type = { specialTransportContainer__specialTransportType : 
                                         specialTransportType__Type;
                                         specialTransportContainer__lightBarSirenInUse : 
                                         lightBarSirenInUse__Type }

(** val specialTransportContainer__list : seq_elem list **)

let specialTransportContainer__list =
  Nor :: (Nor :: [])

type specialTransportContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val specialTransportContainer__Format_list :
    specialTransportContainer__Format_Type **)

let specialTransportContainer__Format_list =
  ((Obj.magic specialTransportType__Format),
    ((Obj.magic lightBarSirenInUse__Format), (Obj.magic unit_format)))

(** val specialTransportContainer__list__Format : seq_type t_Format **)

let specialTransportContainer__list__Format =
  seq_format specialTransportContainer__list
    (Obj.magic specialTransportContainer__Format_list)

(** val specialTransportContainer__F1 :
    specialTransportContainer__Type ->
    specialTransportType__Type * (lightBarSirenInUse__Type * unit) **)

let specialTransportContainer__F1 z0 =
  (z0.specialTransportContainer__specialTransportType,
    (z0.specialTransportContainer__lightBarSirenInUse, ()))

(** val specialTransportContainer__F2 :
    seq_type -> specialTransportContainer__Type **)

let specialTransportContainer__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { specialTransportContainer__specialTransportType = i0;
  specialTransportContainer__lightBarSirenInUse = i1 }

(** val specialTransportContainer__Format :
    specialTransportContainer__Type t_Format **)

let specialTransportContainer__Format =
  proj2_format specialTransportContainer__list__Format
    (Obj.magic specialTransportContainer__F1) specialTransportContainer__F2

type dangerousGoodsBasic__Type =
| DangerousGoodsBasic__explosives1
| DangerousGoodsBasic__explosives2
| DangerousGoodsBasic__explosives3
| DangerousGoodsBasic__explosives4
| DangerousGoodsBasic__explosives5
| DangerousGoodsBasic__explosives6
| DangerousGoodsBasic__flammableGases
| DangerousGoodsBasic__nonFlammableGases
| DangerousGoodsBasic__toxicGases
| DangerousGoodsBasic__flammableLiquids
| DangerousGoodsBasic__flammableSolids
| DangerousGoodsBasic__substancesLiableToSpontaneousCombustion
| DangerousGoodsBasic__substancesEmittingFlammableGasesUponContactWithWater
| DangerousGoodsBasic__oxidizingSubstances
| DangerousGoodsBasic__organicPeroxides
| DangerousGoodsBasic__toxicSubstances
| DangerousGoodsBasic__infectiousSubstances
| DangerousGoodsBasic__radioactiveMaterial
| DangerousGoodsBasic__corrosiveSubstances
| DangerousGoodsBasic__miscellaneousDangerousSubstances

(** val dangerousGoodsBasic__nat__Format : int t_Format **)

let dangerousGoodsBasic__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))

(** val dangerousGoodsBasic__F1 : dangerousGoodsBasic__Type -> int **)

let dangerousGoodsBasic__F1 = function
| DangerousGoodsBasic__explosives1 -> 0
| DangerousGoodsBasic__explosives2 -> Stdlib.Int.succ 0
| DangerousGoodsBasic__explosives3 -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| DangerousGoodsBasic__explosives4 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| DangerousGoodsBasic__explosives5 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| DangerousGoodsBasic__explosives6 ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| DangerousGoodsBasic__flammableGases ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| DangerousGoodsBasic__nonFlammableGases ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
| DangerousGoodsBasic__toxicGases ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))
| DangerousGoodsBasic__flammableLiquids ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))
| DangerousGoodsBasic__flammableSolids ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))
| DangerousGoodsBasic__substancesLiableToSpontaneousCombustion ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
| DangerousGoodsBasic__substancesEmittingFlammableGasesUponContactWithWater ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))
| DangerousGoodsBasic__oxidizingSubstances ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))
| DangerousGoodsBasic__organicPeroxides ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))
| DangerousGoodsBasic__toxicSubstances ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))
| DangerousGoodsBasic__infectiousSubstances ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))
| DangerousGoodsBasic__radioactiveMaterial ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))
| DangerousGoodsBasic__corrosiveSubstances ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))
| DangerousGoodsBasic__miscellaneousDangerousSubstances ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))

(** val dangerousGoodsBasic__F2 : int -> dangerousGoodsBasic__Type **)

let dangerousGoodsBasic__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> DangerousGoodsBasic__explosives1)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> DangerousGoodsBasic__explosives2)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> DangerousGoodsBasic__explosives3)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> DangerousGoodsBasic__explosives4)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> DangerousGoodsBasic__explosives5)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> DangerousGoodsBasic__explosives6)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> DangerousGoodsBasic__flammableGases)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> DangerousGoodsBasic__nonFlammableGases)
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> DangerousGoodsBasic__toxicGases)
                    (fun n9 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ ->
                      DangerousGoodsBasic__flammableLiquids)
                      (fun n10 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ ->
                        DangerousGoodsBasic__flammableSolids)
                        (fun n11 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ ->
                          DangerousGoodsBasic__substancesLiableToSpontaneousCombustion)
                          (fun n12 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ ->
                            DangerousGoodsBasic__substancesEmittingFlammableGasesUponContactWithWater)
                            (fun n13 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ ->
                              DangerousGoodsBasic__oxidizingSubstances)
                              (fun n14 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ ->
                                DangerousGoodsBasic__organicPeroxides)
                                (fun n15 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ ->
                                  DangerousGoodsBasic__toxicSubstances)
                                  (fun n16 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ ->
                                    DangerousGoodsBasic__infectiousSubstances)
                                    (fun n17 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ ->
                                      DangerousGoodsBasic__radioactiveMaterial)
                                      (fun n18 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ ->
                                        DangerousGoodsBasic__corrosiveSubstances)
                                        (fun n19 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ ->
                                          DangerousGoodsBasic__miscellaneousDangerousSubstances)
                                          (fun _ ->
                                          DangerousGoodsBasic__explosives1)
                                          n19)
                                        n18)
                                      n17)
                                    n16)
                                  n15)
                                n14)
                              n13)
                            n12)
                          n11)
                        n10)
                      n9)
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val dangerousGoodsBasic__Format : dangerousGoodsBasic__Type t_Format **)

let dangerousGoodsBasic__Format =
  proj3_format dangerousGoodsBasic__nat__Format dangerousGoodsBasic__F1
    dangerousGoodsBasic__F2

type dangerousGoodsContainer__Type = { dangerousGoodsContainer__dangerousGoodsBasic : 
                                       dangerousGoodsBasic__Type }

(** val dangerousGoodsContainer__list : seq_elem list **)

let dangerousGoodsContainer__list =
  Nor :: []

type dangerousGoodsContainer__Format_Type =
  seq_elem_to_format * seq_elem_to_format

(** val dangerousGoodsContainer__Format_list :
    dangerousGoodsContainer__Format_Type **)

let dangerousGoodsContainer__Format_list =
  ((Obj.magic dangerousGoodsBasic__Format), (Obj.magic unit_format))

(** val dangerousGoodsContainer__list__Format : seq_type t_Format **)

let dangerousGoodsContainer__list__Format =
  seq_format dangerousGoodsContainer__list
    (Obj.magic dangerousGoodsContainer__Format_list)

(** val dangerousGoodsContainer__F1 :
    dangerousGoodsContainer__Type -> dangerousGoodsBasic__Type * unit **)

let dangerousGoodsContainer__F1 z0 =
  (z0.dangerousGoodsContainer__dangerousGoodsBasic, ())

(** val dangerousGoodsContainer__F2 :
    seq_type -> dangerousGoodsContainer__Type **)

let dangerousGoodsContainer__F2 y =
  let (i0, _) = Obj.magic y in
  { dangerousGoodsContainer__dangerousGoodsBasic = i0 }

(** val dangerousGoodsContainer__Format :
    dangerousGoodsContainer__Type t_Format **)

let dangerousGoodsContainer__Format =
  proj2_format dangerousGoodsContainer__list__Format
    (Obj.magic dangerousGoodsContainer__F1) dangerousGoodsContainer__F2

type roadworksSubCauseCode__Type = int

(** val roadworksSubCauseCode__Format : int t_Format **)

let roadworksSubCauseCode__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type hardShoulderStatus__Type =
| HardShoulderStatus__availableForStopping
| HardShoulderStatus__closed
| HardShoulderStatus__availableForDriving

(** val hardShoulderStatus__nat__Format : int t_Format **)

let hardShoulderStatus__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val hardShoulderStatus__F1 : hardShoulderStatus__Type -> int **)

let hardShoulderStatus__F1 = function
| HardShoulderStatus__availableForStopping -> 0
| HardShoulderStatus__closed -> Stdlib.Int.succ 0
| HardShoulderStatus__availableForDriving ->
  Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val hardShoulderStatus__F2 : int -> hardShoulderStatus__Type **)

let hardShoulderStatus__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> HardShoulderStatus__availableForStopping)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> HardShoulderStatus__closed)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> HardShoulderStatus__availableForDriving)
        (fun _ -> HardShoulderStatus__availableForStopping)
        n2)
      n1)
    n0

(** val hardShoulderStatus__Format : hardShoulderStatus__Type t_Format **)

let hardShoulderStatus__Format =
  proj3_format hardShoulderStatus__nat__Format hardShoulderStatus__F1
    hardShoulderStatus__F2

type drivingLaneStatus__Type = bit_string

(** val drivingLaneStatus__Format : drivingLaneStatus__Type t_Format **)

let drivingLaneStatus__Format =
  bit_string_ranged_format 1 ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))

type closedLanes__Type = { closedLanes__innerhardShoulderStatus : hardShoulderStatus__Type
                                                                  option;
                           closedLanes__outerhardShoulderStatus : hardShoulderStatus__Type
                                                                  option;
                           closedLanes__drivingLaneStatus : drivingLaneStatus__Type
                                                            option }

(** val closedLanes__root_list : seq_elem list **)

let closedLanes__root_list =
  Opt :: (Opt :: (Opt :: []))

(** val closedLanes__ext_list : typ list **)

let closedLanes__ext_list =
  []

type closedLanes__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val closedLanes__root_Format_list : closedLanes__root_Format_Type **)

let closedLanes__root_Format_list =
  ((Obj.magic hardShoulderStatus__Format),
    ((Obj.magic hardShoulderStatus__Format),
    ((Obj.magic drivingLaneStatus__Format), (Obj.magic unit_format))))

type closedLanes__ext_Format_Type = unit t_Format

(** val closedLanes__ext_Format_list : closedLanes__ext_Format_Type **)

let closedLanes__ext_Format_list =
  unit__Format

type closedLanes__list_type = seq_type * seq_ext_type

(** val closedLanes__list_format : closedLanes__list_type t_Format **)

let closedLanes__list_format =
  seq_ext_format closedLanes__root_list
    (Obj.magic closedLanes__root_Format_list) closedLanes__ext_list
    (Obj.magic closedLanes__ext_Format_list)

(** val closedLanes__F1 : closedLanes__Type -> closedLanes__list_type **)

let closedLanes__F1 z0 =
  ((Obj.magic (z0.closedLanes__innerhardShoulderStatus,
     (z0.closedLanes__outerhardShoulderStatus,
     (z0.closedLanes__drivingLaneStatus, ())))), (Obj.magic ()))

(** val closedLanes__F2 : closedLanes__list_type -> closedLanes__Type **)

let closedLanes__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, _) = p in
  { closedLanes__innerhardShoulderStatus = j0;
  closedLanes__outerhardShoulderStatus = j1; closedLanes__drivingLaneStatus =
  j2 }

(** val closedLanes__Format : closedLanes__Type t_Format **)

let closedLanes__Format =
  proj2_format closedLanes__list_format closedLanes__F1 closedLanes__F2

type roadWorksContainerBasic__Type = { roadWorksContainerBasic__roadworksSubCauseCode : 
                                       roadworksSubCauseCode__Type option;
                                       roadWorksContainerBasic__lightBarSirenInUse : 
                                       lightBarSirenInUse__Type;
                                       roadWorksContainerBasic__closedLanes : 
                                       closedLanes__Type option }

(** val roadWorksContainerBasic__list : seq_elem list **)

let roadWorksContainerBasic__list =
  Opt :: (Nor :: (Opt :: []))

type roadWorksContainerBasic__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val roadWorksContainerBasic__Format_list :
    roadWorksContainerBasic__Format_Type **)

let roadWorksContainerBasic__Format_list =
  ((Obj.magic roadworksSubCauseCode__Format),
    ((Obj.magic lightBarSirenInUse__Format), ((Obj.magic closedLanes__Format),
    (Obj.magic unit_format))))

(** val roadWorksContainerBasic__list__Format : seq_type t_Format **)

let roadWorksContainerBasic__list__Format =
  seq_format roadWorksContainerBasic__list
    (Obj.magic roadWorksContainerBasic__Format_list)

(** val roadWorksContainerBasic__F1 :
    roadWorksContainerBasic__Type -> roadworksSubCauseCode__Type
    option * (lightBarSirenInUse__Type * (closedLanes__Type option * unit)) **)

let roadWorksContainerBasic__F1 z0 =
  (z0.roadWorksContainerBasic__roadworksSubCauseCode,
    (z0.roadWorksContainerBasic__lightBarSirenInUse,
    (z0.roadWorksContainerBasic__closedLanes, ())))

(** val roadWorksContainerBasic__F2 :
    seq_type -> roadWorksContainerBasic__Type **)

let roadWorksContainerBasic__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { roadWorksContainerBasic__roadworksSubCauseCode = i0;
  roadWorksContainerBasic__lightBarSirenInUse = i1;
  roadWorksContainerBasic__closedLanes = i2 }

(** val roadWorksContainerBasic__Format :
    roadWorksContainerBasic__Type t_Format **)

let roadWorksContainerBasic__Format =
  proj2_format roadWorksContainerBasic__list__Format
    (Obj.magic roadWorksContainerBasic__F1) roadWorksContainerBasic__F2

type rescueContainer__Type = { rescueContainer__lightBarSirenInUse : lightBarSirenInUse__Type }

(** val rescueContainer__list : seq_elem list **)

let rescueContainer__list =
  Nor :: []

type rescueContainer__Format_Type = seq_elem_to_format * seq_elem_to_format

(** val rescueContainer__Format_list : rescueContainer__Format_Type **)

let rescueContainer__Format_list =
  ((Obj.magic lightBarSirenInUse__Format), (Obj.magic unit_format))

(** val rescueContainer__list__Format : seq_type t_Format **)

let rescueContainer__list__Format =
  seq_format rescueContainer__list (Obj.magic rescueContainer__Format_list)

(** val rescueContainer__F1 :
    rescueContainer__Type -> lightBarSirenInUse__Type * unit **)

let rescueContainer__F1 z0 =
  (z0.rescueContainer__lightBarSirenInUse, ())

(** val rescueContainer__F2 : seq_type -> rescueContainer__Type **)

let rescueContainer__F2 y =
  let (i0, _) = Obj.magic y in { rescueContainer__lightBarSirenInUse = i0 }

(** val rescueContainer__Format : rescueContainer__Type t_Format **)

let rescueContainer__Format =
  proj2_format rescueContainer__list__Format (Obj.magic rescueContainer__F1)
    rescueContainer__F2

type causeCodeType__Type = int

(** val causeCodeType__Format : int t_Format **)

let causeCodeType__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type subCauseCodeType__Type = int

(** val subCauseCodeType__Format : int t_Format **)

let subCauseCodeType__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type causeCode__Type = { causeCode__causeCode : causeCodeType__Type;
                         causeCode__subCauseCode : subCauseCodeType__Type }

(** val causeCode__root_list : seq_elem list **)

let causeCode__root_list =
  Nor :: (Nor :: [])

(** val causeCode__ext_list : typ list **)

let causeCode__ext_list =
  []

type causeCode__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val causeCode__root_Format_list : causeCode__root_Format_Type **)

let causeCode__root_Format_list =
  ((Obj.magic causeCodeType__Format), ((Obj.magic subCauseCodeType__Format),
    (Obj.magic unit_format)))

type causeCode__ext_Format_Type = unit t_Format

(** val causeCode__ext_Format_list : causeCode__ext_Format_Type **)

let causeCode__ext_Format_list =
  unit__Format

type causeCode__list_type = seq_type * seq_ext_type

(** val causeCode__list_format : causeCode__list_type t_Format **)

let causeCode__list_format =
  seq_ext_format causeCode__root_list (Obj.magic causeCode__root_Format_list)
    causeCode__ext_list (Obj.magic causeCode__ext_Format_list)

(** val causeCode__F1 : causeCode__Type -> causeCode__list_type **)

let causeCode__F1 z0 =
  ((Obj.magic (z0.causeCode__causeCode, (z0.causeCode__subCauseCode, ()))),
    (Obj.magic ()))

(** val causeCode__F2 : causeCode__list_type -> causeCode__Type **)

let causeCode__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, _) = l in
  { causeCode__causeCode = j0; causeCode__subCauseCode = j1 }

(** val causeCode__Format : causeCode__Type t_Format **)

let causeCode__Format =
  proj2_format causeCode__list_format causeCode__F1 causeCode__F2

type emergencyPriority__Type = bit_string_fixed

(** val emergencyPriority__Format : emergencyPriority__Type t_Format **)

let emergencyPriority__Format =
  bit_string_fixed_format ((fun p->2*p) 1)

type emergencyContainer__Type = { emergencyContainer__lightBarSirenInUse : 
                                  lightBarSirenInUse__Type;
                                  emergencyContainer__incidentIndication : 
                                  causeCode__Type option;
                                  emergencyContainer__emergencyPriority : 
                                  emergencyPriority__Type option }

(** val emergencyContainer__list : seq_elem list **)

let emergencyContainer__list =
  Nor :: (Opt :: (Opt :: []))

type emergencyContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val emergencyContainer__Format_list : emergencyContainer__Format_Type **)

let emergencyContainer__Format_list =
  ((Obj.magic lightBarSirenInUse__Format), ((Obj.magic causeCode__Format),
    ((Obj.magic emergencyPriority__Format), (Obj.magic unit_format))))

(** val emergencyContainer__list__Format : seq_type t_Format **)

let emergencyContainer__list__Format =
  seq_format emergencyContainer__list
    (Obj.magic emergencyContainer__Format_list)

(** val emergencyContainer__F1 :
    emergencyContainer__Type -> lightBarSirenInUse__Type * (causeCode__Type
    option * (emergencyPriority__Type option * unit)) **)

let emergencyContainer__F1 z0 =
  (z0.emergencyContainer__lightBarSirenInUse,
    (z0.emergencyContainer__incidentIndication,
    (z0.emergencyContainer__emergencyPriority, ())))

(** val emergencyContainer__F2 : seq_type -> emergencyContainer__Type **)

let emergencyContainer__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { emergencyContainer__lightBarSirenInUse = i0;
  emergencyContainer__incidentIndication = i1;
  emergencyContainer__emergencyPriority = i2 }

(** val emergencyContainer__Format : emergencyContainer__Type t_Format **)

let emergencyContainer__Format =
  proj2_format emergencyContainer__list__Format
    (Obj.magic emergencyContainer__F1) emergencyContainer__F2

type trafficRule__root__Type =
| TrafficRule__root__noPassing
| TrafficRule__root__noPassingForTrucks
| TrafficRule__root__passToRight
| TrafficRule__root__passToLeft

(** val trafficRule__root__nat__Format : int t_Format **)

let trafficRule__root__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val trafficRule__root__F1 : trafficRule__root__Type -> int **)

let trafficRule__root__F1 = function
| TrafficRule__root__noPassing -> 0
| TrafficRule__root__noPassingForTrucks -> Stdlib.Int.succ 0
| TrafficRule__root__passToRight -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| TrafficRule__root__passToLeft ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val trafficRule__root__F2 : int -> trafficRule__root__Type **)

let trafficRule__root__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> TrafficRule__root__noPassing)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> TrafficRule__root__noPassingForTrucks)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> TrafficRule__root__passToRight)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> TrafficRule__root__passToLeft)
          (fun _ -> TrafficRule__root__noPassing)
          n3)
        n2)
      n1)
    n0

type trafficRule__ext__Type = empty_set

type trafficRule__Type = (trafficRule__root__Type, trafficRule__ext__Type) sum

(** val trafficRule__root__Format : trafficRule__root__Type t_Format **)

let trafficRule__root__Format =
  proj3_format trafficRule__root__nat__Format trafficRule__root__F1
    trafficRule__root__F2

(** val trafficRule__ext__Format : trafficRule__ext__Type t_Format **)

let trafficRule__ext__Format =
  empty_format

(** val trafficRule__Format : trafficRule__Type t_Format **)

let trafficRule__Format =
  sum_format trafficRule__root__Format trafficRule__ext__Format

type speedLimit__Type = int

(** val speedLimit__Format : int t_Format **)

let speedLimit__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type safetyCarContainer__Type = { safetyCarContainer__lightBarSirenInUse : 
                                  lightBarSirenInUse__Type;
                                  safetyCarContainer__incidentIndication : 
                                  causeCode__Type option;
                                  safetyCarContainer__trafficRule : trafficRule__Type
                                                                    option;
                                  safetyCarContainer__speedLimit : speedLimit__Type
                                                                   option }

(** val safetyCarContainer__list : seq_elem list **)

let safetyCarContainer__list =
  Nor :: (Opt :: (Opt :: (Opt :: [])))

type safetyCarContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

(** val safetyCarContainer__Format_list : safetyCarContainer__Format_Type **)

let safetyCarContainer__Format_list =
  ((Obj.magic lightBarSirenInUse__Format), ((Obj.magic causeCode__Format),
    ((Obj.magic trafficRule__Format), ((Obj.magic speedLimit__Format),
    (Obj.magic unit_format)))))

(** val safetyCarContainer__list__Format : seq_type t_Format **)

let safetyCarContainer__list__Format =
  seq_format safetyCarContainer__list
    (Obj.magic safetyCarContainer__Format_list)

(** val safetyCarContainer__F1 :
    safetyCarContainer__Type -> lightBarSirenInUse__Type * (causeCode__Type
    option * (trafficRule__Type option * (speedLimit__Type option * unit))) **)

let safetyCarContainer__F1 z0 =
  (z0.safetyCarContainer__lightBarSirenInUse,
    (z0.safetyCarContainer__incidentIndication,
    (z0.safetyCarContainer__trafficRule, (z0.safetyCarContainer__speedLimit,
    ()))))

(** val safetyCarContainer__F2 : seq_type -> safetyCarContainer__Type **)

let safetyCarContainer__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, _) = p0 in
  { safetyCarContainer__lightBarSirenInUse = i0;
  safetyCarContainer__incidentIndication = i1;
  safetyCarContainer__trafficRule = i2; safetyCarContainer__speedLimit = i3 }

(** val safetyCarContainer__Format : safetyCarContainer__Type t_Format **)

let safetyCarContainer__Format =
  proj2_format safetyCarContainer__list__Format
    (Obj.magic safetyCarContainer__F1) safetyCarContainer__F2

type specialVehicleContainer__root__Type =
| SpecialVehicleContainer__root__publicTransportContainer of publicTransportContainer__Type
| SpecialVehicleContainer__root__specialTransportContainer of specialTransportContainer__Type
| SpecialVehicleContainer__root__dangerousGoodsContainer of dangerousGoodsContainer__Type
| SpecialVehicleContainer__root__roadWorksContainerBasic of roadWorksContainerBasic__Type
| SpecialVehicleContainer__root__rescueContainer of rescueContainer__Type
| SpecialVehicleContainer__root__emergencyContainer of emergencyContainer__Type
| SpecialVehicleContainer__root__safetyCarContainer of safetyCarContainer__Type

type specialVehicleContainer__ext__Type = empty_set

type specialVehicleContainer__Type =
  (specialVehicleContainer__root__Type, specialVehicleContainer__ext__Type) sum

(** val specialVehicleContainer__root__list__Format :
    (int, __) sigT t_Format **)

let specialVehicleContainer__root__list__Format =
  { t_Serial = (fun bf pos c ->
    match restrict_serialize (fun a ->
            le_dec a
              ((-) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ 0))))))) (Stdlib.Int.succ 0)))
            (put_n_nat
              ((+)
                (BigArrayExtr.log2
                  ((-) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ 0))))))) (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ 0))) bf pos (let ExistT (a, _) = c in a) with
    | Some p ->
      let (p0, _) = p in
      let (bf', pos') = p0 in
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         Obj.magic publicTransportContainer__Format.t_Serial bf' pos'
           (let ExistT (_, h) = c in h))
         (fun n0 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           Obj.magic specialTransportContainer__Format.t_Serial bf' pos'
             (let ExistT (_, h) = c in h))
           (fun n1 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ ->
             Obj.magic dangerousGoodsContainer__Format.t_Serial bf' pos'
               (let ExistT (_, h) = c in h))
             (fun n2 ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ ->
               Obj.magic roadWorksContainerBasic__Format.t_Serial bf' pos'
                 (let ExistT (_, h) = c in h))
               (fun n3 ->
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ ->
                 Obj.magic rescueContainer__Format.t_Serial bf' pos'
                   (let ExistT (_, h) = c in h))
                 (fun n4 ->
                 (fun fO fS n -> if n=0 then fO () else fS (n-1))
                   (fun _ ->
                   Obj.magic emergencyContainer__Format.t_Serial bf' pos'
                     (let ExistT (_, h) = c in h))
                   (fun n5 ->
                   (fun fO fS n -> if n=0 then fO () else fS (n-1))
                     (fun _ ->
                     Obj.magic safetyCarContainer__Format.t_Serial bf' pos'
                       (let ExistT (_, h) = c in h))
                     (fun n6 ->
                     (fun fO fS n -> if n=0 then fO () else fS (n-1))
                       (fun _ -> assert false (* absurd case *))
                       (fun _ -> assert false (* absurd case *))
                       n6)
                     n5)
                   n4)
                 n3)
               n2)
             n1)
           n0)
         (let ExistT (a, _) = c in a))
    | None -> None); t_Parse =
    (bind_parse
      (restrict_parse (fun a ->
        le_dec a
          ((-) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0))))))) (Stdlib.Int.succ 0)))
        (read_n_nat
          ((+)
            (BigArrayExtr.log2
              ((-) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ 0))))))) (Stdlib.Int.succ 0)))
            (Stdlib.Int.succ 0)))) (fun n0 _ _ ->
      bind_parse
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           Obj.magic publicTransportContainer__Format.t_Parse)
           (fun n1 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ ->
             Obj.magic specialTransportContainer__Format.t_Parse)
             (fun n2 ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ ->
               Obj.magic dangerousGoodsContainer__Format.t_Parse)
               (fun n3 ->
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ ->
                 Obj.magic roadWorksContainerBasic__Format.t_Parse)
                 (fun n4 ->
                 (fun fO fS n -> if n=0 then fO () else fS (n-1))
                   (fun _ ->
                   Obj.magic rescueContainer__Format.t_Parse)
                   (fun n5 ->
                   (fun fO fS n -> if n=0 then fO () else fS (n-1))
                     (fun _ ->
                     Obj.magic emergencyContainer__Format.t_Parse)
                     (fun n6 ->
                     (fun fO fS n -> if n=0 then fO () else fS (n-1))
                       (fun _ ->
                       Obj.magic safetyCarContainer__Format.t_Parse)
                       (fun n7 _ _ ->
                       (fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> None)
                         (fun _ -> None)
                         n7)
                       n6)
                     n5)
                   n4)
                 n3)
               n2)
             n1)
           n0) (fun v _ flg0 -> return_parse (Exist (ExistT (n0, v))) flg0)));
    t_to_len = (fun c ->
    let ExistT (n0, a) = c in
    if (<=) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         0)))))))
    then add_opt (Some
           ((+)
             (BigArrayExtr.log2
               ((-) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0))))))) (Stdlib.Int.succ 0)))
             (Stdlib.Int.succ 0)))
           ((fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              Obj.magic publicTransportContainer__Format.t_to_len a)
              (fun n1 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                Obj.magic specialTransportContainer__Format.t_to_len a)
                (fun n2 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  Obj.magic dangerousGoodsContainer__Format.t_to_len a)
                  (fun n3 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ ->
                    Obj.magic roadWorksContainerBasic__Format.t_to_len a)
                    (fun n4 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ ->
                      Obj.magic rescueContainer__Format.t_to_len a)
                      (fun n5 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ ->
                        Obj.magic emergencyContainer__Format.t_to_len a)
                        (fun n6 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ ->
                          Obj.magic safetyCarContainer__Format.t_to_len a)
                          (fun n7 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> assert false (* absurd case *))
                            (fun _ -> assert false (* absurd case *))
                            n7)
                          n6)
                        n5)
                      n4)
                    n3)
                  n2)
                n1)
              n0)
    else None) }

(** val specialVehicleContainer__root__F1 :
    specialVehicleContainer__root__Type -> choice **)

let specialVehicleContainer__root__F1 = function
| SpecialVehicleContainer__root__publicTransportContainer t ->
  ExistT (0, (Obj.magic t))
| SpecialVehicleContainer__root__specialTransportContainer t ->
  ExistT ((Stdlib.Int.succ 0), (Obj.magic t))
| SpecialVehicleContainer__root__dangerousGoodsContainer t ->
  ExistT ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (Obj.magic t))
| SpecialVehicleContainer__root__roadWorksContainerBasic t ->
  ExistT ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (Obj.magic t))
| SpecialVehicleContainer__root__rescueContainer t ->
  ExistT ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Obj.magic t))
| SpecialVehicleContainer__root__emergencyContainer t ->
  ExistT ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (Obj.magic t))
| SpecialVehicleContainer__root__safetyCarContainer t ->
  ExistT ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (Obj.magic t))

(** val specialVehicleContainer__root__F2 :
    choice -> specialVehicleContainer__root__Type **)

let specialVehicleContainer__root__F2 = function
| ExistT (x0, t0) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> SpecialVehicleContainer__root__publicTransportContainer
     (Obj.magic t0))
     (fun n0 ->
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> SpecialVehicleContainer__root__specialTransportContainer
       (Obj.magic t0))
       (fun n1 ->
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> SpecialVehicleContainer__root__dangerousGoodsContainer
         (Obj.magic t0))
         (fun n2 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> SpecialVehicleContainer__root__roadWorksContainerBasic
           (Obj.magic t0))
           (fun n3 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> SpecialVehicleContainer__root__rescueContainer
             (Obj.magic t0))
             (fun n4 ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> SpecialVehicleContainer__root__emergencyContainer
               (Obj.magic t0))
               (fun n5 ->
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> SpecialVehicleContainer__root__safetyCarContainer
                 (Obj.magic t0))
                 (fun _ -> assert false (* absurd case *))
                 n5)
               n4)
             n3)
           n2)
         n1)
       n0)
     x0)

(** val specialVehicleContainer__root__Format :
    specialVehicleContainer__root__Type t_Format **)

let specialVehicleContainer__root__Format =
  proj2_format specialVehicleContainer__root__list__Format
    specialVehicleContainer__root__F1 specialVehicleContainer__root__F2

(** val specialVehicleContainer__ext__Format :
    specialVehicleContainer__ext__Type t_Format **)

let specialVehicleContainer__ext__Format =
  empty_format

(** val specialVehicleContainer__Format :
    specialVehicleContainer__Type t_Format **)

let specialVehicleContainer__Format =
  sum_format specialVehicleContainer__root__Format
    specialVehicleContainer__ext__Format

type camParameters__Type = { camParameters__basicContainer : basicContainer__Type;
                             camParameters__highFrequencyContainer : highFrequencyContainer__Type;
                             camParameters__lowFrequencyContainer : lowFrequencyContainer__Type
                                                                    option;
                             camParameters__specialVehicleContainer : 
                             specialVehicleContainer__Type option }

(** val camParameters__root_list : seq_elem list **)

let camParameters__root_list =
  Nor :: (Nor :: (Opt :: (Opt :: [])))

(** val camParameters__ext_list : typ list **)

let camParameters__ext_list =
  []

type camParameters__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

(** val camParameters__root_Format_list : camParameters__root_Format_Type **)

let camParameters__root_Format_list =
  ((Obj.magic basicContainer__Format),
    ((Obj.magic highFrequencyContainer__Format),
    ((Obj.magic lowFrequencyContainer__Format),
    ((Obj.magic specialVehicleContainer__Format), (Obj.magic unit_format)))))

type camParameters__ext_Format_Type = unit t_Format

(** val camParameters__ext_Format_list : camParameters__ext_Format_Type **)

let camParameters__ext_Format_list =
  unit__Format

type camParameters__list_type = seq_type * seq_ext_type

(** val camParameters__list_format : camParameters__list_type t_Format **)

let camParameters__list_format =
  seq_ext_format camParameters__root_list
    (Obj.magic camParameters__root_Format_list) camParameters__ext_list
    (Obj.magic camParameters__ext_Format_list)

(** val camParameters__F1 : camParameters__Type -> camParameters__list_type **)

let camParameters__F1 z0 =
  ((Obj.magic (z0.camParameters__basicContainer,
     (z0.camParameters__highFrequencyContainer,
     (z0.camParameters__lowFrequencyContainer,
     (z0.camParameters__specialVehicleContainer, ()))))), (Obj.magic ()))

(** val camParameters__F2 : camParameters__list_type -> camParameters__Type **)

let camParameters__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, _) = p0 in
  { camParameters__basicContainer = j0;
  camParameters__highFrequencyContainer = j1;
  camParameters__lowFrequencyContainer = j2;
  camParameters__specialVehicleContainer = j3 }

(** val camParameters__Format : camParameters__Type t_Format **)

let camParameters__Format =
  proj2_format camParameters__list_format camParameters__F1 camParameters__F2

type coopAwareness__Type = { coopAwareness__generationDeltaTime : generationDeltaTime__Type;
                             coopAwareness__camParameters : camParameters__Type }

(** val coopAwareness__list : seq_elem list **)

let coopAwareness__list =
  Nor :: (Nor :: [])

type coopAwareness__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val coopAwareness__Format_list : coopAwareness__Format_Type **)

let coopAwareness__Format_list =
  ((Obj.magic generationDeltaTime__Format),
    ((Obj.magic camParameters__Format), (Obj.magic unit_format)))

(** val coopAwareness__list__Format : seq_type t_Format **)

let coopAwareness__list__Format =
  seq_format coopAwareness__list (Obj.magic coopAwareness__Format_list)

(** val coopAwareness__F1 :
    coopAwareness__Type ->
    generationDeltaTime__Type * (camParameters__Type * unit) **)

let coopAwareness__F1 z0 =
  (z0.coopAwareness__generationDeltaTime, (z0.coopAwareness__camParameters,
    ()))

(** val coopAwareness__F2 : seq_type -> coopAwareness__Type **)

let coopAwareness__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { coopAwareness__generationDeltaTime = i0; coopAwareness__camParameters =
  i1 }

(** val coopAwareness__Format : coopAwareness__Type t_Format **)

let coopAwareness__Format =
  proj2_format coopAwareness__list__Format (Obj.magic coopAwareness__F1)
    coopAwareness__F2

type cAM__Type = { cAM__header : itsPduHeader__Type;
                   cAM__cam : coopAwareness__Type }

(** val cAM__list : seq_elem list **)

let cAM__list =
  Nor :: (Nor :: [])

type cAM__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val cAM__Format_list : cAM__Format_Type **)

let cAM__Format_list =
  ((Obj.magic itsPduHeader__Format), ((Obj.magic coopAwareness__Format),
    (Obj.magic unit_format)))

(** val cAM__list__Format : seq_type t_Format **)

let cAM__list__Format =
  seq_format cAM__list (Obj.magic cAM__Format_list)

(** val cAM__F1 :
    cAM__Type -> itsPduHeader__Type * (coopAwareness__Type * unit) **)

let cAM__F1 z0 =
  (z0.cAM__header, (z0.cAM__cam, ()))

(** val cAM__F2 : seq_type -> cAM__Type **)

let cAM__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in { cAM__header = i0; cAM__cam = i1 }

(** val cAM__Format : cAM__Type t_Format **)

let cAM__Format =
  proj2_format cAM__list__Format (Obj.magic cAM__F1) cAM__F2

type sequenceNumber__Type = int

(** val sequenceNumber__Format : int t_Format **)

let sequenceNumber__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    1)))))))))))))))

type actionID__Type = { actionID__originatingStationID : stationID__Type;
                        actionID__sequenceNumber : sequenceNumber__Type }

(** val actionID__list : seq_elem list **)

let actionID__list =
  Nor :: (Nor :: [])

type actionID__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val actionID__Format_list : actionID__Format_Type **)

let actionID__Format_list =
  ((Obj.magic stationID__Format), ((Obj.magic sequenceNumber__Format),
    (Obj.magic unit_format)))

(** val actionID__list__Format : seq_type t_Format **)

let actionID__list__Format =
  seq_format actionID__list (Obj.magic actionID__Format_list)

(** val actionID__F1 :
    actionID__Type -> stationID__Type * (sequenceNumber__Type * unit) **)

let actionID__F1 z0 =
  (z0.actionID__originatingStationID, (z0.actionID__sequenceNumber, ()))

(** val actionID__F2 : seq_type -> actionID__Type **)

let actionID__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in
  { actionID__originatingStationID = i0; actionID__sequenceNumber = i1 }

(** val actionID__Format : actionID__Type t_Format **)

let actionID__Format =
  proj2_format actionID__list__Format (Obj.magic actionID__F1) actionID__F2

type termination__Type =
| Termination__isCancellation
| Termination__isNegation

(** val termination__nat__Format : int t_Format **)

let termination__nat__Format =
  nat_enum_format (Stdlib.Int.succ 0)

(** val termination__F1 : termination__Type -> int **)

let termination__F1 = function
| Termination__isCancellation -> 0
| Termination__isNegation -> Stdlib.Int.succ 0

(** val termination__F2 : int -> termination__Type **)

let termination__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Termination__isCancellation)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Termination__isNegation)
      (fun _ -> Termination__isCancellation)
      n1)
    n0

(** val termination__Format : termination__Type t_Format **)

let termination__Format =
  proj3_format termination__nat__Format termination__F1 termination__F2

type relevanceDistance__Type =
| RelevanceDistance__lessThan50m
| RelevanceDistance__lessThan100m
| RelevanceDistance__lessThan200m
| RelevanceDistance__lessThan500m
| RelevanceDistance__lessThan1000m
| RelevanceDistance__lessThan5km
| RelevanceDistance__lessThan10km
| RelevanceDistance__over10km

(** val relevanceDistance__nat__Format : int t_Format **)

let relevanceDistance__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val relevanceDistance__F1 : relevanceDistance__Type -> int **)

let relevanceDistance__F1 = function
| RelevanceDistance__lessThan50m -> 0
| RelevanceDistance__lessThan100m -> Stdlib.Int.succ 0
| RelevanceDistance__lessThan200m -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| RelevanceDistance__lessThan500m ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| RelevanceDistance__lessThan1000m ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| RelevanceDistance__lessThan5km ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
| RelevanceDistance__lessThan10km ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
| RelevanceDistance__over10km ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val relevanceDistance__F2 : int -> relevanceDistance__Type **)

let relevanceDistance__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> RelevanceDistance__lessThan50m)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> RelevanceDistance__lessThan100m)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> RelevanceDistance__lessThan200m)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> RelevanceDistance__lessThan500m)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> RelevanceDistance__lessThan1000m)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> RelevanceDistance__lessThan5km)
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> RelevanceDistance__lessThan10km)
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> RelevanceDistance__over10km)
                  (fun _ -> RelevanceDistance__lessThan50m)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val relevanceDistance__Format : relevanceDistance__Type t_Format **)

let relevanceDistance__Format =
  proj3_format relevanceDistance__nat__Format relevanceDistance__F1
    relevanceDistance__F2

type relevanceTrafficDirection__Type =
| RelevanceTrafficDirection__allTrafficDirections
| RelevanceTrafficDirection__upstreamTraffic
| RelevanceTrafficDirection__downstreamTraffic
| RelevanceTrafficDirection__oppositeTraffic

(** val relevanceTrafficDirection__nat__Format : int t_Format **)

let relevanceTrafficDirection__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val relevanceTrafficDirection__F1 :
    relevanceTrafficDirection__Type -> int **)

let relevanceTrafficDirection__F1 = function
| RelevanceTrafficDirection__allTrafficDirections -> 0
| RelevanceTrafficDirection__upstreamTraffic -> Stdlib.Int.succ 0
| RelevanceTrafficDirection__downstreamTraffic ->
  Stdlib.Int.succ (Stdlib.Int.succ 0)
| RelevanceTrafficDirection__oppositeTraffic ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val relevanceTrafficDirection__F2 :
    int -> relevanceTrafficDirection__Type **)

let relevanceTrafficDirection__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> RelevanceTrafficDirection__allTrafficDirections)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> RelevanceTrafficDirection__upstreamTraffic)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> RelevanceTrafficDirection__downstreamTraffic)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> RelevanceTrafficDirection__oppositeTraffic)
          (fun _ -> RelevanceTrafficDirection__allTrafficDirections)
          n3)
        n2)
      n1)
    n0

(** val relevanceTrafficDirection__Format :
    relevanceTrafficDirection__Type t_Format **)

let relevanceTrafficDirection__Format =
  proj3_format relevanceTrafficDirection__nat__Format
    relevanceTrafficDirection__F1 relevanceTrafficDirection__F2

type validityDuration__Type = int

(** val validityDuration__Format : int t_Format **)

let validityDuration__Format =
  ranged_int_format 0 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1))))))))))))))))

type transmissionInterval__Type = int

(** val transmissionInterval__Format : int t_Format **)

let transmissionInterval__Format =
  ranged_int_format 1 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))))))

type managementContainer__Type = { managementContainer__actionID : actionID__Type;
                                   managementContainer__detectionTime : 
                                   timestampIts__Type;
                                   managementContainer__referenceTime : 
                                   timestampIts__Type;
                                   managementContainer__termination : 
                                   termination__Type option;
                                   managementContainer__eventPosition : 
                                   referencePosition__Type;
                                   managementContainer__relevanceDistance : 
                                   relevanceDistance__Type option;
                                   managementContainer__relevanceTrafficDirection : 
                                   relevanceTrafficDirection__Type option;
                                   managementContainer__validityDuration : 
                                   validityDuration__Type;
                                   managementContainer__transmissionInterval : 
                                   transmissionInterval__Type option;
                                   managementContainer__stationType : 
                                   stationType__Type }

(** val managementContainer__root_list : seq_elem list **)

let managementContainer__root_list =
  Nor :: (Nor :: (Nor :: (Opt :: (Nor :: (Opt :: (Opt :: ((Dft
    ((Obj.magic ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) 1)))))))))),
    (Obj.magic (=)))) :: (Opt :: (Nor :: [])))))))))

(** val managementContainer__ext_list : typ list **)

let managementContainer__ext_list =
  []

type managementContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))

(** val managementContainer__root_Format_list :
    managementContainer__root_Format_Type **)

let managementContainer__root_Format_list =
  ((Obj.magic actionID__Format), ((Obj.magic timestampIts__Format),
    ((Obj.magic timestampIts__Format), ((Obj.magic termination__Format),
    ((Obj.magic referencePosition__Format),
    ((Obj.magic relevanceDistance__Format),
    ((Obj.magic relevanceTrafficDirection__Format),
    ((Obj.magic validityDuration__Format),
    ((Obj.magic transmissionInterval__Format),
    ((Obj.magic stationType__Format), (Obj.magic unit_format)))))))))))

type managementContainer__ext_Format_Type = unit t_Format

(** val managementContainer__ext_Format_list :
    managementContainer__ext_Format_Type **)

let managementContainer__ext_Format_list =
  unit__Format

type managementContainer__list_type = seq_type * seq_ext_type

(** val managementContainer__list_format :
    managementContainer__list_type t_Format **)

let managementContainer__list_format =
  seq_ext_format managementContainer__root_list
    (Obj.magic managementContainer__root_Format_list)
    managementContainer__ext_list
    (Obj.magic managementContainer__ext_Format_list)

(** val managementContainer__F1 :
    managementContainer__Type -> managementContainer__list_type **)

let managementContainer__F1 z0 =
  ((Obj.magic (z0.managementContainer__actionID,
     (z0.managementContainer__detectionTime,
     (z0.managementContainer__referenceTime,
     (z0.managementContainer__termination,
     (z0.managementContainer__eventPosition,
     (z0.managementContainer__relevanceDistance,
     (z0.managementContainer__relevanceTrafficDirection,
     (z0.managementContainer__validityDuration,
     (z0.managementContainer__transmissionInterval,
     (z0.managementContainer__stationType, ()))))))))))), (Obj.magic ()))

(** val managementContainer__F2 :
    managementContainer__list_type -> managementContainer__Type **)

let managementContainer__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, p1) = p0 in
  let (j4, p2) = p1 in
  let (j5, p3) = p2 in
  let (j6, p4) = p3 in
  let (j7, p5) = p4 in
  let (j8, p6) = p5 in
  let (j9, _) = p6 in
  { managementContainer__actionID = j0; managementContainer__detectionTime =
  j1; managementContainer__referenceTime = j2;
  managementContainer__termination = j3; managementContainer__eventPosition =
  j4; managementContainer__relevanceDistance = j5;
  managementContainer__relevanceTrafficDirection = j6;
  managementContainer__validityDuration = j7;
  managementContainer__transmissionInterval = j8;
  managementContainer__stationType = j9 }

(** val managementContainer__Format : managementContainer__Type t_Format **)

let managementContainer__Format =
  proj2_format managementContainer__list_format managementContainer__F1
    managementContainer__F2

type informationQuality__Type = int

(** val informationQuality__Format : int t_Format **)

let informationQuality__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) 1))

type eventPoint__Type = { eventPoint__eventPosition : deltaReferencePosition__Type;
                          eventPoint__eventDeltaTime : pathDeltaTime__Type
                                                       option;
                          eventPoint__informationQuality : informationQuality__Type }

(** val eventPoint__list : seq_elem list **)

let eventPoint__list =
  Nor :: (Opt :: (Nor :: []))

type eventPoint__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

(** val eventPoint__Format_list : eventPoint__Format_Type **)

let eventPoint__Format_list =
  ((Obj.magic deltaReferencePosition__Format),
    ((Obj.magic pathDeltaTime__Format),
    ((Obj.magic informationQuality__Format), (Obj.magic unit_format))))

(** val eventPoint__list__Format : seq_type t_Format **)

let eventPoint__list__Format =
  seq_format eventPoint__list (Obj.magic eventPoint__Format_list)

(** val eventPoint__F1 :
    eventPoint__Type -> deltaReferencePosition__Type * (pathDeltaTime__Type
    option * (informationQuality__Type * unit)) **)

let eventPoint__F1 z0 =
  (z0.eventPoint__eventPosition, (z0.eventPoint__eventDeltaTime,
    (z0.eventPoint__informationQuality, ())))

(** val eventPoint__F2 : seq_type -> eventPoint__Type **)

let eventPoint__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, _) = p in
  { eventPoint__eventPosition = i0; eventPoint__eventDeltaTime = i1;
  eventPoint__informationQuality = i2 }

(** val eventPoint__Format : eventPoint__Type t_Format **)

let eventPoint__Format =
  proj2_format eventPoint__list__Format (Obj.magic eventPoint__F1)
    eventPoint__F2

type eventHistory__Type = eventPoint__Type list

(** val eventHistory__Format : eventHistory__Type t_Format **)

let eventHistory__Format =
  seq_of_format eventPoint__Format 1 ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1))))

type situationContainer__Type = { situationContainer__informationQuality : 
                                  informationQuality__Type;
                                  situationContainer__eventType : causeCode__Type;
                                  situationContainer__linkedCause : causeCode__Type
                                                                    option;
                                  situationContainer__eventHistory : eventHistory__Type
                                                                     option }

(** val situationContainer__root_list : seq_elem list **)

let situationContainer__root_list =
  Nor :: (Nor :: (Opt :: (Opt :: [])))

(** val situationContainer__ext_list : typ list **)

let situationContainer__ext_list =
  []

type situationContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

(** val situationContainer__root_Format_list :
    situationContainer__root_Format_Type **)

let situationContainer__root_Format_list =
  ((Obj.magic informationQuality__Format), ((Obj.magic causeCode__Format),
    ((Obj.magic causeCode__Format), ((Obj.magic eventHistory__Format),
    (Obj.magic unit_format)))))

type situationContainer__ext_Format_Type = unit t_Format

(** val situationContainer__ext_Format_list :
    situationContainer__ext_Format_Type **)

let situationContainer__ext_Format_list =
  unit__Format

type situationContainer__list_type = seq_type * seq_ext_type

(** val situationContainer__list_format :
    situationContainer__list_type t_Format **)

let situationContainer__list_format =
  seq_ext_format situationContainer__root_list
    (Obj.magic situationContainer__root_Format_list)
    situationContainer__ext_list
    (Obj.magic situationContainer__ext_Format_list)

(** val situationContainer__F1 :
    situationContainer__Type -> situationContainer__list_type **)

let situationContainer__F1 z0 =
  ((Obj.magic (z0.situationContainer__informationQuality,
     (z0.situationContainer__eventType, (z0.situationContainer__linkedCause,
     (z0.situationContainer__eventHistory, ()))))), (Obj.magic ()))

(** val situationContainer__F2 :
    situationContainer__list_type -> situationContainer__Type **)

let situationContainer__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, _) = p0 in
  { situationContainer__informationQuality = j0;
  situationContainer__eventType = j1; situationContainer__linkedCause = j2;
  situationContainer__eventHistory = j3 }

(** val situationContainer__Format : situationContainer__Type t_Format **)

let situationContainer__Format =
  proj2_format situationContainer__list_format situationContainer__F1
    situationContainer__F2

type traces__Type = pathHistory__Type list

(** val traces__Format : traces__Type t_Format **)

let traces__Format =
  seq_of_format pathHistory__Format 1 ((fun p->1+2*p) ((fun p->1+2*p) 1))

type roadType__Type =
| RoadType__urban_NoStructuralSeparationToOppositeLanes
| RoadType__urban_WithStructuralSeparationToOppositeLanes
| RoadType__nonUrban_NoStructuralSeparationToOppositeLanes
| RoadType__nonUrban_WithStructuralSeparationToOppositeLanes

(** val roadType__nat__Format : int t_Format **)

let roadType__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val roadType__F1 : roadType__Type -> int **)

let roadType__F1 = function
| RoadType__urban_NoStructuralSeparationToOppositeLanes -> 0
| RoadType__urban_WithStructuralSeparationToOppositeLanes -> Stdlib.Int.succ 0
| RoadType__nonUrban_NoStructuralSeparationToOppositeLanes ->
  Stdlib.Int.succ (Stdlib.Int.succ 0)
| RoadType__nonUrban_WithStructuralSeparationToOppositeLanes ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val roadType__F2 : int -> roadType__Type **)

let roadType__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> RoadType__urban_NoStructuralSeparationToOppositeLanes)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      RoadType__urban_WithStructuralSeparationToOppositeLanes)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        RoadType__nonUrban_NoStructuralSeparationToOppositeLanes)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          RoadType__nonUrban_WithStructuralSeparationToOppositeLanes)
          (fun _ -> RoadType__urban_NoStructuralSeparationToOppositeLanes)
          n3)
        n2)
      n1)
    n0

(** val roadType__Format : roadType__Type t_Format **)

let roadType__Format =
  proj3_format roadType__nat__Format roadType__F1 roadType__F2

type locationContainer__Type = { locationContainer__eventSpeed : speed__Type
                                                                 option;
                                 locationContainer__eventPositionHeading : 
                                 heading__Type option;
                                 locationContainer__traces : traces__Type;
                                 locationContainer__roadType : roadType__Type
                                                               option }

(** val locationContainer__root_list : seq_elem list **)

let locationContainer__root_list =
  Opt :: (Opt :: (Nor :: (Opt :: [])))

(** val locationContainer__ext_list : typ list **)

let locationContainer__ext_list =
  []

type locationContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

(** val locationContainer__root_Format_list :
    locationContainer__root_Format_Type **)

let locationContainer__root_Format_list =
  ((Obj.magic speed__Format), ((Obj.magic heading__Format),
    ((Obj.magic traces__Format), ((Obj.magic roadType__Format),
    (Obj.magic unit_format)))))

type locationContainer__ext_Format_Type = unit t_Format

(** val locationContainer__ext_Format_list :
    locationContainer__ext_Format_Type **)

let locationContainer__ext_Format_list =
  unit__Format

type locationContainer__list_type = seq_type * seq_ext_type

(** val locationContainer__list_format :
    locationContainer__list_type t_Format **)

let locationContainer__list_format =
  seq_ext_format locationContainer__root_list
    (Obj.magic locationContainer__root_Format_list)
    locationContainer__ext_list (Obj.magic locationContainer__ext_Format_list)

(** val locationContainer__F1 :
    locationContainer__Type -> locationContainer__list_type **)

let locationContainer__F1 z0 =
  ((Obj.magic (z0.locationContainer__eventSpeed,
     (z0.locationContainer__eventPositionHeading,
     (z0.locationContainer__traces, (z0.locationContainer__roadType, ()))))),
    (Obj.magic ()))

(** val locationContainer__F2 :
    locationContainer__list_type -> locationContainer__Type **)

let locationContainer__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, _) = p0 in
  { locationContainer__eventSpeed = j0;
  locationContainer__eventPositionHeading = j1; locationContainer__traces =
  j2; locationContainer__roadType = j3 }

(** val locationContainer__Format : locationContainer__Type t_Format **)

let locationContainer__Format =
  proj2_format locationContainer__list_format locationContainer__F1
    locationContainer__F2

type heightLonCarr__Type = int

(** val heightLonCarr__Format : int t_Format **)

let heightLonCarr__Format =
  ranged_int_format 1 ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))

type posLonCarr__Type = int

(** val posLonCarr__Format : int t_Format **)

let posLonCarr__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

type posPillar__Type = int

(** val posPillar__Format : int t_Format **)

let posPillar__Format =
  ranged_int_format 1 ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1))))

type positionOfPillars__Type = posPillar__Type list

(** val positionOfPillars__Format : positionOfPillars__Type t_Format **)

let positionOfPillars__Format =
  seq_of_ext_format posPillar__Format (Stdlib.Int.succ 0) (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))

type posCentMass__Type = int

(** val posCentMass__Format : int t_Format **)

let posCentMass__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))

type wheelBaseVehicle__Type = int

(** val wheelBaseVehicle__Format : int t_Format **)

let wheelBaseVehicle__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

type turningRadius__Type = int

(** val turningRadius__Format : int t_Format **)

let turningRadius__Format =
  ranged_int_format 1 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type posFrontAx__Type = int

(** val posFrontAx__Format : int t_Format **)

let posFrontAx__Format =
  ranged_int_format 1 ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1))))

type positionOfOccupants__Type = bit_string_fixed

(** val positionOfOccupants__Format : positionOfOccupants__Type t_Format **)

let positionOfOccupants__Format =
  bit_string_fixed_format ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1))))

type vehicleMass__Type = int

(** val vehicleMass__Format : int t_Format **)

let vehicleMass__Format =
  ranged_int_format 1 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1))))))))))

type requestResponseIndication__Type =
| RequestResponseIndication__request
| RequestResponseIndication__response

(** val requestResponseIndication__nat__Format : int t_Format **)

let requestResponseIndication__nat__Format =
  nat_enum_format (Stdlib.Int.succ 0)

(** val requestResponseIndication__F1 :
    requestResponseIndication__Type -> int **)

let requestResponseIndication__F1 = function
| RequestResponseIndication__request -> 0
| RequestResponseIndication__response -> Stdlib.Int.succ 0

(** val requestResponseIndication__F2 :
    int -> requestResponseIndication__Type **)

let requestResponseIndication__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> RequestResponseIndication__request)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> RequestResponseIndication__response)
      (fun _ -> RequestResponseIndication__request)
      n1)
    n0

(** val requestResponseIndication__Format :
    requestResponseIndication__Type t_Format **)

let requestResponseIndication__Format =
  proj3_format requestResponseIndication__nat__Format
    requestResponseIndication__F1 requestResponseIndication__F2

type impactReductionContainer__Type = { impactReductionContainer__heightLonCarrLeft : 
                                        heightLonCarr__Type;
                                        impactReductionContainer__heightLonCarrRight : 
                                        heightLonCarr__Type;
                                        impactReductionContainer__posLonCarrLeft : 
                                        posLonCarr__Type;
                                        impactReductionContainer__posLonCarrRight : 
                                        posLonCarr__Type;
                                        impactReductionContainer__positionOfPillars : 
                                        positionOfPillars__Type;
                                        impactReductionContainer__posCentMass : 
                                        posCentMass__Type;
                                        impactReductionContainer__wheelBaseVehicle : 
                                        wheelBaseVehicle__Type;
                                        impactReductionContainer__turningRadius : 
                                        turningRadius__Type;
                                        impactReductionContainer__posFrontAx : 
                                        posFrontAx__Type;
                                        impactReductionContainer__positionOfOccupants : 
                                        positionOfOccupants__Type;
                                        impactReductionContainer__vehicleMass : 
                                        vehicleMass__Type;
                                        impactReductionContainer__requestResponseIndication : 
                                        requestResponseIndication__Type }

(** val impactReductionContainer__list : seq_elem list **)

let impactReductionContainer__list =
  Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Nor :: [])))))))))))

type impactReductionContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))))

(** val impactReductionContainer__Format_list :
    impactReductionContainer__Format_Type **)

let impactReductionContainer__Format_list =
  ((Obj.magic heightLonCarr__Format), ((Obj.magic heightLonCarr__Format),
    ((Obj.magic posLonCarr__Format), ((Obj.magic posLonCarr__Format),
    ((Obj.magic positionOfPillars__Format), ((Obj.magic posCentMass__Format),
    ((Obj.magic wheelBaseVehicle__Format), ((Obj.magic turningRadius__Format),
    ((Obj.magic posFrontAx__Format), ((Obj.magic positionOfOccupants__Format),
    ((Obj.magic vehicleMass__Format),
    ((Obj.magic requestResponseIndication__Format),
    (Obj.magic unit_format)))))))))))))

(** val impactReductionContainer__list__Format : seq_type t_Format **)

let impactReductionContainer__list__Format =
  seq_format impactReductionContainer__list
    (Obj.magic impactReductionContainer__Format_list)

(** val impactReductionContainer__F1 :
    impactReductionContainer__Type ->
    heightLonCarr__Type * (heightLonCarr__Type * (posLonCarr__Type * (posLonCarr__Type * (positionOfPillars__Type * (posCentMass__Type * (wheelBaseVehicle__Type * (turningRadius__Type * (posFrontAx__Type * (positionOfOccupants__Type * (vehicleMass__Type * (requestResponseIndication__Type * unit))))))))))) **)

let impactReductionContainer__F1 z0 =
  (z0.impactReductionContainer__heightLonCarrLeft,
    (z0.impactReductionContainer__heightLonCarrRight,
    (z0.impactReductionContainer__posLonCarrLeft,
    (z0.impactReductionContainer__posLonCarrRight,
    (z0.impactReductionContainer__positionOfPillars,
    (z0.impactReductionContainer__posCentMass,
    (z0.impactReductionContainer__wheelBaseVehicle,
    (z0.impactReductionContainer__turningRadius,
    (z0.impactReductionContainer__posFrontAx,
    (z0.impactReductionContainer__positionOfOccupants,
    (z0.impactReductionContainer__vehicleMass,
    (z0.impactReductionContainer__requestResponseIndication, ()))))))))))))

(** val impactReductionContainer__F2 :
    seq_type -> impactReductionContainer__Type **)

let impactReductionContainer__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, p1) = p0 in
  let (i4, p2) = p1 in
  let (i5, p3) = p2 in
  let (i6, p4) = p3 in
  let (i7, p5) = p4 in
  let (i8, p6) = p5 in
  let (i9, p7) = p6 in
  let (i10, p8) = p7 in
  let (i11, _) = p8 in
  { impactReductionContainer__heightLonCarrLeft = i0;
  impactReductionContainer__heightLonCarrRight = i1;
  impactReductionContainer__posLonCarrLeft = i2;
  impactReductionContainer__posLonCarrRight = i3;
  impactReductionContainer__positionOfPillars = i4;
  impactReductionContainer__posCentMass = i5;
  impactReductionContainer__wheelBaseVehicle = i6;
  impactReductionContainer__turningRadius = i7;
  impactReductionContainer__posFrontAx = i8;
  impactReductionContainer__positionOfOccupants = i9;
  impactReductionContainer__vehicleMass = i10;
  impactReductionContainer__requestResponseIndication = i11 }

(** val impactReductionContainer__Format :
    impactReductionContainer__Type t_Format **)

let impactReductionContainer__Format =
  proj2_format impactReductionContainer__list__Format
    (Obj.magic impactReductionContainer__F1) impactReductionContainer__F2

type temperature__Type = int

(** val temperature__Format : int t_Format **)

let temperature__Format =
  ranged_int_format ((~-) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))

type restrictedTypes__Type = stationType__Type list

(** val restrictedTypes__Format : restrictedTypes__Type t_Format **)

let restrictedTypes__Format =
  seq_of_ext_format stationType__Format (Stdlib.Int.succ 0) (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))

type itineraryPath__Type = referencePosition__Type list

(** val itineraryPath__Format : itineraryPath__Type t_Format **)

let itineraryPath__Format =
  seq_of_format referencePosition__Format 1 ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))

type referenceDenms__Type = actionID__Type list

(** val referenceDenms__Format : referenceDenms__Type t_Format **)

let referenceDenms__Format =
  seq_of_ext_format actionID__Format (Stdlib.Int.succ 0) (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))

type roadWorksContainerExtended__Type = { roadWorksContainerExtended__lightBarSirenInUse : 
                                          lightBarSirenInUse__Type option;
                                          roadWorksContainerExtended__closedLanes : 
                                          closedLanes__Type option;
                                          roadWorksContainerExtended__restriction : 
                                          restrictedTypes__Type option;
                                          roadWorksContainerExtended__speedLimit : 
                                          speedLimit__Type option;
                                          roadWorksContainerExtended__incidentIndication : 
                                          causeCode__Type option;
                                          roadWorksContainerExtended__recommendedPath : 
                                          itineraryPath__Type option;
                                          roadWorksContainerExtended__startingPointSpeedLimit : 
                                          deltaReferencePosition__Type option;
                                          roadWorksContainerExtended__trafficFlowRule : 
                                          trafficRule__Type option;
                                          roadWorksContainerExtended__referenceDenms : 
                                          referenceDenms__Type option }

(** val roadWorksContainerExtended__list : seq_elem list **)

let roadWorksContainerExtended__list =
  Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: []))))))))

type roadWorksContainerExtended__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))

(** val roadWorksContainerExtended__Format_list :
    roadWorksContainerExtended__Format_Type **)

let roadWorksContainerExtended__Format_list =
  ((Obj.magic lightBarSirenInUse__Format), ((Obj.magic closedLanes__Format),
    ((Obj.magic restrictedTypes__Format), ((Obj.magic speedLimit__Format),
    ((Obj.magic causeCode__Format), ((Obj.magic itineraryPath__Format),
    ((Obj.magic deltaReferencePosition__Format),
    ((Obj.magic trafficRule__Format), ((Obj.magic referenceDenms__Format),
    (Obj.magic unit_format))))))))))

(** val roadWorksContainerExtended__list__Format : seq_type t_Format **)

let roadWorksContainerExtended__list__Format =
  seq_format roadWorksContainerExtended__list
    (Obj.magic roadWorksContainerExtended__Format_list)

(** val roadWorksContainerExtended__F1 :
    roadWorksContainerExtended__Type -> lightBarSirenInUse__Type
    option * (closedLanes__Type option * (restrictedTypes__Type
    option * (speedLimit__Type option * (causeCode__Type
    option * (itineraryPath__Type option * (deltaReferencePosition__Type
    option * (trafficRule__Type option * (referenceDenms__Type
    option * unit)))))))) **)

let roadWorksContainerExtended__F1 z0 =
  (z0.roadWorksContainerExtended__lightBarSirenInUse,
    (z0.roadWorksContainerExtended__closedLanes,
    (z0.roadWorksContainerExtended__restriction,
    (z0.roadWorksContainerExtended__speedLimit,
    (z0.roadWorksContainerExtended__incidentIndication,
    (z0.roadWorksContainerExtended__recommendedPath,
    (z0.roadWorksContainerExtended__startingPointSpeedLimit,
    (z0.roadWorksContainerExtended__trafficFlowRule,
    (z0.roadWorksContainerExtended__referenceDenms, ())))))))))

(** val roadWorksContainerExtended__F2 :
    seq_type -> roadWorksContainerExtended__Type **)

let roadWorksContainerExtended__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, p1) = p0 in
  let (i4, p2) = p1 in
  let (i5, p3) = p2 in
  let (i6, p4) = p3 in
  let (i7, p5) = p4 in
  let (i8, _) = p5 in
  { roadWorksContainerExtended__lightBarSirenInUse = i0;
  roadWorksContainerExtended__closedLanes = i1;
  roadWorksContainerExtended__restriction = i2;
  roadWorksContainerExtended__speedLimit = i3;
  roadWorksContainerExtended__incidentIndication = i4;
  roadWorksContainerExtended__recommendedPath = i5;
  roadWorksContainerExtended__startingPointSpeedLimit = i6;
  roadWorksContainerExtended__trafficFlowRule = i7;
  roadWorksContainerExtended__referenceDenms = i8 }

(** val roadWorksContainerExtended__Format :
    roadWorksContainerExtended__Type t_Format **)

let roadWorksContainerExtended__Format =
  proj2_format roadWorksContainerExtended__list__Format
    (Obj.magic roadWorksContainerExtended__F1) roadWorksContainerExtended__F2

type positioningSolutionType__root__Type =
| PositioningSolutionType__root__noPositioningSolution
| PositioningSolutionType__root__sGNSS
| PositioningSolutionType__root__dGNSS
| PositioningSolutionType__root__sGNSSplusDR
| PositioningSolutionType__root__dGNSSplusDR
| PositioningSolutionType__root__dR

(** val positioningSolutionType__root__nat__Format : int t_Format **)

let positioningSolutionType__root__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val positioningSolutionType__root__F1 :
    positioningSolutionType__root__Type -> int **)

let positioningSolutionType__root__F1 = function
| PositioningSolutionType__root__noPositioningSolution -> 0
| PositioningSolutionType__root__sGNSS -> Stdlib.Int.succ 0
| PositioningSolutionType__root__dGNSS -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PositioningSolutionType__root__sGNSSplusDR ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| PositioningSolutionType__root__dGNSSplusDR ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| PositioningSolutionType__root__dR ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))

(** val positioningSolutionType__root__F2 :
    int -> positioningSolutionType__root__Type **)

let positioningSolutionType__root__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> PositioningSolutionType__root__noPositioningSolution)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> PositioningSolutionType__root__sGNSS)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> PositioningSolutionType__root__dGNSS)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> PositioningSolutionType__root__sGNSSplusDR)
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> PositioningSolutionType__root__dGNSSplusDR)
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> PositioningSolutionType__root__dR)
              (fun _ -> PositioningSolutionType__root__noPositioningSolution)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

type positioningSolutionType__ext__Type = empty_set

type positioningSolutionType__Type =
  (positioningSolutionType__root__Type, positioningSolutionType__ext__Type) sum

(** val positioningSolutionType__root__Format :
    positioningSolutionType__root__Type t_Format **)

let positioningSolutionType__root__Format =
  proj3_format positioningSolutionType__root__nat__Format
    positioningSolutionType__root__F1 positioningSolutionType__root__F2

(** val positioningSolutionType__ext__Format :
    positioningSolutionType__ext__Type t_Format **)

let positioningSolutionType__ext__Format =
  empty_format

(** val positioningSolutionType__Format :
    positioningSolutionType__Type t_Format **)

let positioningSolutionType__Format =
  sum_format positioningSolutionType__root__Format
    positioningSolutionType__ext__Format

type stationarySince__Type =
| StationarySince__lessThan1Minute
| StationarySince__lessThan2Minutes
| StationarySince__lessThan15Minutes
| StationarySince__equalOrGreater15Minutes

(** val stationarySince__nat__Format : int t_Format **)

let stationarySince__nat__Format =
  nat_enum_format (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val stationarySince__F1 : stationarySince__Type -> int **)

let stationarySince__F1 = function
| StationarySince__lessThan1Minute -> 0
| StationarySince__lessThan2Minutes -> Stdlib.Int.succ 0
| StationarySince__lessThan15Minutes -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| StationarySince__equalOrGreater15Minutes ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val stationarySince__F2 : int -> stationarySince__Type **)

let stationarySince__F2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> StationarySince__lessThan1Minute)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> StationarySince__lessThan2Minutes)
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> StationarySince__lessThan15Minutes)
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> StationarySince__equalOrGreater15Minutes)
          (fun _ -> StationarySince__lessThan1Minute)
          n3)
        n2)
      n1)
    n0

(** val stationarySince__Format : stationarySince__Type t_Format **)

let stationarySince__Format =
  proj3_format stationarySince__nat__Format stationarySince__F1
    stationarySince__F2

type phoneNumber__Type = char list

(** val phoneNumber__Format : phoneNumber__Type t_Format **)

let phoneNumber__Format =
  seq_of_format numeric_string__Format 1 ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) 1))))

type dangerousGoodsExtended__emergencyActionCode__Type = char list

type dangerousGoodsExtended__Type = { dangerousGoodsExtended__dangerousGoodsType : 
                                      dangerousGoodsBasic__Type;
                                      dangerousGoodsExtended__unNumber : 
                                      int;
                                      dangerousGoodsExtended__elevatedTemperature : 
                                      bool;
                                      dangerousGoodsExtended__tunnelsRestricted : 
                                      bool;
                                      dangerousGoodsExtended__limitedQuantity : 
                                      bool;
                                      dangerousGoodsExtended__emergencyActionCode : 
                                      dangerousGoodsExtended__emergencyActionCode__Type
                                      option;
                                      dangerousGoodsExtended__phoneNumber : 
                                      phoneNumber__Type option;
                                      dangerousGoodsExtended__companyName : 
                                      string option }

(** val dangerousGoodsExtended__root_list : seq_elem list **)

let dangerousGoodsExtended__root_list =
  Nor :: (Nor :: (Nor :: (Nor :: (Nor :: (Opt :: (Opt :: (Opt :: [])))))))

(** val dangerousGoodsExtended__ext_list : typ list **)

let dangerousGoodsExtended__ext_list =
  []

(** val dangerousGoodsExtended__unNumber__Format : int t_Format **)

let dangerousGoodsExtended__unNumber__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) 1)))))))))))))

(** val dangerousGoodsExtended__emergencyActionCode__Format :
    dangerousGoodsExtended__emergencyActionCode__Type t_Format **)

let dangerousGoodsExtended__emergencyActionCode__Format =
  seq_of_format ia5_string__Format 1 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1))))

type dangerousGoodsExtended__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))

(** val dangerousGoodsExtended__root_Format_list :
    dangerousGoodsExtended__root_Format_Type **)

let dangerousGoodsExtended__root_Format_list =
  ((Obj.magic dangerousGoodsBasic__Format),
    ((Obj.magic dangerousGoodsExtended__unNumber__Format),
    ((Obj.magic bool__Format), ((Obj.magic bool__Format),
    ((Obj.magic bool__Format),
    ((Obj.magic dangerousGoodsExtended__emergencyActionCode__Format),
    ((Obj.magic phoneNumber__Format), ((Obj.magic utf8_string__Format),
    (Obj.magic unit_format)))))))))

type dangerousGoodsExtended__ext_Format_Type = unit t_Format

(** val dangerousGoodsExtended__ext_Format_list :
    dangerousGoodsExtended__ext_Format_Type **)

let dangerousGoodsExtended__ext_Format_list =
  unit__Format

type dangerousGoodsExtended__list_type = seq_type * seq_ext_type

(** val dangerousGoodsExtended__list_format :
    dangerousGoodsExtended__list_type t_Format **)

let dangerousGoodsExtended__list_format =
  seq_ext_format dangerousGoodsExtended__root_list
    (Obj.magic dangerousGoodsExtended__root_Format_list)
    dangerousGoodsExtended__ext_list
    (Obj.magic dangerousGoodsExtended__ext_Format_list)

(** val dangerousGoodsExtended__F1 :
    dangerousGoodsExtended__Type -> dangerousGoodsExtended__list_type **)

let dangerousGoodsExtended__F1 z0 =
  ((Obj.magic (z0.dangerousGoodsExtended__dangerousGoodsType,
     (z0.dangerousGoodsExtended__unNumber,
     (z0.dangerousGoodsExtended__elevatedTemperature,
     (z0.dangerousGoodsExtended__tunnelsRestricted,
     (z0.dangerousGoodsExtended__limitedQuantity,
     (z0.dangerousGoodsExtended__emergencyActionCode,
     (z0.dangerousGoodsExtended__phoneNumber,
     (z0.dangerousGoodsExtended__companyName, ()))))))))), (Obj.magic ()))

(** val dangerousGoodsExtended__F2 :
    dangerousGoodsExtended__list_type -> dangerousGoodsExtended__Type **)

let dangerousGoodsExtended__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, p1) = p0 in
  let (j4, p2) = p1 in
  let (j5, p3) = p2 in
  let (j6, p4) = p3 in
  let (j7, _) = p4 in
  { dangerousGoodsExtended__dangerousGoodsType = j0;
  dangerousGoodsExtended__unNumber = j1;
  dangerousGoodsExtended__elevatedTemperature = j2;
  dangerousGoodsExtended__tunnelsRestricted = j3;
  dangerousGoodsExtended__limitedQuantity = j4;
  dangerousGoodsExtended__emergencyActionCode = j5;
  dangerousGoodsExtended__phoneNumber = j6;
  dangerousGoodsExtended__companyName = j7 }

(** val dangerousGoodsExtended__Format :
    dangerousGoodsExtended__Type t_Format **)

let dangerousGoodsExtended__Format =
  proj2_format dangerousGoodsExtended__list_format dangerousGoodsExtended__F1
    dangerousGoodsExtended__F2

type numberOfOccupants__Type = int

(** val numberOfOccupants__Format : int t_Format **)

let numberOfOccupants__Format =
  ranged_int_format 0 ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))

type wMInumber__Type = char list

(** val wMInumber__Format : wMInumber__Type t_Format **)

let wMInumber__Format =
  seq_of_format ia5_string__Format 1 ((fun p->1+2*p) 1)

type vDS__Type = char list

(** val vDS__Format : vDS__Type t_Format **)

let vDS__Format =
  seq_of_fixed_format ia5_string__Format ((fun p->2*p) ((fun p->1+2*p) 1))

type vehicleIdentification__Type = { vehicleIdentification__wMInumber : 
                                     wMInumber__Type option;
                                     vehicleIdentification__vDS : vDS__Type
                                                                  option }

(** val vehicleIdentification__root_list : seq_elem list **)

let vehicleIdentification__root_list =
  Opt :: (Opt :: [])

(** val vehicleIdentification__ext_list : typ list **)

let vehicleIdentification__ext_list =
  []

type vehicleIdentification__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val vehicleIdentification__root_Format_list :
    vehicleIdentification__root_Format_Type **)

let vehicleIdentification__root_Format_list =
  ((Obj.magic wMInumber__Format), ((Obj.magic vDS__Format),
    (Obj.magic unit_format)))

type vehicleIdentification__ext_Format_Type = unit t_Format

(** val vehicleIdentification__ext_Format_list :
    vehicleIdentification__ext_Format_Type **)

let vehicleIdentification__ext_Format_list =
  unit__Format

type vehicleIdentification__list_type = seq_type * seq_ext_type

(** val vehicleIdentification__list_format :
    vehicleIdentification__list_type t_Format **)

let vehicleIdentification__list_format =
  seq_ext_format vehicleIdentification__root_list
    (Obj.magic vehicleIdentification__root_Format_list)
    vehicleIdentification__ext_list
    (Obj.magic vehicleIdentification__ext_Format_list)

(** val vehicleIdentification__F1 :
    vehicleIdentification__Type -> vehicleIdentification__list_type **)

let vehicleIdentification__F1 z0 =
  ((Obj.magic (z0.vehicleIdentification__wMInumber,
     (z0.vehicleIdentification__vDS, ()))), (Obj.magic ()))

(** val vehicleIdentification__F2 :
    vehicleIdentification__list_type -> vehicleIdentification__Type **)

let vehicleIdentification__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, _) = l in
  { vehicleIdentification__wMInumber = j0; vehicleIdentification__vDS = j1 }

(** val vehicleIdentification__Format :
    vehicleIdentification__Type t_Format **)

let vehicleIdentification__Format =
  proj2_format vehicleIdentification__list_format vehicleIdentification__F1
    vehicleIdentification__F2

type energyStorageType__Type = bit_string_fixed

(** val energyStorageType__Format : energyStorageType__Type t_Format **)

let energyStorageType__Format =
  bit_string_fixed_format ((fun p->1+2*p) ((fun p->1+2*p) 1))

type stationaryVehicleContainer__Type = { stationaryVehicleContainer__stationarySince : 
                                          stationarySince__Type option;
                                          stationaryVehicleContainer__stationaryCause : 
                                          causeCode__Type option;
                                          stationaryVehicleContainer__carryingDangerousGoods : 
                                          dangerousGoodsExtended__Type option;
                                          stationaryVehicleContainer__numberOfOccupants : 
                                          numberOfOccupants__Type option;
                                          stationaryVehicleContainer__vehicleIdentification : 
                                          vehicleIdentification__Type option;
                                          stationaryVehicleContainer__energyStorageType : 
                                          energyStorageType__Type option }

(** val stationaryVehicleContainer__list : seq_elem list **)

let stationaryVehicleContainer__list =
  Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: [])))))

type stationaryVehicleContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

(** val stationaryVehicleContainer__Format_list :
    stationaryVehicleContainer__Format_Type **)

let stationaryVehicleContainer__Format_list =
  ((Obj.magic stationarySince__Format), ((Obj.magic causeCode__Format),
    ((Obj.magic dangerousGoodsExtended__Format),
    ((Obj.magic numberOfOccupants__Format),
    ((Obj.magic vehicleIdentification__Format),
    ((Obj.magic energyStorageType__Format), (Obj.magic unit_format)))))))

(** val stationaryVehicleContainer__list__Format : seq_type t_Format **)

let stationaryVehicleContainer__list__Format =
  seq_format stationaryVehicleContainer__list
    (Obj.magic stationaryVehicleContainer__Format_list)

(** val stationaryVehicleContainer__F1 :
    stationaryVehicleContainer__Type -> stationarySince__Type
    option * (causeCode__Type option * (dangerousGoodsExtended__Type
    option * (numberOfOccupants__Type option * (vehicleIdentification__Type
    option * (energyStorageType__Type option * unit))))) **)

let stationaryVehicleContainer__F1 z0 =
  (z0.stationaryVehicleContainer__stationarySince,
    (z0.stationaryVehicleContainer__stationaryCause,
    (z0.stationaryVehicleContainer__carryingDangerousGoods,
    (z0.stationaryVehicleContainer__numberOfOccupants,
    (z0.stationaryVehicleContainer__vehicleIdentification,
    (z0.stationaryVehicleContainer__energyStorageType, ()))))))

(** val stationaryVehicleContainer__F2 :
    seq_type -> stationaryVehicleContainer__Type **)

let stationaryVehicleContainer__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, p1) = p0 in
  let (i4, p2) = p1 in
  let (i5, _) = p2 in
  { stationaryVehicleContainer__stationarySince = i0;
  stationaryVehicleContainer__stationaryCause = i1;
  stationaryVehicleContainer__carryingDangerousGoods = i2;
  stationaryVehicleContainer__numberOfOccupants = i3;
  stationaryVehicleContainer__vehicleIdentification = i4;
  stationaryVehicleContainer__energyStorageType = i5 }

(** val stationaryVehicleContainer__Format :
    stationaryVehicleContainer__Type t_Format **)

let stationaryVehicleContainer__Format =
  proj2_format stationaryVehicleContainer__list__Format
    (Obj.magic stationaryVehicleContainer__F1) stationaryVehicleContainer__F2

type alacarteContainer__Type = { alacarteContainer__lanePosition : lanePosition__Type
                                                                   option;
                                 alacarteContainer__impactReduction : 
                                 impactReductionContainer__Type option;
                                 alacarteContainer__externalTemperature : 
                                 temperature__Type option;
                                 alacarteContainer__roadWorks : roadWorksContainerExtended__Type
                                                                option;
                                 alacarteContainer__positioningSolution : 
                                 positioningSolutionType__Type option;
                                 alacarteContainer__stationaryVehicle : 
                                 stationaryVehicleContainer__Type option }

(** val alacarteContainer__root_list : seq_elem list **)

let alacarteContainer__root_list =
  Opt :: (Opt :: (Opt :: (Opt :: (Opt :: (Opt :: [])))))

(** val alacarteContainer__ext_list : typ list **)

let alacarteContainer__ext_list =
  []

type alacarteContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

(** val alacarteContainer__root_Format_list :
    alacarteContainer__root_Format_Type **)

let alacarteContainer__root_Format_list =
  ((Obj.magic lanePosition__Format),
    ((Obj.magic impactReductionContainer__Format),
    ((Obj.magic temperature__Format),
    ((Obj.magic roadWorksContainerExtended__Format),
    ((Obj.magic positioningSolutionType__Format),
    ((Obj.magic stationaryVehicleContainer__Format),
    (Obj.magic unit_format)))))))

type alacarteContainer__ext_Format_Type = unit t_Format

(** val alacarteContainer__ext_Format_list :
    alacarteContainer__ext_Format_Type **)

let alacarteContainer__ext_Format_list =
  unit__Format

type alacarteContainer__list_type = seq_type * seq_ext_type

(** val alacarteContainer__list_format :
    alacarteContainer__list_type t_Format **)

let alacarteContainer__list_format =
  seq_ext_format alacarteContainer__root_list
    (Obj.magic alacarteContainer__root_Format_list)
    alacarteContainer__ext_list (Obj.magic alacarteContainer__ext_Format_list)

(** val alacarteContainer__F1 :
    alacarteContainer__Type -> alacarteContainer__list_type **)

let alacarteContainer__F1 z0 =
  ((Obj.magic (z0.alacarteContainer__lanePosition,
     (z0.alacarteContainer__impactReduction,
     (z0.alacarteContainer__externalTemperature,
     (z0.alacarteContainer__roadWorks,
     (z0.alacarteContainer__positioningSolution,
     (z0.alacarteContainer__stationaryVehicle, ()))))))), (Obj.magic ()))

(** val alacarteContainer__F2 :
    alacarteContainer__list_type -> alacarteContainer__Type **)

let alacarteContainer__F2 = function
| (s, _) ->
  let (j0, l) = Obj.magic s in
  let (j1, p) = l in
  let (j2, p0) = p in
  let (j3, p1) = p0 in
  let (j4, p2) = p1 in
  let (j5, _) = p2 in
  { alacarteContainer__lanePosition = j0; alacarteContainer__impactReduction =
  j1; alacarteContainer__externalTemperature = j2;
  alacarteContainer__roadWorks = j3; alacarteContainer__positioningSolution =
  j4; alacarteContainer__stationaryVehicle = j5 }

(** val alacarteContainer__Format : alacarteContainer__Type t_Format **)

let alacarteContainer__Format =
  proj2_format alacarteContainer__list_format alacarteContainer__F1
    alacarteContainer__F2

type decentralizedEnvironmentalNotificationMessage__Type = { decentralizedEnvironmentalNotificationMessage__management : 
                                                             managementContainer__Type;
                                                             decentralizedEnvironmentalNotificationMessage__situation : 
                                                             situationContainer__Type
                                                             option;
                                                             decentralizedEnvironmentalNotificationMessage__location : 
                                                             locationContainer__Type
                                                             option;
                                                             decentralizedEnvironmentalNotificationMessage__alacarte : 
                                                             alacarteContainer__Type
                                                             option }

(** val decentralizedEnvironmentalNotificationMessage__list : seq_elem list **)

let decentralizedEnvironmentalNotificationMessage__list =
  Nor :: (Opt :: (Opt :: (Opt :: [])))

type decentralizedEnvironmentalNotificationMessage__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

(** val decentralizedEnvironmentalNotificationMessage__Format_list :
    decentralizedEnvironmentalNotificationMessage__Format_Type **)

let decentralizedEnvironmentalNotificationMessage__Format_list =
  ((Obj.magic managementContainer__Format),
    ((Obj.magic situationContainer__Format),
    ((Obj.magic locationContainer__Format),
    ((Obj.magic alacarteContainer__Format), (Obj.magic unit_format)))))

(** val decentralizedEnvironmentalNotificationMessage__list__Format :
    seq_type t_Format **)

let decentralizedEnvironmentalNotificationMessage__list__Format =
  seq_format decentralizedEnvironmentalNotificationMessage__list
    (Obj.magic decentralizedEnvironmentalNotificationMessage__Format_list)

(** val decentralizedEnvironmentalNotificationMessage__F1 :
    decentralizedEnvironmentalNotificationMessage__Type ->
    managementContainer__Type * (situationContainer__Type
    option * (locationContainer__Type option * (alacarteContainer__Type
    option * unit))) **)

let decentralizedEnvironmentalNotificationMessage__F1 z0 =
  (z0.decentralizedEnvironmentalNotificationMessage__management,
    (z0.decentralizedEnvironmentalNotificationMessage__situation,
    (z0.decentralizedEnvironmentalNotificationMessage__location,
    (z0.decentralizedEnvironmentalNotificationMessage__alacarte, ()))))

(** val decentralizedEnvironmentalNotificationMessage__F2 :
    seq_type -> decentralizedEnvironmentalNotificationMessage__Type **)

let decentralizedEnvironmentalNotificationMessage__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, p) = l in
  let (i2, p0) = p in
  let (i3, _) = p0 in
  { decentralizedEnvironmentalNotificationMessage__management = i0;
  decentralizedEnvironmentalNotificationMessage__situation = i1;
  decentralizedEnvironmentalNotificationMessage__location = i2;
  decentralizedEnvironmentalNotificationMessage__alacarte = i3 }

(** val decentralizedEnvironmentalNotificationMessage__Format :
    decentralizedEnvironmentalNotificationMessage__Type t_Format **)

let decentralizedEnvironmentalNotificationMessage__Format =
  proj2_format decentralizedEnvironmentalNotificationMessage__list__Format
    (Obj.magic decentralizedEnvironmentalNotificationMessage__F1)
    decentralizedEnvironmentalNotificationMessage__F2

type dENM__Type = { dENM__header : itsPduHeader__Type;
                    dENM__denm : decentralizedEnvironmentalNotificationMessage__Type }

(** val dENM__list : seq_elem list **)

let dENM__list =
  Nor :: (Nor :: [])

type dENM__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

(** val dENM__Format_list : dENM__Format_Type **)

let dENM__Format_list =
  ((Obj.magic itsPduHeader__Format),
    ((Obj.magic decentralizedEnvironmentalNotificationMessage__Format),
    (Obj.magic unit_format)))

(** val dENM__list__Format : seq_type t_Format **)

let dENM__list__Format =
  seq_format dENM__list (Obj.magic dENM__Format_list)

(** val dENM__F1 :
    dENM__Type ->
    itsPduHeader__Type * (decentralizedEnvironmentalNotificationMessage__Type * unit) **)

let dENM__F1 z0 =
  (z0.dENM__header, (z0.dENM__denm, ()))

(** val dENM__F2 : seq_type -> dENM__Type **)

let dENM__F2 y =
  let (i0, l) = Obj.magic y in
  let (i1, _) = l in { dENM__header = i0; dENM__denm = i1 }

(** val dENM__Format : dENM__Type t_Format **)

let dENM__Format =
  proj2_format dENM__list__Format (Obj.magic dENM__F1) dENM__F2
