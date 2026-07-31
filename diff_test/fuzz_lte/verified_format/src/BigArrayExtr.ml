type bigarray_buf = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

type byte_buf =
  { buf_len : int;
    buffer : bigarray_buf;
  }

(*let const_char init_char index = init_char *)

let buf_len bf = bf.buf_len

let buffer bf = bf.buffer

let create len =
  { buf_len = len;
    buffer = Bigarray.(Array1.create char Bigarray.c_layout len)
  }

let make len init_char =
  let bf = create len in
  Bigarray.Array1.fill (bf.buffer) init_char;
  bf

let get bf index =
  if index < bf.buf_len then
    Some (Bigarray.Array1.get bf.buffer index)
  else
    None

let set bf index c =
  if index < bf.buf_len then 
    (Bigarray.Array1.set bf.buffer index c;
    Some bf)
  else
    None

let byte_of_nat n = Some (Char.chr n)

let nat_ones n = (1 lsl n) - 1

let int_id (n : int) = n

let log2 (n : int) =
  if n = 0 then
    0  
  else (Base.Int.floor_log2 n)
