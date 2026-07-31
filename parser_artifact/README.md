# Verified ASN1 Encoder/Decoder 

This is a project that aims to provide a formalization of 
ASN.1, notably Unaligned PER encodings. And provide correctness 
proofs and guarantees to both encoders and decoders of ASN.1.


# Structure of our Project

## Simple Formats
The need for simple formats is that they are bijective. They are 
used in the Root elements, as well as some supportive structures 
in more complicated format like Sequence. 

There are 5 different simple format combinators. 

### Module Definitions
We define these formats abstractly first, then we move on to 
concrete implementations. 

  * `AbsFormat`. In this file is the formal definition of a basic
		format. This includes 
	
	1. Unit/Basic Nat. This simply encode a `word` of $n$-bits.
	2. Projection. This will work as a bijection map between two 
		formats.
	3. Append. This will append one format after another.
	4. Sigma. Similar to Append. However, the second format is 
		dependent on the first value. But note that the second type does 
		NOT dependent on the first value. Thus it is not strictly a 
		$\Sigma$-type.
	5. Restrict. This will restrict the format to a smaller domain.
	
  * `AbsArray`. This file defines the Module Type for `Array`, 
	a abstract notion of a byte buffer which would store the 
	encoded bit-stream.
	
	A separate Module Type `ArrayProp` is defined alongside 
	`Array`. This will provide the properties we want the `Array`
	to have, while keeping the functional and theoretical parts 
	separate. 

	The third part is the definition of equivalent bits. A way to 
	compare two byte buffers between two bit positions. This will
	facilitate the encoder/decoder correctness definition.
	
  * `AbsComb`. Here is all the parser combinators we need for 
	basic formats. However, we might still reuse some of these 
	combinators in later parts. This is defined in `FormatComb`.
	
	The second part is the correctness definitions that they have, 
	which would be summerized later. 
	
	A `Parser` module type is also defined here. It has two 


### Byte Buffer

First, we briefly discuss the Bit-Buffer. We can simply think 
of this as using a `list bool` to store all the data, which is 
perfect in a theoretical setting. But it would be quite slow if
we were to extract it and run it on actual systems. 

Now, for Byte-Buffer. We can visualize it as follows, 
	

		|--------|--------|--------|
		  ^            ^
		  pos1         pos2
	
When we encode some value, we will be given a byte buffer, 
some initial position. The position here will consists of a 
tuple of the byte position and the bit position within that 
byte. In this example `pos1` will be `(0, I1)`. 
It will output a new buffer and a new position after the 
encoding. 

When we decode some buffer, we will also be given a position.
And the output will be the decoded value and a new position. 

### Simple/Basic Types

Here we discuss the basic types that we support. This is included
in the `src/Formats/Term`.

  * `NonNeg.v` Non-Negative Integer. Here, we use `nat` in Coq to represent
	it. It is not standalone. It is used as the basis for almost 
	all other formats through projections. 
  
  * `ConsInt.v` Integer (Constrained). 
  
  * `Boolean.v` Boolean.
  
  * `LengthDet.v` Length Determinant. This is not a standalone format. 
	Instead it is usually used in other formats like Byte
	Strings, Open Types, or other combinators. This includes both 
	constrained, unconstrained and normally length determinant. 
  
  * `ListFormat.v`. This is a list defined through basic formats. 
	It could be used in Bit/Octet String.
  
  * `BitString.v` Bit String. (Yet to fully implement)
  
  * `OctetString.v` Byte String. (Yet to fully implement)


## ASN.1 Encoder/Decoder Combinators
These combinators are for ASN.1 only. This cannot be derived from 
simple combinators because they do not satisfy the bijective property.

This is mostly in `src/Formats/Comb`.

  * Sequence. In `Sequence.v` is the type information. 
	And the actual decoder is in `SeqImpl.v`. 
  
  * Sequence with Extension. Similar to Sequence. It has two files 
	`SequenceExt.v` and `SeqExtImpl.v`.
	
  * Choice. Defined in `Choice.v`. 
  
  * Sequence Of. Defined in `SequenceOf.v`.

## Correctness Proofs

The proofs are all in the file names ending with `Prop`. 

# Code Generation and Extraction 

## Generate from ASN.1 Definition to Coq

The first question that we face is how to generate Coq code from 
ASN.1 definitions. This is solved in the `Compile/` part of 
the code. 

Basically, there is a lexer and parser defined (using ocamllex 
and menhir) that will parse the ASN.1 definition into an 
abstract syntax tree defined in `Compile/src/ASN1Format.ml`. 

Then, in `Compile/src/compiler/ml`, the function `gen_asn1_list_def`
will turn an AST into a Coq file, which can be used to extract
OCaml code. 

Some things to note, we have to use this approach because 
our representation of some types, like Sequence or Enum relies
heavily on dependent types. So we will generate the definition
separately, for example, 

	T0 ::= ENUMERATED {ok, err, spare} 

will be translated into 

	Inductive T0__type := ok | err | spare. 

in Coq. Similar for Sequence, which corresponds to Record type.
Here is an example, say 

	S-1 ::= SEQUENCE {
	  e1  T0,
	  e2  INTEGER (0..10)  OPTIONAL,
	  e3  BOOLEAN
	}

Then, first we would define the `e2` item. Here, we would need to
define some helper lemmas for the generation of the Integer parser.

	Definition S_1__e2__type := Z. 

This would correspond to the Record type,

	Record S_1__type := 
	  make__S_1__type {
	    S_1__e1 : T0__type;
		S_1__e2 : option S_1__e2__type;
		S_1__e3 : bool;
	}.

Then, there is a `list typ` that represents `S-1`. It would be 
defined as 

	Definition S_1__list := 
	  Nor T0__type T0__cond :: 
	  Opt S_1__e2__type S_1__e2__cond :: 
	  Nor bool (fun _ => True) ::
	  nil.
	   
This would give us the new type `seq_type S_1__list`, which is
	
	(T0__type * (S_1__e2__type * (bool * unit))).

Here we will derive the encoder/decoder from this. It corresponds
to the `src/Formats/SeqImpl.v` file. There should be some mapping
between the two types. This is defined as 

	Definition S_1__f2 (y : seq_type S_1__list) := 
	  match y with
	  | (i0, (i1, (i2, _))) => 
	    make__S_1__type i0 i1 i2
      end.
	
To obtain the parser for `S-1`, we first obtain a parser for 
`seq_type S_1__list`. This can be obtained by generating all the 
parsers of the types. Here, 

	Definition S_1__dec_list := 
	  (T0__dec, (S_1__e2__dec, (bool_dec, ByteParser.read_unit))).
	 
	Definition S_1__list__dec := 
	  seq_parse S_1__list S_1__dec_list.

Then we can using `S_1__f2` to map the result to `S_1__type`.

## Extraction from Coq to OCaml

Here we discuss the extraction process. There is a gap between
Coq and OCaml. Coq has a much richer type system than OCaml. 
It supports dependent types, and can easily manipulate types. 
This would cause things to be mapped to `Obj.t` in OCaml, which
is not ideal. For example, when we have a type like 
`(to_type x)`, it would be `Obj.t` instead of the actual type, 
say `(nat, (bool, unit))`. This is not ideal. 
Certain functions must be computed in Coq in order 
that it would work.


## Environment Setup

We use OCaml version 4.14 and Coq version 8.20. 

First [install opam]{https://opam.ocaml.org/doc/Install.html}. 
Next, use `opam switch import vuper_env.export` to set up the environment. 


## Steps

### 0. Build the base `asn1parser` library (one-time setup)

The generated project (e.g. `NR17`) depends on the base formalization in
`asn1parser/` (its `_CoqProject` references it via `-R ../../asn1parser/src
ASN1Parser`). This library is not pre-built and has no `Makefile` checked in,
so it must be compiled once before step 6 below, otherwise `make` fails with
an error like:
```
No rule to make target '../../asn1parser/src/ExtrOCaml/ExtractHelper.vo'
```
Build it with:
```
cd asn1parser && coq_makefile -f _CoqProject -o Makefile && make
```
This only needs to be done once (or whenever `asn1parser/` changes) — it does
not need to be repeated for each ASN.1 project you compile.

In `Compile/` there is a compiler that takes an ASN.1 definition as
input and outputs serializer/parser functions in Coq.

**1. Configure the input.**
Set the ASN.1 file path in `Compile/src/test_format.ml` (currently
`test/nr.asn1`) and set `proj_name` in `Compile/src/compiler_basic.ml`
(currently `"NR17"`).

**2. Build the compiler.**
```
cd Compile && dune build
```

**3. Create the output directory.**
The compiler writes directly into a directory named after `proj_name`,
which must exist beforehand:
```
mkdir Compile/NR17
```

**4. Run the compiler.**
Run from inside `Compile/`:
```
./_build/default/src/test_format.exe
```
The generated Coq files will appear in `Compile/NR17/`.

**5. Generate the Makefile.**
The compiler produces a `_CoqProject` file but not a `Makefile`.
Generate one with:
```
cd Compile/NR17 && coq_makefile -f _CoqProject -o Makefile
```

**6. Compile the Coq files.**
```
make
```

**7. Add an extraction file.**
To extract OCaml code from a Coq type, create a small `.v` file in
`Compile/NR17/`. See `Compile/NR/extr_dl_dcch.v` for an example:
```coq
Require Export ASN1Parser.ExtrOCaml.Extract.
Require Import NR17.DL_DCCH_Message.
Extraction "../../ExtrTest/src/FormatTest.ml" DL_DCCH_Message__enc DL_DCCH_Message__dec.
```
Update the `Require Import` module name, the destination path, and the
exported symbols to match your target type. Then add the file name to
`_CoqProject`, regenerate the Makefile (step 5), and run `make` again.
This produces the extracted OCaml file in `ExtrTest/src/`.

**8. Fix two spurious `rec` flags in the extracted OCaml file.**
Coq's extraction sometimes emits `let rec` for non-recursive bindings,
which OCaml rejects as warnings-as-errors. In `ExtrTest/src/FormatTest.ml`,
change:
```ocaml
let rec succ = Stdlib.Int.succ
let rec compare_cont = fun c x y -> ...
```
to:
```ocaml
let succ = Stdlib.Int.succ
let compare_cont = fun c x y -> ...
```

**9. Generate pretty-printer stubs.**
Run from inside `ExtrTest/`:
```
cd ExtrTest && python3 scripts/generate_pp.py
```
This reads `src/FormatTest.mli` and generates `src/FormatJson.ml`.

**10. Build and run the tests.**
```
cd ExtrTest && dune build
```
