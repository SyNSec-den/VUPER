{
open Parser

exception SyntaxError of string
}

let white = [' ' '\t' '\n']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let chars = ['a'-'z' 'A'-'Z' '0'-'9']
let uppercase = ['A'-'Z']
let lowercase = ['a'-'z']
let bits = '\'' ['0'-'1']+ '\'' 'B'

let id = lowercase chars* ('-' chars+)*
let ref = uppercase chars* ('-' chars+)*

(* Here is the inline comments *)
let inline_cmt = "--" [^'\n']*

rule read =
     parse
     | white      { read lexbuf }
     | int 	  { INT_VAL (int_of_string (Lexing.lexeme lexbuf)) }
     | bits 	  { BITS (Lexing.lexeme lexbuf) }
     | inline_cmt { read lexbuf }
     | "DEFINITIONS" { DEFINITIONS }
     | "AUTOMATIC TAGS" { AUTOMATIC_TAGS }
     | "BEGIN"	  { BEGIN }
     | "END" 	  { END }
     | "IMPORTS"  { IMPORTS }
     | "FROM" 	  { FROM }
     | "NULL" 	  { NULL }
     | "INTEGER"  { INTEGER }
     | "BOOLEAN"  { BOOLEAN }
     | "OCTET" 	  { OCTET }
     | "BIT"	  { BIT }
     | "STRING"   { STRING }
     | "IA5String" { IA5String }
     | "NumericString" { NumericString }
     | "UTF8String" { UTF8String } 
     | "ENUMERATED" { ENUM }
     | "SEQUENCE" { SEQUENCE }
     | "WITH" 	  { WITH }
     | "COMPONENTS" { COMPONENTS }
     | "ABSENT"	  { ABSENT }
     | "CHOICE"	  { CHOICE }
     | "OF"	  { OF }
     | "SIZE" 	  { SIZE }
     | "OPTIONAL" { OPTIONAL }
     | "DEFAULT"  { DEFAULT } 
     | "CONTAINING" { CONTAINING }
     | "::=" 	  { ASSIGN }
     | "," 	  { COMMA }
     | ";"	  { SEMICOLON }
     | "{"	  { LBRACE }
     | "}" 	  { RBRACE }
     | "("	  { LPAREN }
     | ")" 	  { RPAREN }
     | "[["	  { LBRACK2 }
     | "]]"	  { RBRACK2 }
     | "..." 	  { DOTS_EXT }
     | ".." 	  { DOTS_SIZE }
     | id	  { ID (ASN1Format.hp_to_us (Lexing.lexeme lexbuf)) }
     | ref 	  { REF (ASN1Format.hp_to_us (Lexing.lexeme lexbuf)) }
     | _ 	  { raise (SyntaxError ("Unexpected char " ^ Lexing.lexeme lexbuf)) }
     | eof 	  { EOF }

