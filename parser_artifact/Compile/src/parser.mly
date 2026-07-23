%{
open ASN1Format
%}

%token <int> INT_VAL
%token <string> REF
%token <string> ID
%token <string> BITS
(* Need to add support for modules *)
%token DEFINITIONS
%token AUTOMATIC_TAGS
%token BEGIN END
%token IMPORTS FROM SEMICOLON
(* For the terminal types and combinators *)
%token NULL
%token INTEGER BOOLEAN ENUM
%token BIT OCTET STRING
%token IA5String NumericString UTF8String
%token CONTAINING
%token SEQUENCE
%token WITH COMPONENTS ABSENT
%token CHOICE
%token OF SIZE
%token OPTIONAL
%token DEFAULT
%token ASSIGN
%token COMMA
%token LBRACE RBRACE
%token LPAREN RPAREN
(* Here brack2 means double bracks *)
%token LBRACK2 RBRACK2
%token DOTS_EXT 
%token DOTS_SIZE
(*%token SIZE *)
%token EOF 

%start <asn1_obj> prog
%%

prog:
  | p = list(module_read); EOF { p };

module_read:
  | name = REF; DEFINITIONS ; AUTOMATIC_TAGS ; ASSIGN ; BEGIN ; ir = import_lists_read; lr = list_read ; END
    { (name, ir, lr)  } ;

import_lists_read:
  | ir = loption (delimited (IMPORTS, list(import_list_read), SEMICOLON))
    { ir } ;

import_list_read:
  | nl = separated_list(COMMA, name_read); FROM; name = REF { (name, nl) } ;

name_read:
  | name = ID { Val_Import name }
  | name = REF { Type_Import name } ;

list_read:
  | lr = list (expr) { lr } ;

expr:
  | v = val_asgn { ASN_Val v }
  | pt = param_type_asgn { ASN_PARAM_Type pt } 
  | t = type_asgn { ASN_Type t } ;

val_asgn:
  | name = ID; INTEGER; ASSIGN; n = INT_VAL
    { INT_value (name, n) } ;

type_asgn: 
  | name = REF; ASSIGN; t = type_read
    { (name, t) } ;

param_type_asgn:
  | name = REF; LBRACE ; param = REF ; RBRACE ; ASSIGN ; t = type_read
    { (name, param, t) } ;

asn1_int_read:
  | name = ID { INT_REF name }
  | n = INT_VAL { INT_LIT n } ;

length_cons_read:
  | LPAREN; SIZE; LPAREN ; a = asn1_int_read ; RPAREN;  RPAREN { FIXED_LEN a }
  | LPAREN; SIZE; LPAREN ; lb = asn1_int_read ; DOTS_SIZE; ub = asn1_int_read ; RPAREN;
    RPAREN
      { RANGED_LEN (lb, ub) }
  | LPAREN; SIZE; LPAREN ; lb = asn1_int_read ; DOTS_SIZE; ub = asn1_int_read ; COMMA;
    DOTS_EXT
    RPAREN; RPAREN
      { RANGED_LEN_Ext (lb, ub) } 
  | { NO_CONS_LEN } ;

(* For octet the constraint might be  *)
octet_cons_read:
  | LPAREN; SIZE; LPAREN ; a = asn1_int_read ; RPAREN;  RPAREN { FIXED_LEN a }
  | LPAREN; SIZE; LPAREN ; lb = asn1_int_read ; DOTS_SIZE; ub = asn1_int_read ; RPAREN; RPAREN
    { RANGED_LEN (lb, ub) } 
  | LPAREN ; CONTAINING ; REF ; RPAREN { NO_CONS_LEN }
  | { NO_CONS_LEN } ;

named_number:
  | ID ; LPAREN ; asn1_int_read ; RPAREN { } ;
    
named_number_list_read:
  | delimited (LBRACE, separated_list ( COMMA, named_number), RBRACE ) {  }
  | { } ;

int_cons_read:
  | LPAREN ; n = asn1_int_read ; RPAREN { FIXED_INT n }
  | LPAREN; lb = asn1_int_read; DOTS_SIZE; ub = asn1_int_read;
    RPAREN
      { RANGED_INT (lb, ub)  }
  | LPAREN; lb = asn1_int_read; DOTS_SIZE; ub = asn1_int_read; COMMA;
    DOTS_EXT ; RPAREN
      { RANGED_INT_Ext (lb, ub) }
  | { NO_CONS_INT } ;

known_string_name:
  | IA5String { IA5String }
  | NumericString { NumericString } ;

enum_id_read:
  | id = ID { id } 
  | id = ID ; LPAREN ;  asn1_int_read ; RPAREN { id } ; 

basic_type_read:
  | NULL { NULL }
  | INTEGER; named_number_list_read ; c = int_cons_read  { INTEGER c }
  | BOOLEAN { BOOLEAN }
  | ENUM; si = delimited (LBRACE, separated_list (COMMA, enum_id = enum_id_read { enum_id } ), RBRACE )
    { ENUM si }
  | ENUM ; LBRACE ; si = terminated ( list (s = enum_id_read; COMMA { s } ), DOTS_EXT ); ei = list ( COMMA ; s = enum_id_read { s } ) ; RBRACE
    { ENUM_Ext (si, ei) }
  | BIT ; STRING; named_number_list_read ; c = length_cons_read  { BIT_STRING c }
  | OCTET ; STRING; c = octet_cons_read  { OCTET_STRING c }
  | str_name = known_string_name ; c = length_cons_read { KnownMultiString (str_name, c) }
  | UTF8String ; octet_cons_read { UnknownMultiString UTF8String }
  | name = REF { Ref name }
  | name = REF ; LBRACE ; param = REF ; RBRACE
    { PARAM_Ref (name, param) } ;

type_read:
  | btv = basic_type_read { TERM btv } 
  | SEQUENCE; LBRACE; sv = separated_list (COMMA, seq_value); RBRACE
    { SEQUENCE sv }
  | SEQUENCE; LBRACE; sv = terminated ( list (s = seq_value; COMMA { s } ), DOTS_EXT ); ext = list (ext_list_value); RBRACE
    { SEQUENCE_Ext (sv, ext) }

  | CHOICE; LBRACE; cv = separated_list (COMMA, list_value); RBRACE
    { CHOICE (cv) }

  | CHOICE; LBRACE; cv = terminated ( list (s = list_value; COMMA { s } ), DOTS_EXT ); ext = list (ext_list_value_choice); RBRACE
    { CHOICE_Ext (cv, ext) }

  | SEQUENCE; c = length_cons_read; OF; t = type_read
    { SEQUENCE_OF (c, t) } ;

(* This is for sequence value only, will include
OPTIONAL, DEFAULT values
*)

seq_value:
  | name = ID; t = type_read; sm = seq_marker { sm (name, t) } ;

default_val_read:
  | n = INT_VAL { INTEGER_DFT n }
  | s = ID { STR_DFT s }
  | b = BITS { BITS_DFT b } ;

seq_marker:
  | OPTIONAL { fun (a, b) -> OPTIONAL (a, b) }
  | DEFAULT ; d = default_val_read { fun (a, b) -> DEFAULT (a, b, d) }
  | LPAREN ; WITH ; COMPONENTS ; LBRACE ; DOTS_EXT ; COMMA ; field_name = ID ; ABSENT ; RBRACE ; RPAREN
      { fun (a, b) -> CONSTRAINT (a, b, ABSENT field_name)  }
  | { fun (a, b) -> NORMAL (a, b) } ;

ext_list_value:
  | COMMA; name = ID; t = type_read { EXT_ELEM (name, t) }
  | COMMA; name = ID; t = type_read; OPTIONAL { EXT_ELEM (name, t) } 
  | COMMA; e = extension_grp_read { EXT_GRP e } ;

ver_bracket_ign_l:
  | LBRACK2 { () }
  | { () } ;

ver_bracket_ign_r:
  | RBRACK2 { () }
  | { () } ;

ext_list_value_choice:
  | COMMA; ver_bracket_ign_l ; name = ID; t = type_read ; ver_bracket_ign_r
    { (name, t) }

list_value:
  | name = ID; t = type_read { (name, t) } ; 

(* For extension groups *)
extension_grp_read:
  | LBRACK2; sv = separated_list (COMMA, seq_value); RBRACK2
    { sv }

