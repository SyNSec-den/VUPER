(*open ASN1Format  *)

(*let i1 = INTEGER (RANGED_INT (INT_LIT 1, INT_LIT 10))

let i2 = ENUM ["ok"; "bad"; "very"] *)

(*let () =
  print_len_cons (FIXED_LEN 10);
  print_len_cons (RANGED_LEN (1, 10));
  print_len_cons (NO_CONS_LEN);
  Printf.printf "\n" *)

(*let s1 = SEQUENCE  
               [(NORMAL ("s10", TERM i1));
                (OPTIONAL ("s11", TERM i1))]

let s2 = ("Seq_2",
          (SEQUENCE  
             [(NORMAL ("w1", TERM (Ref "T1")));
              (OPTIONAL ("w2", TERM BOOLEAN));
              (NORMAL ("w3", TERM BOOLEAN));
              (NORMAL ("w5", TERM (ENUM
                                     ["ok"; "bad"; "spare1"])))]))

let s3 = ("Seq_3",
          (SEQUENCE_Ext (
               [(NORMAL ("x1", TERM (Ref "T2")));
                (OPTIONAL ("x2", TERM BOOLEAN));
                (* (NORMAL ("x4", s1)); *)
                (NORMAL ("x5", TERM (Ref "Seq_2")))
               ],
               [EXT_ELEM ("e1", TERM BOOLEAN);
                EXT_ELEM ("e2", TERM (INTEGER (RANGED_INT (INT_LIT 1, INT_LIT 20))));
                EXT_ELEM ("e3", TERM (Ref "T1"))
         ])))

let (l : asn1_list) = [ASN_Type ("T1", TERM i1);
                       ASN_Type ("T2", TERM i2);
                       ASN_Type s2; ASN_Type s3]

 *)
let () =
(*  print_typ_def s2;
  print_typ_def s3; *)
  (* Printf.printf "%s" (Compiler.gen_asn1_list_def l) *)
  (* Driver.asn1_compile "test/test.asn1" "../ExtrTest/def/test.v"  *)
  let ast = Driver.read_file "test/nr.asn1" in
  Compiler.gen_asn1_obj ast
  (*Compiler.gen_extract_file "BCCH_BCH_Message" "../../ExtrTest/src/FormatTest.ml" *)
    (*print_obj ast *)

