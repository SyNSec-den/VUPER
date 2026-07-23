Require Import ASN1Parser.Formats.Comb
               ASN1Parser.Formats.Comb.Seq
               ASN1Parser.Formats.Comb.SeqProp
               ASN1Parser.Formats.Term.Unit.

Definition seq_format (l : list seq_elem) (fmts : seq_format_prod l) : T_Format (seq_type l) (seq_cond l) :=
  mk_format
    _ _ 
      (seq_serialize l (fmt_to_seq_prod l fmts Serialize T_Serial put_unit))
      (seq_parse l (fmt_to_seq_prod l fmts Parse T_Parse read_unit))
      (seq_to_len l (fmt_to_seq_prod_no_cond l fmts (fun X => X -> option nat)
                       T_to_len (fun _ => Some 0)))
      (seq_format_correct l fmts).
                      
