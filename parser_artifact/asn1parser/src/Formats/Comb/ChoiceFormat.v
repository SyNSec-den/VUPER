Require Import
          ASN1Parser.Formats.Comb
          ASN1Parser.Formats.Comb.SeqProd
          ASN1Parser.Formats.Comb.HelperComb
          ASN1Parser.Formats.Comb.Choice
          ASN1Parser.Formats.Comb.ChoiceProp
          ASN1Parser.Formats.Term.Unit.

Definition choice_format
  (l : list typ)
  (pf1 : length_cond l)
  (length_l_ge2 : 2 <= length2 l)
  (fmts : get_formats l) := 
  mk_format  (choice l) (choice_cond l)
    (choice_serial l pf1 (fmt_to_prodc l fmts Serialize T_Serial put_empty))
    (choice_parse l pf1 (fmt_to_prodc l fmts Parse T_Parse read_empty))
    (choice_to_len l (fmt_to_prod_no_condc l fmts _ (T_to_len) empty_to_len))
    (choice_format_correct l pf1 length_l_ge2 fmts).
