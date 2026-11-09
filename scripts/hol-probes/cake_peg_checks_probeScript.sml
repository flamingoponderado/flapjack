load "pegexec_cml_foTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "symbols="; print_term (rhs (concl (EVAL ``
 MAP (\s. (gram$validMultSym s,gram$validAddSym s,gram$validRelSym s,gram$validListSym s,gram$validPrefixSym s))
 ["";"+";"|";"||";"=";"==";":";":=";"::";"~";"~~";"!";"*";"@"]``))); print "\n");
val _ = (print "alpha="; print_term (rhs (concl (EVAL ``
 MAP (\s. MAP (\p. pegexec_cml_fo$eval_token_alpha_check p s)
   [TokenAlpha_nonempty;TokenAlpha_upper_initial;TokenAlpha_lower_initial_not_reserved])
 [«»;«Name»;«value»;«before»;«div»;«mod»;«o»;«_x»]``))); print "\n");
val _ = (print "tokens="; print_term (rhs (concl (EVAL ``
 let l = location$unknown_loc in
 [(pegexec_cml_fo$eval_token_check (TokenCheck_eq tokens$ValT) (tokens$ValT,l));
  (pegexec_cml_fo$eval_token_check TokenCheck_isInt (tokens$IntT 5,l));
  (pegexec_cml_fo$eval_token_check (TokenCheck_alpha TokenAlpha_lower_initial_not_reserved) (tokens$AlphaT «mod»,l));
  (pegexec_cml_fo$eval_token_check (TokenCheck_symbol TokenSymbol_valid_list) (tokens$SymbolT «::»,l));
  (pegexec_cml_fo$eval_token_check (TokenCheck_longid TokenLongid_ctor_upper_initial) (tokens$LongidT (tokens$Mod «M» tokens$End) «Name»,l));
  (pegexec_cml_fo$eval_token_check (TokenCheck_longid TokenLongid_tail_nonempty_head_alpha_not_upper) (tokens$LongidT tokens$End «+»,l));
  (pegexec_cml_fo$eval_token_check TokenCheck_opid_alpha_nonempty (tokens$AlphaT «»,l))]``))); print "\n");
