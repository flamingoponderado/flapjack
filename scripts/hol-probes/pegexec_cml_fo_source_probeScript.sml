(* Typed source declarations for pegexec_cml_fo. *)
load "preamble";
load "pegexec_cml_foTheory";
open HolKernel Parse boolLib bossLib;
open preamble pegexec_cml_foTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun show_cons label cs = (print (label ^ "=");
  print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs)); print "\n");

val _ = show_cons "sem_u_typed" [``pegexec_cml_fo$SemU_id``, ``pegexec_cml_fo$SemU_bindNT``];
val _ = show_cons "sem_b_typed" [``pegexec_cml_fo$SemB_first``, ``pegexec_cml_fo$SemB_second``, ``pegexec_cml_fo$SemB_append``, ``pegexec_cml_fo$SemB_mklinfix``, ``pegexec_cml_fo$SemB_foldl_Eapp``, ``pegexec_cml_fo$SemB_foldl_DType``, ``pegexec_cml_fo$SemB_papp_ctor_rpt``, ``pegexec_cml_fo$SemB_ebase_paren_apply``, ``pegexec_cml_fo$SemB_bindNT0``];
val _ = show_cons "token_alpha_check_typed" [``pegexec_cml_fo$TokenAlpha_nonempty``, ``pegexec_cml_fo$TokenAlpha_upper_initial``, ``pegexec_cml_fo$TokenAlpha_lower_initial_not_reserved``];
val _ = show_cons "token_symbol_check_typed" [``pegexec_cml_fo$TokenSymbol_nonempty``, ``pegexec_cml_fo$TokenSymbol_valid_mult``, ``pegexec_cml_fo$TokenSymbol_valid_add``, ``pegexec_cml_fo$TokenSymbol_valid_rel``, ``pegexec_cml_fo$TokenSymbol_valid_list``, ``pegexec_cml_fo$TokenSymbol_valid_prefix``];
val _ = show_cons "token_longid_check_typed" [``pegexec_cml_fo$TokenLongid_tail_nonempty``, ``pegexec_cml_fo$TokenLongid_tail_nonempty_head_alpha_not_upper``, ``pegexec_cml_fo$TokenLongid_ctor_upper_initial``];
val _ = show_cons "token_check_typed" [``pegexec_cml_fo$TokenCheck_always``, ``pegexec_cml_fo$TokenCheck_never``, ``pegexec_cml_fo$TokenCheck_eq``, ``pegexec_cml_fo$TokenCheck_isInt``, ``pegexec_cml_fo$TokenCheck_isString``, ``pegexec_cml_fo$TokenCheck_isChar``, ``pegexec_cml_fo$TokenCheck_isWord``, ``pegexec_cml_fo$TokenCheck_isFFI``, ``pegexec_cml_fo$TokenCheck_alpha``, ``pegexec_cml_fo$TokenCheck_symbol``, ``pegexec_cml_fo$TokenCheck_longid``, ``pegexec_cml_fo$TokenCheck_isTyvarT``, ``pegexec_cml_fo$TokenCheck_isAlphaSym``, ``pegexec_cml_fo$TokenCheck_isLongidT``, ``pegexec_cml_fo$TokenCheck_opid_longid_nonempty``, ``pegexec_cml_fo$TokenCheck_opid_symbol_nonempty``, ``pegexec_cml_fo$TokenCheck_opid_alpha_nonempty``];
val _ = show_cons "tok_map_typed" [``pegexec_cml_fo$TokenMap_mktokLf``, ``pegexec_cml_fo$TokenMap_empty_list``, ``pegexec_cml_fo$TokenMap_bindNT``];
val _ = show_cons "pegsym_fo_typed" [``pegexec_cml_fo$Empty_fo``, ``pegexec_cml_fo$Any_fo``, ``pegexec_cml_fo$Tok_fo``, ``pegexec_cml_fo$Nt_fo``, ``pegexec_cml_fo$Seq_fo``, ``pegexec_cml_fo$Choice_fo``, ``pegexec_cml_fo$Rpt_fo``, ``pegexec_cml_fo$Not_fo``, ``pegexec_cml_fo$Error_fo``];
val _ = show "eval_unary_def_typed" pegexec_cml_foTheory.eval_unary_def;
val _ = show "mk_linfix_fo_def_typed" pegexec_cml_foTheory.mk_linfix_fo_def;
val _ = show "mkNd_fo_def_typed" pegexec_cml_foTheory.mkNd_fo_def;
val _ = show "eval_binary_def_typed" pegexec_cml_foTheory.eval_binary_def;
val _ = show "eval_token_alpha_check_def_typed" pegexec_cml_foTheory.eval_token_alpha_check_def;
val _ = show "eval_token_symbol_check_def_typed" pegexec_cml_foTheory.eval_token_symbol_check_def;
val _ = show "eval_token_longid_check_alt_def_typed" pegexec_cml_foTheory.eval_token_longid_check_alt_def;
val _ = show "eval_token_check_def_typed" pegexec_cml_foTheory.eval_token_check_def;
val _ = show "eval_tok_map_def_typed" pegexec_cml_foTheory.eval_tok_map_def;
val _ = show "nt_rule_fo_def_typed" pegexec_cml_foTheory.nt_rule_fo_def;
