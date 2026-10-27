load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "do_app_typed=" flatSemTheory.do_app_def;
val _ = show_eval "global_alloc=" ``OPTION_MAP (λ(s,r). (s.globals,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := []) (GlobalVarAlloc 2) [])``;
val _ = show_eval "global_init=" ``OPTION_MAP (λ(s,r). (s.globals,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [NONE]) (GlobalVarInit 0) [Litv (IntLit 7)])``;
val _ = show_eval "global_reinit=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [SOME (Litv (IntLit 3))]) (GlobalVarInit 0) [Litv (IntLit 7)])``;
val _ = show_eval "global_lookup=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [SOME (Litv (IntLit 7))]) (GlobalVarLookup 0) [])``;
val _ = show_eval "global_missing=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [NONE]) (GlobalVarLookup 0) [])``;
val _ = show_eval "tag_match=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (TagLenEq 2 1) [Conv (SOME (2,NONE)) [Litv (IntLit 7)]])``;
val _ = show_eval "tag_mismatch=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (TagLenEq 3 1) [Conv (SOME (2,NONE)) [Litv (IntLit 7)]])``;
val _ = show_eval "tuple_length=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (LenEq 1) [Conv NONE [Litv (IntLit 7)]])``;
val _ = show_eval "field_index=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (El 0) [Conv NONE [Litv (IntLit 7)]])``;
val _ = show_eval "ref_field=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 7))]) (El 0) [Loc T 0])``;
val _ = show_eval "ref_bad_index=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 7))]) (El 1) [Loc T 0])``;
val _ = show_eval "identity=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) Id [Litv (IntLit 7)])``;
