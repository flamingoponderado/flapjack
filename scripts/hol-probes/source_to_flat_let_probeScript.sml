load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail label;
val named = prove(``source_to_flat$compile_exp t env (ast$Let (SOME x) e1 e2) =
  flatLang$Let None (SOME x) (source_to_flat$compile_exp (x::t) env e1)
    (source_to_flat$compile_exp t (env with v := nsBind x (Local None x) env.v) e2)``,
  simp [source_to_flatTheory.compile_exp_def]);
val anonymous = prove(``source_to_flat$compile_exp t env (ast$Let NONE e1 e2) =
  flatLang$Let None NONE (source_to_flat$compile_exp t env e1) (source_to_flat$compile_exp t env e2)``,
  simp [source_to_flatTheory.compile_exp_def]);
val _ = show_thm "named_compile_typed=" named;
val _ = show_thm "anonymous_compile_typed=" anonymous;
val _ = show_thm "optional_bind_typed=" namespaceTheory.nsOptBind_def;
