load "flat_to_closTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "has_install_typed=" closLangTheory.has_install_def;
val _ = show_thm "interp_el_typed=" clos_interpTheory.clos_interp_el_def;
val _ = show_thm "interp_rev_typed=" clos_interpTheory.clos_interp_rev_def;
val _ = show_thm "interpreter_body_typed=" clos_interpTheory.clos_interpreter_body_def;
val _ = show_thm "interpreter_typed=" clos_interpTheory.clos_interpreter_def;
val _ = show_thm "compile_init_typed=" clos_interpTheory.compile_init_def;
val _ = show_thm "attach_interpreter_typed=" clos_interpTheory.attach_interpreter_def;
val _ = show_thm "compile_prog_typed=" flat_to_closTheory.compile_prog_def;
val _ = show_thm "insert_interp_typed=" clos_interpTheory.insert_interp_def;
val _ = show_thm "inc_compile_decs_typed=" flat_to_closTheory.inc_compile_decs_def;
