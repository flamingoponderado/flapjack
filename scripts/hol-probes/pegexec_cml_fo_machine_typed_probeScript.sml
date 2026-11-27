(* Typed source declarations for the first-order PEG machine datatypes and
   driver definitions in pegexec_cml_fo.  Datatypes are captured through their
   case equations so the constructor argument types are visible. *)
load "preamble";
load "pegexec_cml_foTheory";
open HolKernel Parse boolLib bossLib;
open preamble pegexec_cml_foTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun showType label ty = (print (label ^ "=");
  Lib.with_flag (Globals.show_types, true)
    print_term (concl (TypeBase.case_def_of ty));
  print "\n");

val _ = showType "pegresult_typed" ``:('a, 'c, 'e) pegresult``;
val _ = showType "kont_fo_typed" ``:kont_fo``;
val _ = showType "evalcase_fo_typed" ``:evalcase_fo``;
val _ = showType "peg_fo_typed" ``:peg_fo``;
val _ = show "sloc_pexec_def_typed" pegexec_cml_foTheory.sloc_pexec_def;
val _ = show "corestep_fo_body_def_typed" pegexec_cml_foTheory.corestep_fo_body_def;
val _ = show "run_peg_fo_def_typed" pegexec_cml_foTheory.run_peg_fo_def;
val _ = show "peg_exec_fuel_fo_def_typed" pegexec_cml_foTheory.peg_exec_fuel_fo_def;
val _ = show "peg_exec_core_fuel_def_typed" pegexec_cml_foTheory.peg_exec_core_fuel_def;
val _ = show "mlstring_nonempty_strlen_typed" pegexec_cml_foTheory.mlstring_nonempty_strlen;
