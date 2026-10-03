load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory;
val _ = Globals.linewidth := 1000000;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");
fun typed_statement label th =
  (show_types := true;
   print (label ^ "="); print_term (concl th); print "\n";
   show_types := false);
fun type_list label th =
  (show_types := true;
   print (label ^ "=");
   app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";"))
     (fst (strip_forall (concl th)) @ free_vars (concl th));
   print "\n";
   show_types := false);

(* Exported originals of stack_to_labProofScript.sml:2741-3025. *)
val _ = checked "flatten_call_correct_statement" (GEN_ALL flatten_call_correct);
val _ = typed_statement "flatten_call_correct_statement_typed" (GEN_ALL flatten_call_correct);
val _ = type_list "flatten_call_correct_statement_types" (GEN_ALL flatten_call_correct);
val _ = checked "halt_assum_def_statement" halt_assum_def;
val _ = typed_statement "halt_assum_def_statement_typed" halt_assum_def;
val _ = type_list "halt_assum_def_statement_types" halt_assum_def;
val _ = checked "flatten_semantics_statement" (GEN_ALL flatten_semantics);
val _ = typed_statement "flatten_semantics_statement_typed" (GEN_ALL flatten_semantics);
val _ = type_list "flatten_semantics_statement_types" (GEN_ALL flatten_semantics);
