load "preamble";
load "panLangTheory";
open HolKernel Parse bossLib preamble panLangTheory;
val _ = Globals.linewidth := 1000000;
fun binders tm =
 if is_forall tm then let val (v,b) = dest_forall tm in v :: binders b end
 else if is_conj tm then let val (a,b) = dest_conj tm in binders a @ binders b end
 else [];
val theorem_full = GEN_ALL is_wf_shape_def;
val _ = if null(hyp theorem_full) andalso null(free_vars(concl theorem_full)) then () else raise Fail "open theorem";
val _ = print "is_wf_shape_def_statement=";
val _ = print_term(concl theorem_full);
val _ = print "\n";
val _ = print("is_wf_shape_def_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_full))) ^ "\n");
val _ = print("is_wf_shape_def_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (binders(concl theorem_full))) ^ "\n");
val theorem_fields = GEN_ALL is_wf_flds_def;
val _ = if null(hyp theorem_fields) andalso null(free_vars(concl theorem_fields)) then () else raise Fail "open field theorem";
val _ = print "is_wf_flds_def_statement=";
val _ = print_term(concl theorem_fields);
val _ = print "\n";
val _ = print("is_wf_flds_def_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_fields))) ^ "\n");
val _ = print("is_wf_flds_def_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (binders(concl theorem_fields))) ^ "\n");
fun emit label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = emit "nat_zero_present" ``is_wf_shape [(strlit "x", 0:num)] (Named (strlit "x"))``;
val _ = emit "bool_false_present" ``is_wf_shape [(strlit "x", F)] (Named (strlit "x"))``;
val _ = emit "bool_false_nested" ``is_wf_shape [(strlit "x", F)] (Comb [One;Named(strlit "x");Comb[]])``;
val _ = emit "nat_nested_missing" ``is_wf_shape [(strlit "x", 0:num)] (Comb [Named(strlit "x");Named(strlit "y")])``;
val _ = emit "generic_fields_present" ``is_wf_flds [(strlit "x", F)] [(0:num, Named(strlit "x"))]``;
val _ = emit "generic_fields_missing" ``is_wf_flds [(strlit "x", F)] [(F, Named(strlit "y"))]``;
