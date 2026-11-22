(* Capture the exported HOL theorem word_bignum$generated_bignum_stubs_eq
   (`EVAL ``generated_bignum_stubs n`` |> SIMP_RULE std_ss [GSYM ADD_ASSOC]`,
   word_bignumScript.sml:576-577): its hypothesis count, free variables, type
   variables, the inferred (show_types) statement for review, and the same
   statement without type annotations, which scripts/generate-bignum-stubs-eq.py
   renders as the Lean literal. *)
load "word_bignumTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;

val th = word_bignumTheory.generated_bignum_stubs_eq;
val _ = if null (hyp th) then ()
  else raise Fail "generated_bignum_stubs_eq has unexpected hypotheses";
val _ = (print "generated_bignum_stubs_eq_hyps=";
  print (Int.toString (length (hyp th))); print "\n");
val _ = (print "generated_bignum_stubs_eq_free_vars=";
  print (String.concatWith "; "
    (map (fn v => fst (dest_var v) ^ " " ^ type_to_string (type_of v))
      (free_vars (concl th))));
  print "\n");
val _ = (print "generated_bignum_stubs_eq_type_vars=";
  print (String.concatWith "; "
    (map type_to_string (type_vars_in_term (concl th))));
  print "\n");
val _ = (print "generated_bignum_stubs_eq_untyped=";
  print_term (concl th); print "\n");
val _ = show_types := true;
val _ = (print "generated_bignum_stubs_eq_typed=";
  print_term (concl th); print "\n");
