(*
  Direct HOL statement observations for the case structure of
  loop_to_wordProof$compile_correct
  (cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97) and for the
  rebound wordSem evaluate_ind/evaluate_def
  (cakeml/compiler/backend/semantics/wordSemScript.sml:1367-1370).

  compile_correct is stated as the conclusion of loopSem$evaluate_ind
  specialised to the lambda `goal`.  This probe rebuilds that `ind_thm`
  exactly as the source does (ISPEC, PBETA_CONV, REWRITE_RULE []), with the
  goal taken from compile_correct itself, and prints each constructor's
  antecedent conjunct.  These conjuncts are the statements that the Lean case
  theorems in Flapjack/Pancake/LoopToWord/Proofs/CompileCorrect/ render.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
load "loopSemTheory";
load "loop_to_wordProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = set_trace "Unicode" 0;
val _ = Globals.linewidth := 150;

val cc = loop_to_wordProofTheory.compile_correct;
val (v0, b0) = dest_forall (concl cc);
val (v1, body) = dest_forall b0;
val goal = pairSyntax.mk_pabs (pairSyntax.mk_pair (v0, v1), body);
val ind_thm = loopSemTheory.evaluate_ind |> ISPEC goal
  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
val _ = if aconv (concl cc) (snd (dest_imp (concl ind_thm)))
        then print "cc_ind_thm_conclusion_is_compile_correct=T\n"
        else print "cc_ind_thm_conclusion_is_compile_correct=F\n";

fun is_loop_eval t =
  let val (c, _) = strip_comb t
      val {Name, Thy, ...} = dest_thy_const c
  in Name = "evaluate" andalso Thy = "loopSem" end handle HOL_ERR _ => false;

fun core t =
  let val (_, b) = strip_forall t in
    if is_imp b andalso is_forall (snd (dest_imp b)) then core (snd (dest_imp b)) else b
  end;

fun ctor_of conj =
  let val e = find_term is_loop_eval (fst (dest_imp (core conj)))
      val prog = fst (pairSyntax.dest_pair (rand e))
  in #Name (dest_thy_const (fst (strip_comb prog))) end;

val wanted = ["Skip", "Fail", "Tick", "Continue", "Break", "Mark", "Return", "Raise", "Seq"];
val cases = strip_conj (fst (dest_imp (concl ind_thm)));
val _ = List.app (fn c =>
  let val n = ctor_of c in
    if List.exists (fn w => w = n) wanted then
      (print ("cc_case_" ^ n ^ "="); print_term c; print "\n")
    else ()
  end) cases;

val _ = (print "ws_evaluate_ind="; print_term (concl wordSemTheory.evaluate_ind); print "\n");
val _ = (print "ws_evaluate_def="; print_term (concl wordSemTheory.evaluate_def); print "\n");
val _ = print "ws_end=T\n";
