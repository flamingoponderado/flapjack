load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory panSemTheory panPropsTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL (Q.prove (`evaluate (p, s) = (res, s') ==>
  s'.structs = s.structs ∧ s'.code = s.code`,
  rw [] \\ imp_res_tac evaluate_invariants));
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = print "evaluate_structs_code_inv_statement=";
val _ = print_term(concl original);
val _ = print "\n";
val _ = print("evaluate_structs_code_inv_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl original)))) ^ "\n");
val _ = print("evaluate_structs_code_inv_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = print("evaluate_structs_code_inv_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
