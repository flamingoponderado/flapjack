load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
val theorem_full = GEN_ALL (Q.prove (
`convert_code (ctxt with locals updated_by f) code = convert_code ctxt code`,
  simp [convert_code_def]));
val _ = if null(hyp theorem_full) andalso null(free_vars(concl theorem_full)) then () else raise Fail "open theorem";
val _ = print "convert_code_locals_upd_statement=";
val _ = print_term(concl theorem_full);
val _ = print "\n";
val _ = print("convert_code_locals_upd_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_full))) ^ "\n");
val _ = print("convert_code_locals_upd_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_full)))) ^ "\n");
