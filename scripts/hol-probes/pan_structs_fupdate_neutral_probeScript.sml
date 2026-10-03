load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory finite_mapTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL(Q.prove (`FLOOKUP fm x = SOME y ==>
  FUPDATE fm (x, y) = fm`,
  simp [FUPDATE_ELIM, TO_FLOOKUP]));
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = print "fupdate_elim2_statement=";
val _ = print_term(concl original);
val _ = print "\n";
val _ = print("fupdate_elim2_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl original)))) ^ "\n");
val _ = print("fupdate_elim2_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = print("fupdate_elim2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
