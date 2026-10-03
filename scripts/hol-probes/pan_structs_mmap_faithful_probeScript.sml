load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory panSemTheory;
val _ = Globals.linewidth := 1000000;
(* Original local theorem statement and proof replayed verbatim below. *)
val replay = Q.prove (`!es vs. OPT_MMAP (eval s) es = SOME vs /\
  (!e. MEM e es ==> (!v. eval s e = SOME v ==>
    eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v))) ==>
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt es) = SOME (MAP convert_v vs)`,
Induct
  >> simp [compile_exp_def, DISJ_IMP_THM, FORALL_AND_THM]
  >> rw []
  >> simp []);
val original = GEN_ALL replay;
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = print "compile_exp_correct_mmap_helper_statement=";
val _ = print_term(concl original);
val _ = print "\n";
val _ = print("compile_exp_correct_mmap_helper_types=" ^ String.concatWith ";" (map (fn v => term_to_string v ^ ":" ^ type_to_string(type_of v)) (#1(strip_forall(concl original)))) ^ "\n");
val _ = print("compile_exp_correct_mmap_helper_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = print("compile_exp_correct_mmap_helper_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
