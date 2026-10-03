load "preamble"; load "word_simpProofTheory";
open HolKernel Parse bossLib preamble wordSemTheory word_simpTheory word_simpProofTheory;
val _ = Globals.linewidth := 1000000;
fun check name th original =
  if null(hyp th) andalso aconv (concl(GEN_ALL th)) (concl(GEN_ALL original))
  then () else raise Fail ("replay " ^ name);
fun closed name th =
  if null(hyp th) then () else raise Fail ("open " ^ name);
(* compile_exp_thm: replay of the original one-line proof. *)
val compile_exp_thm_replay = prove(concl compile_exp_thm,
    fs [word_simpTheory.compile_exp_def,evaluate_Seq_assoc,
        evaluate_const_fp, evaluate_simp_duplicate_if,
        evaluate_simp_push_out_if]);
val _ = check "compile_exp_thm" compile_exp_thm_replay compile_exp_thm;
val _ = (print "compile_exp_thm_statement="; print_term(concl(GEN_ALL compile_exp_thm_replay)); print "\n");
val _ = print("compile_exp_thm_hypotheses=" ^ Int.toString(length(hyp compile_exp_thm_replay)) ^ "\n");
(* evaluate_Seq_assoc: replay of the original one-line proof. *)
val evaluate_Seq_assoc_replay = prove(concl evaluate_Seq_assoc,
  fs [evaluate_Seq_assoc_lemma,evaluate_def]);
val _ = check "evaluate_Seq_assoc" evaluate_Seq_assoc_replay evaluate_Seq_assoc;
val _ = (print "evaluate_Seq_assoc_statement="; print_term(concl(GEN_ALL evaluate_Seq_assoc_replay)); print "\n");
(* Exported statements of the pass-level evaluation theorems. *)
val _ = closed "evaluate_simp_push_out_if" evaluate_simp_push_out_if;
val _ = (print "evaluate_simp_push_out_if_statement="; print_term(concl(GEN_ALL evaluate_simp_push_out_if)); print "\n");
val _ = closed "evaluate_simp_duplicate_if" evaluate_simp_duplicate_if;
val _ = (print "evaluate_simp_duplicate_if_statement="; print_term(concl(GEN_ALL evaluate_simp_duplicate_if)); print "\n");
val _ = closed "evaluate_const_fp" evaluate_const_fp;
val _ = (print "evaluate_const_fp_statement="; print_term(concl(GEN_ALL evaluate_const_fp)); print "\n");
val _ = closed "evaluate_const_fp_loop" evaluate_const_fp_loop;
val _ = (print "evaluate_const_fp_loop_statement="; print_term(concl(GEN_ALL evaluate_const_fp_loop)); print "\n");
val _ = closed "evaluate_sf_gc_consts" evaluate_sf_gc_consts;
val _ = (print "evaluate_sf_gc_consts_statement="; print_term(concl(GEN_ALL evaluate_sf_gc_consts)); print "\n");
val _ = closed "evaluate_gc_fun_const_ok" evaluate_gc_fun_const_ok;
val _ = (print "evaluate_gc_fun_const_ok_statement="; print_term(concl(GEN_ALL evaluate_gc_fun_const_ok)); print "\n");
val _ = closed "evaluate_drop_consts" evaluate_drop_consts;
val _ = (print "evaluate_drop_consts_statement="; print_term(concl(GEN_ALL evaluate_drop_consts)); print "\n");
val _ = closed "evaluate_Loop_body_cong_gc" evaluate_Loop_body_cong_gc;
val _ = (print "evaluate_Loop_body_cong_gc_statement="; print_term(concl(GEN_ALL evaluate_Loop_body_cong_gc)); print "\n");
