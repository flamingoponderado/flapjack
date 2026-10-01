load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
fun out label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
val _ = out "rc_alloc1" ``(is_alloc_var 1,is_alloc_var (1+4),is_stack_var 1,is_stack_var (1+4))``;
val _ = out "rc_stack3" ``(is_alloc_var 3,is_alloc_var (3+4),is_stack_var 3,is_stack_var (3+4))``;
val _ = out "rc_physical0" ``(is_alloc_var 0,is_alloc_var (0+4),is_stack_var 0,is_stack_var (0+4))``;
val _ = out "rc_physical2" ``(is_alloc_var 2,is_alloc_var (2+4),is_stack_var 2,is_stack_var (2+4))``;
val _ = out "rc_alloc5" ``(is_alloc_var 5,is_alloc_var (5+4),is_stack_var 5,is_stack_var (5+4))``;
val _ = out "rc_stack7" ``(is_alloc_var 7,is_alloc_var (7+4),is_stack_var 7,is_stack_var (7+4))``;
val _ = out "rc_large_alloc" ``(is_alloc_var 1000000000000000000000000000001,is_alloc_var (1000000000000000000000000000001+4),is_stack_var 1000000000000000000000000000001,is_stack_var (1000000000000000000000000000001+4))``;
val _ = out "rc_large_stack" ``(is_alloc_var 1000000000000000000000000000003,is_alloc_var (1000000000000000000000000000003+4),is_stack_var 1000000000000000000000000000003,is_stack_var (1000000000000000000000000000003+4))``;
(* The source lemmas are local. Recheck their literal statements with the original source proof, rather than claim an exported DB theorem. *)
val alloc_add_source = prove (``!na. is_alloc_var na ==> is_alloc_var (na+4)``, full_simp_tac(srw_ss())[is_alloc_var_def] >> (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS >> full_simp_tac(srw_ss())[] >> pop_assum (qspecl_then [`na`,`4`] assume_tac) >> rev_full_simp_tac(srw_ss())[]));
val stack_add_source = prove (``!na. is_stack_var na ==> is_stack_var (na+4)``, full_simp_tac(srw_ss())[is_stack_var_def] >> (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS >> full_simp_tac(srw_ss())[] >> pop_assum (qspecl_then [`na`,`4`] assume_tac) >> rev_full_simp_tac(srw_ss())[]));
val _ = (print "rc_alloc_source_replay=";print_thm alloc_add_source;print "\n");
val _ = (print "rc_stack_source_replay=";print_thm stack_add_source;print "\n");
