load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib source_to_flatProofTheory source_to_flatTheory;
val _ = Globals.linewidth := 1000000;
val s_i1 = ``s_i1 : ('f_orac_st, 'ffi) flatSem$state``;
val theorem_statement = ``
(!cenv s p v env r env' env'' env_i1 ^s_i1 v_i1 st'.
   semanticPrimitives$pmatch cenv s p v env = r ∧
   s_rel genv st' s_i1 ∧
   global_env_inv genv comp_map2 shadowers senv ∧
   genv_c_ok genv.c ∧
   genv_c_tys_ok genv.c genv.tys ∧
   cenv = senv.c ∧
   comp_map2.c = comp_map.c ∧
   env = env' ++ env'' ∧
   s_i1.globals = genv.v ∧
   s = st'.refs ∧
   v_rel genv v v_i1 ∧
   env_rel genv (alist_to_ns env') env_i1
   ⇒
   ?r_i1.
     flatSem$pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 ∧
     match_result_rel genv env'' r r_i1) ∧
  (!cenv s ps vs env r env' env'' env_i1 ^s_i1 vs_i1 st'.
   semanticPrimitives$pmatch_list cenv s ps vs env = r ∧
   global_env_inv genv comp_map2 shadowers senv ∧
   genv_c_ok genv.c ∧
   genv_c_tys_ok genv.c genv.tys ∧
   cenv = senv.c ∧
   comp_map2.c = comp_map.c ∧
   env = env' ++ env'' ∧
   s_i1.globals = genv.v ∧
   s_rel genv st' s_i1 ∧
   s = st'.refs ∧
   LIST_REL (v_rel genv) vs vs_i1 ∧
   env_rel genv (alist_to_ns env') env_i1
   ⇒
   ?r_i1.
     flatSem$pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 = r_i1 ∧
     match_result_rel genv env'' r r_i1)
``;
val _ = (print "pmatch_statement_typed="; Lib.with_flag (Globals.show_types,true) print_term theorem_statement);
