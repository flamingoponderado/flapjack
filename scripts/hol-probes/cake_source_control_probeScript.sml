load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "if_type="; print_type (type_of ``semanticPrimitives$do_if``); print "\n");
val _ = (print "combine_type="; print_type (type_of ``semanticPrimitives$combine_dec_result``); print "\n");
val if_true = rhs (concl (EVAL ``semanticPrimitives$do_if (semanticPrimitives$Boolv T) (1:num) 2``));
val _ = (print "if_true="; print_term if_true; print "\n");
val if_false = rhs (concl (EVAL ``semanticPrimitives$do_if (semanticPrimitives$Boolv F) (1:num) 2``));
val _ = (print "if_false="; print_term if_false; print "\n");
val if_invalid = rhs (concl (EVAL ``semanticPrimitives$do_if (Litv (IntLit 0)) (1:num) 2``));
val _ = (print "if_invalid="; print_term if_invalid; print "\n");
val and_true = rhs (concl (EVAL ``semanticPrimitives$do_log Andalso (semanticPrimitives$Boolv T) (Var (Short «x»))``));
val _ = (print "and_true="; print_term and_true; print "\n");
val and_false = rhs (concl (EVAL ``semanticPrimitives$do_log Andalso (semanticPrimitives$Boolv F) (Var (Short «x»))``));
val _ = (print "and_false="; print_term and_false; print "\n");
val constructors = rhs (concl (EVAL ``nsLookup
  (semanticPrimitives$build_tdefs 5 [([],«t»,[(«A»,[])]); ([],«u»,[(«A»,[])])]) (Short «A»)``));
val _ = (print "constructors="; print_term constructors; print "\n");
val duplicates = rhs (concl (EVAL ``semanticPrimitives$check_dup_ctors ([],«t»,[(«A»,[]); («A»,[])])``));
val _ = (print "duplicates="; print_term duplicates; print "\n");
val failure = rhs (concl (EVAL ``semanticPrimitives$combine_dec_result (ARB:v sem_env)
  (Rerr (Rraise (3:num)) : (v sem_env,num) result)``));
val _ = (print "failure="; print_term failure; print "\n");
