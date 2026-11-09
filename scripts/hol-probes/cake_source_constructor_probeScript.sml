load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "find_type="; print_type (type_of ``semanticPrimitives$find_recfun``); print "\n");
val _ = (print "build_env_type="; print_type (type_of ``semanticPrimitives$build_rec_env``); print "\n");
val same_type = rhs (concl (EVAL ``semanticPrimitives$same_type (TypeStamp «A» 7) (TypeStamp «B» 7)``));
val _ = (print "same_type="; print_term same_type; print "\n");
val same_ctor = rhs (concl (EVAL ``semanticPrimitives$same_ctor (TypeStamp «A» 7) (TypeStamp «B» 7)``));
val _ = (print "same_ctor="; print_term same_ctor; print "\n");
val exn_type = rhs (concl (EVAL ``semanticPrimitives$same_type (ExnStamp 1) (ExnStamp 2)``));
val _ = (print "exn_type="; print_term exn_type; print "\n");
val check = rhs (concl (EVAL ``semanticPrimitives$do_con_check
  (Bind [(«A»,(1,TypeStamp «A» 7))] []) (SOME (Short «A»)) 1``));
val _ = (print "check="; print_term check; print "\n");
val wrong_arity = rhs (concl (EVAL ``semanticPrimitives$do_con_check
  (Bind [(«A»,(1,TypeStamp «A» 7))] []) (SOME (Short «A»)) 0``));
val _ = (print "wrong_arity="; print_term wrong_arity; print "\n");
val build = rhs (concl (EVAL ``semanticPrimitives$build_conv
  (Bind [(«A»,(1,TypeStamp «A» 7))] []) (SOME (Short «A»)) []``));
val _ = (print "build="; print_term build; print "\n");
