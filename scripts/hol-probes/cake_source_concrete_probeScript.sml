load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "type="; print_type (type_of ``semanticPrimitives$concrete_v``); print "\n");
val literal = rhs (concl (EVAL ``semanticPrimitives$concrete_v (Litv (IntLit 1))``));
val _ = (print "literal="; print_term literal; print "\n");
val location = rhs (concl (EVAL ``semanticPrimitives$concrete_v (Loc F 0)``));
val _ = (print "location="; print_term location; print "\n");
val tree = rhs (concl (EVAL ``semanticPrimitives$concrete_v
  (Conv NONE [Litv (IntLit 1); Vectorv [Loc T 2]])``));
val _ = (print "tree="; print_term tree; print "\n");
val closure = rhs (concl (EVAL ``semanticPrimitives$concrete_v
  (Closure (ARB:v sem_env) «x» (Var (Short «x»)))``));
val _ = (print "closure="; print_term closure; print "\n");
val nested_closure = rhs (concl (EVAL ``semanticPrimitives$concrete_v
  (Conv NONE [Litv (IntLit 1); Vectorv [Closure (ARB:v sem_env) «x» (Var (Short «x»))]])``));
val _ = (print "nested_closure="; print_term nested_closure; print "\n");
val environment = rhs (concl (EVAL ``semanticPrimitives$concrete_v (Env (ARB:v sem_env) (0,0))``));
val _ = (print "environment="; print_term environment; print "\n");
