load "astTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "type="; print_type (type_of ``ast$every_exp``); print "\n");
fun capture name tm =
  let val result = rhs (concl (EVAL tm))
  in print (name ^ "="); print_term result; print "\n" end;
val _ = capture "nested" ``ast$every_exp (λe. case e of Var _ => F | _ => T)
  (If (Lit (IntLit 1)) (Con NONE [Lit (IntLit 2); Var (Short «x»)]) (Lit (IntLit 3)))``;
val _ = capture "clauses" ``ast$every_exp (λe. case e of Var _ => F | _ => T)
  (Mat (Lit (IntLit 0)) [(Pany, Lit (IntLit 1)); (Pany, Var (Short «x»))])``;
val _ = capture "funs" ``ast$every_exp (λe. case e of Var _ => F | _ => T)
  (Letrec [(«f», «x», Var (Short «x»))] (Lit (IntLit 0)))``;
val _ = capture "all_good" ``ast$every_exp (λe. case e of Var _ => F | _ => T)
  (Letrec [(«f», «x», Lit (IntLit 1))] (Lit (IntLit 0)))``;
