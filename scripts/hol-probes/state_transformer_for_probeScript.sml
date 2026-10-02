load "state_transformerTheory";
open HolKernel Parse bossLib state_transformerTheory;
val _ = Globals.linewidth := 100000;
fun out label q = let val th = EVAL q in
 if null (hyp th) then (print(label ^ "="); print_term(snd(boolSyntax.dest_eq(concl th))); print "\n")
 else raise Fail "undischarged assumptions" end;
val _ = out "for_ascending" ``FOR (1,3,\i s. ((),s ++ [i])) ([]:num list)``;
val _ = out "for_descending" ``FOR (3,1,\i s. ((),s ++ [i])) ([]:num list)``;
val _ = out "for_equal_zero" ``FOR (0,0,\i s. ((),s ++ [i])) ([]:num list)``;
val _ = out "for_descending_zero" ``FOR (2,0,\i s. ((),s ++ [i])) ([9]:num list)``;
