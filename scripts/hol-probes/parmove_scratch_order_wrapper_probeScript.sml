load "bossLib";
load "parmoveTheory";
open HolKernel Parse boolLib bossLib parmoveTheory miscTheory;
val _ = Globals.linewidth := 1000;
val _ = print "pso_original_statement=";
val _ = print_term (concl (DB.fetch "parmove" "parmove_not_use_temp_before_assign"));
val _ = print "\n";
fun observe label moves =
  let val term = ``let out = parmove ^moves in
    (out, find_index NONE (MAP SND out) 0, find_index NONE (MAP FST out) 0,
     windmill ^moves,
     case find_index NONE (MAP SND out) 0 of NONE => T | SOME i =>
       case find_index NONE (MAP FST out) 0 of NONE => F | SOME j => ~(i <= j))``
  in print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n" end;
val _ = observe "pso_empty" ``([]:(num # num) list)``;
val _ = observe "pso_self" ``[(0:num,0:num)]``;
val _ = observe "pso_chain" ``[(0:num,1:num);(1,2)]``;
val _ = observe "pso_swap" ``[(0:num,1:num);(1,0)]``;
val _ = observe "pso_cycle" ``[(0:num,1:num);(1,2);(2,0)]``;
val _ = observe "pso_shared_source" ``[(0:num,2:num);(1,2)]``;
val _ = observe "pso_bool_swap" ``[(F,T);(T,F)]``;
val _ = observe "pso_duplicate_boundary" ``[(0:num,1:num);(0,2)]``;
