load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;

(* Direct original semantic operations, including repeated destinations where
   windmill does not hold. parsem/seqsem/sem retain generic num keys, while
   eqenv has option keys. Function UPDATE_LIST is head-before-tail, last wins. *)
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
fun print_simp label q =
  let val th = SIMP_CONV (srw_ss()) [eqenv_def, optionTheory.FORALL_OPTION] q
  in (print (label ^ "="); print_term (rconc th); print "\n") end;

val _ = print_eval "sem_windmill" ``parmove$windmill [(1:num,2);(2,1)]``;
val _ = print_eval "sem_repeated" ``parmove$windmill [(1:num,2);(1,3)]``;
val _ = print_eval "sem_parallel_swap1" ``parmove$parsem [(1,2);(2,1)] (\n:num. n+10) 1``;
val _ = print_eval "sem_parallel_swap2" ``parmove$parsem [(1,2);(2,1)] (\n:num. n+10) 2``;
val _ = print_eval "sem_sequential_swap2" ``parmove$seqsem [(1,2);(2,1)] (\n:num. n+10) 2``;
val _ = print_eval "sem_parallel_last" ``parmove$parsem [(1,2);(1,3)] (\n:num. n+10) 1``;
val _ = print_eval "sem_sequential_last" ``parmove$seqsem [(1,2);(1,3)] (\n:num. n+10) 1``;
val _ = print_eval "sem_untouched" ``parmove$parsem [(1,2);(1,3)] (\n:num. n+10) 7``;
val _ = print_eval "sem_state_first"
  ``parmove$sem ([(1,2)],[(2,3)],[(3,4);(4,5)]) (\n:num. n+10) 1``;
val _ = print_eval "sem_state_second"
  ``parmove$sem ([(1,2)],[(2,3)],[(3,4);(4,5)]) (\n:num. n+10) 2``;
val _ = print_simp "sem_ignore_temp"
  ``parmove$eqenv (\r:num option. if IS_SOME r then 7 else 0)
      (\r:num option. if IS_SOME r then 7 else 99)``;
val _ = print_simp "sem_real_difference"
  ``parmove$eqenv (\r:num option. if IS_SOME r then 7 else 0)
      (\r:num option. if IS_SOME r then 8 else 0)``;
