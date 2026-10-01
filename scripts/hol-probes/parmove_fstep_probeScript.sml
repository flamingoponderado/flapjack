load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;

(* Original deterministic scheduler, parmoveScript.sml:526-546.
   All queries are direct fstep equalities at num option registers; NONE is
   retained as the temporary, including malformed/unconstrained input states.
   No substitute parallel-move evaluator or wf premise is used. *)
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val _ = print_eval "fs_final"
  ``parmove$fstep ([],[],[(SOME 8,SOME 9)] : (num option # num option) list) =
    ([],[],[(SOME 8,SOME 9)])``;
val _ = print_eval "fs_self"
  ``parmove$fstep ([(SOME 1,SOME 1);(SOME 2,SOME 3)],[],[] : (num option # num option) list) =
    ([(SOME 2,SOME 3)],[],[])``;
val _ = print_eval "fs_start"
  ``parmove$fstep ([(SOME 1,SOME 2);(SOME 3,SOME 4)],[],[] : (num option # num option) list) =
    ([(SOME 3,SOME 4)],[(SOME 1,SOME 2)],[])``;
val _ = print_eval "fs_first"
  ``parmove$fstep ([(SOME 7,SOME 8);(SOME 3,SOME 1);(SOME 4,SOME 1)],[(SOME 1,SOME 2)],[] : (num option # num option) list) =
    ([(SOME 7,SOME 8);(SOME 4,SOME 1)],[(SOME 3,SOME 1);(SOME 1,SOME 2)],[])``;
val _ = print_eval "fs_single"
  ``parmove$fstep ([(SOME 7,SOME 8)],[(SOME 1,SOME 2)],[(SOME 8,SOME 9)] : (num option # num option) list) =
    ([(SOME 7,SOME 8)],[],[(SOME 1,SOME 2);(SOME 8,SOME 9)])``;
val _ = print_eval "fs_chain"
  ``parmove$fstep ([],[(SOME 1,SOME 2);(SOME 2,SOME 3);(SOME 3,SOME 4)],[] : (num option # num option) list) =
    ([],[(SOME 2,SOME 3);(SOME 3,SOME 4)],[(SOME 1,SOME 2)])``;
val _ = print_eval "fs_cycle"
  ``parmove$fstep ([],[(SOME 1,SOME 2);(SOME 2,SOME 1)],[] : (num option # num option) list) =
    ([],[(SOME 2,NONE)],[(SOME 1,SOME 2);(NONE,SOME 1)])``;
val _ = print_eval "fs_cycle_long"
  ``parmove$fstep ([],[(SOME 1,SOME 2);(SOME 2,SOME 3);(SOME 3,SOME 1)],[(SOME 8,SOME 9)] : (num option # num option) list) =
    ([],[(SOME 2,SOME 3);(SOME 3,NONE)],[(SOME 1,SOME 2);(NONE,SOME 1);(SOME 8,SOME 9)])``;
val _ = print_eval "fs_temp_match"
  ``parmove$fstep ([(SOME 2,NONE)],[(NONE,SOME 1)],[] : (num option # num option) list) =
    ([],[(SOME 2,NONE);(NONE,SOME 1)],[])``;
val _ = print_eval "fs_temp_self"
  ``parmove$fstep ([(NONE,NONE)],[],[] : (num option # num option) list) = ([],[],[])``;
