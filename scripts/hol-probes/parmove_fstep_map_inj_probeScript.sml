load "bossLib";
load "parmoveTheory";
open HolKernel Parse boolLib bossLib parmoveTheory;
val _ = Globals.linewidth := 1000;
val _ = print "pfm_statement=";
val _ = print_term (concl (DB.fetch "parmove" "fstep_MAP_INJ"));
val _ = print "\n";
val rename = ``\x:num option. case x of NONE => NONE | SOME n => SOME (n = 1)``;
val stateType = ``:(num option # num option) list # (num option # num option) list # (num option # num option) list``;
fun observe label state =
  let val state = inst (match_type (type_of state) stateType) state
      val valid = prove (``inj_on_state ^rename ^state``,
        rw [inj_on_state_def,state_to_list_def] >> fs [] >>
        rpt gen_tac >> Cases_on `x` >> simp [] >> rw [] >> fs [])
      val term = ``(T,
     fstep (map_state ^rename ^state), map_state ^rename (fstep ^state))``
  in print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n" end;
val _ = observe "pfm_empty" ``([],[],[]):(num option # num option) list # (num option # num option) list # (num option # num option) list``;
val _ = observe "pfm_self" ``([(SOME (0:num),SOME (0:num))],[],[])``;
val _ = observe "pfm_start" ``([(SOME (0:num),SOME (1:num))],[],[])``;
val _ = observe "pfm_found" ``([(SOME (0:num),SOME (1:num))],[(SOME (1:num),SOME (0:num))],[])``;
val _ = observe "pfm_emit" ``([],[(SOME (1:num),SOME (0:num))],[])``;
val _ = observe "pfm_cycle" ``([],[(SOME (1:num),SOME (0:num));(SOME (0:num),SOME (1:num))],[])``;
val _ = observe "pfm_no_cycle" ``([],[(SOME (1:num),SOME (0:num));(SOME (0:num),SOME (0:num))],[])``;
val _ = observe "pfm_temp" ``([(NONE,SOME (0:num))],[],[(SOME (1:num),NONE)])``;
