load "bossLib";
load "parmoveTheory";
open HolKernel Parse boolLib bossLib parmoveTheory;
val _ = Globals.linewidth := 1000;
val _ = print "smi_original_statement=";
val _ = print_term (concl (DB.fetch "parmove" "step_MAP_INJ"));
val _ = print "\n";
val rename = ``\x:bool option. case x of NONE => NONE | SOME b => SOME (if b then 20:num else 10)``;
fun observe label first second =
  (print (label ^ "=");
   print_term (rhs (concl (EVAL ``(map_state ^rename ^first, map_state ^rename ^second)``)));
   print "\n");
val _ = observe "smi_remove_self" ``(([(SOME F,SOME F)],[],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)`` ``(([],[],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)``;
val _ = observe "smi_start" ``(([(SOME F,SOME T)],[],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)`` ``(([],[(SOME F,SOME T)],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)``;
val _ = observe "smi_extend" ``(([(SOME T,SOME F)],[(SOME F,SOME T)],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)`` ``(([],[(SOME T,SOME F);(SOME F,SOME T)],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)``;
val _ = observe "smi_save" ``(([],[(SOME F,SOME T)],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)`` ``(([],[(SOME F,NONE)],[(NONE,SOME T)]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)``;
val _ = observe "smi_emit_head" ``(([],[(SOME T,SOME F);(SOME F,SOME F)],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)`` ``(([],[(SOME F,SOME F)],[(SOME T,SOME F)]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)``;
val _ = observe "smi_emit_last" ``(([],[(SOME F,SOME T)],[]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)`` ``(([],[],[(SOME F,SOME T)]) : (bool option # bool option) list # (bool option # bool option) list # (bool option # bool option) list)``;
val collapse = ``\x:num option. case x of NONE => NONE | SOME n => SOME F``;
val _ = print "smi_scoped_collapse=";
val _ = print_term (rhs (concl (EVAL ``(map_state ^collapse (([(SOME 3,SOME 3)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list),
  ^collapse (SOME 4) = ^collapse (SOME 5))``)));
val _ = print "\n";
val _ = print "smi_scoped_injectivity=";
val _ = print_term (concl (prove (``inj_on_state ^collapse (([(SOME 3,SOME 3)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``,
  simp [inj_on_state_def,state_to_list_def] >> gen_tac >> Cases_on `x` >> simp [])));
val _ = print "\n";
