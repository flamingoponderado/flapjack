(* Direct original HOL observations for stackSem$copy_words_def (y19g.11.2.2).
   Run read-only from the prebuilt compiler/backend/semantics theory directory
   through regenerate.sh. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = observe "normal_continue" ``case stackSem$copy_words 0 (0w:word8) 100w
  ([0x81w;0x11w;0x22w;0x33w;0x44w;0x55w;0x66w;0x77w;0x01w]:word8 list) UNIV
  (K (Loc 9 9)) of NONE => NONE | SOME (a,m) => SOME (a, m 0w, m 1w, m 2w, m 6w, m 7w)``;
val _ = observe "stops_early" ``case stackSem$copy_words 0 (0w:word8) 100w
  ([0x7Fw;0x0Aw;0x0Bw;0x0Cw;0x0Dw;0x0Ew;0x0Fw]:word8 list) UNIV
  (K (Loc 9 9)) of NONE => NONE | SOME (a,m) => SOME (a, m 0w, m 1w, m 5w, m 6w)``;
val _ = observe "zero_pattern" ``case stackSem$copy_words 0 (0w:word8) 100w
  ([0x81w;0x11w;0x22w;0x33w;0x44w;0x55w;0x66w;0x77w;0x00w]:word8 list) UNIV
  (K (Loc 9 9)) of NONE => NONE | SOME (a,m) => SOME (a, m 0w)``;
val _ = observe "out_of_range" ``case stackSem$copy_words 5 (0w:word8) 100w
  ([0x01w;0x02w]:word8 list) UNIV
  (K (Loc 9 9)) of NONE => NONE | SOME (a,m) => SOME (a, m 0w)``;
