load "bossLib"; load "preamble"; load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val _ = observe "adrtc_scratch" ``let s = (([(NONE,SOME 2)],[(NONE,NONE)],[(NONE,SOME 3)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list) in ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s ++ FST(SND s) ++ SND(SND s))))``;
val _ = observe "adrtc_first" ``let s = (([(SOME 1,SOME 2)],[],[(NONE,SOME 3);(NONE,NONE)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list) in ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s ++ FST(SND s) ++ SND(SND s))))``;
val _ = observe "adrtc_middle" ``let s = (([],[(SOME 1,SOME 2)],[(NONE,SOME 3);(NONE,NONE)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list) in ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s ++ FST(SND s) ++ SND(SND s))))``;
val _ = observe "adrtc_last" ``let s = (([],[(SOME 1,NONE)],[(NONE,SOME 2);(NONE,SOME 3);(NONE,NONE)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list) in ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s ++ FST(SND s) ++ SND(SND s))))``;
