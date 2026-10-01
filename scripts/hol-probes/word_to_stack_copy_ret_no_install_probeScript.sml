load "preamble";
load "word_to_stackTheory";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory stackPropsTheory;
fun out label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
(* The source theorem is local: directly evaluate its full iff and output value. *)
val _ = out "crni_zero_bad" ``let kont=(Install 0 1 2 3 4:64 stackLang$prog) in let p=copy_ret F F (9,0,T) [1;2] kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_plain_good" ``let kont=(Skip:64 stackLang$prog) in let p=copy_ret F F (1,0,F) [1;2] kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_handler_bad" ``let kont=(Install 0 1 2 3 4:64 stackLang$prog) in let p=copy_ret F T (1,7,[T;F]) [1;2] kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_perf_good" ``let kont=(Skip:1 stackLang$prog) in let p=copy_ret T T (0,7,[T;F]) [T;F] kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_perf_bad" ``let kont=(Install 0 1 2 3 4:1 stackLang$prog) in let p=copy_ret T F (0,7,T) [T;F] kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_option_tail_handler" ``let kont=(Call NONE (INL 8) (SOME (Install 0 1 2 3 4,7,5)):1 stackLang$prog) in let p=copy_ret T F (0,7,(NONE:bool option)) [[];[1;2]] kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_empty_list_loop" ``let kont=(Loop (Install 0 1 2 3 4):16 stackLang$prog) in let p=copy_ret F T (0,0,([]:num list)) ([]:num list) kont in ((no_install p <=> no_install kont), no_install p)``;
val _ = out "crni_exact_count_zero" ``let kont=(Seq (Inst asm$Skip) Skip:16 stackLang$prog) in let p=copy_ret F T (3,99,()) [1;2] kont in ((no_install p <=> no_install kont), no_install p)``;
