load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "evaluate=" dataSemTheory.evaluate_def;
val _ = show "eval_skip=" (EVAL ``dataSem$evaluate (dataLang$Skip, s:('c,'ffi) dataSem$state)``);
val _ = show "eval_tick_timeout=" (EVAL ``dataSem$evaluate (dataLang$Tick,
  (s:('c,'ffi) dataSem$state) with clock := 0)``);
val _ = show "eval_move_missing=" (EVAL ``dataSem$evaluate (dataLang$Move 3 2,
  (s:('c,'ffi) dataSem$state) with locals := sptree$LN)``);
val _ = show "eval_return_empty=" (EVAL ``dataSem$evaluate (dataLang$Return [],
  s:('c,'ffi) dataSem$state)``);
val _ = show "eval_seq_timeout=" (EVAL ``dataSem$evaluate (dataLang$Seq dataLang$Skip dataLang$Tick,
  (s:('c,'ffi) dataSem$state) with clock := 0)``);
val _ = show "eval_call_missing=" (EVAL ``dataSem$evaluate (dataLang$Call NONE (SOME 4) [] NONE,
  (s:('c,'ffi) dataSem$state) with code := sptree$LN)``);
val _ = show "eval_force_evaluated=" (EVAL ``dataSem$evaluate (dataLang$Force NONE 5 0,
  (s:('c,'ffi) dataSem$state) with <|locals := sptree$LS (dataSem$RefPtr F 0);
    refs := sptree$LS (bvlSem$Thunk Evaluated (dataSem$Number 7))|>)``);
val _ = show "eval_tail_call_result=" (EVAL ``FST (dataSem$evaluate
  (dataLang$Call NONE (SOME 0) [] NONE,
   (s:('c,'ffi) dataSem$state) with <|code := sptree$LS (0, dataLang$Return []); clock := 1|>))``);
val _ = show "eval_call_handler_result=" (EVAL ``FST (dataSem$evaluate
  (dataLang$Call (SOME ([1], sptree$LN)) (SOME 0) [0] (SOME (2, dataLang$Return [2])),
   (s:('c,'ffi) dataSem$state) with <|locals := sptree$LS (dataSem$Number 7);
     code := sptree$LS (1, dataLang$Raise 0); clock := 1; stack := []|>))``);
