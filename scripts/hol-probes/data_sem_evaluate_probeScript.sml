load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
val _ = show_type "prog_skip_type=" ``dataLang$Skip``;
val _ = show_type "prog_move_type=" ``dataLang$Move``;
val _ = show_type "prog_call_type=" ``dataLang$Call``;
val _ = show_type "prog_assign_type=" ``dataLang$Assign``;
val _ = show_type "prog_seq_type=" ``dataLang$Seq``;
val _ = show_type "prog_if_type=" ``dataLang$If``;
val _ = show_type "prog_make_space_type=" ``dataLang$MakeSpace``;
val _ = show_type "prog_raise_type=" ``dataLang$Raise``;
val _ = show_type "prog_return_type=" ``dataLang$Return``;
val _ = show_type "prog_tick_type=" ``dataLang$Tick``;
val _ = show_type "prog_force_type=" ``dataLang$Force``;
val _ = show_type "stack_env_type=" ``dataSem$Env``;
val _ = show_type "stack_exc_type=" ``dataSem$Exc``;
val _ = show_type "limits_heap_type=" ``λ(l:dataSem$limits). l.heap_limit``;
val _ = show_type "limits_length_type=" ``λ(l:dataSem$limits). l.length_limit``;
val _ = show_type "limits_stack_type=" ``λ(l:dataSem$limits). l.stack_limit``;
val _ = show_type "limits_arch_type=" ``λ(l:dataSem$limits). l.arch_64_bit``;
val _ = show_type "limits_fp_type=" ``λ(l:dataSem$limits). l.has_fp_ops``;
val _ = show_type "limits_fp_tops_type=" ``λ(l:dataSem$limits). l.has_fp_tops``;
val _ = show_type "state_locals_type=" ``λ(s:('c,'ffi) dataSem$state). s.locals``;
val _ = show_type "state_locals_size_type=" ``λ(s:('c,'ffi) dataSem$state). s.locals_size``;
val _ = show_type "state_stack_type=" ``λ(s:('c,'ffi) dataSem$state). s.stack``;
val _ = show_type "state_stack_max_type=" ``λ(s:('c,'ffi) dataSem$state). s.stack_max``;
val _ = show_type "state_frame_sizes_type=" ``λ(s:('c,'ffi) dataSem$state). s.stack_frame_sizes``;
val _ = show_type "state_global_type=" ``λ(s:('c,'ffi) dataSem$state). s.global``;
val _ = show_type "state_handler_type=" ``λ(s:('c,'ffi) dataSem$state). s.handler``;
val _ = show_type "state_refs_type=" ``λ(s:('c,'ffi) dataSem$state). s.refs``;
val _ = show_type "state_compile_type=" ``λ(s:('c,'ffi) dataSem$state). s.compile``;
val _ = show_type "state_clock_type=" ``λ(s:('c,'ffi) dataSem$state). s.clock``;
val _ = show_type "state_code_type=" ``λ(s:('c,'ffi) dataSem$state). s.code``;
val _ = show_type "state_ffi_type=" ``λ(s:('c,'ffi) dataSem$state). s.ffi``;
val _ = show_type "state_space_type=" ``λ(s:('c,'ffi) dataSem$state). s.space``;
val _ = show_type "state_tstamps_type=" ``λ(s:('c,'ffi) dataSem$state). s.tstamps``;
val _ = show_type "state_limits_type=" ``λ(s:('c,'ffi) dataSem$state). s.limits``;
val _ = show_type "state_safe_type=" ``λ(s:('c,'ffi) dataSem$state). s.safe_for_space``;
val _ = show_type "state_peak_type=" ``λ(s:('c,'ffi) dataSem$state). s.peak_heap_length``;
val _ = show_type "state_oracle_type=" ``λ(s:('c,'ffi) dataSem$state). s.compile_oracle``;
val _ = show "dec_clock=" dataSemTheory.dec_clock_def;
val _ = show "fix_clock=" dataSemTheory.fix_clock_def;
(* Typed replay of the local fix_clock_IMP theorem, which HOL does not export. *)
val fix_clock_imp_replay = Q.prove (
  `dataSem$fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` THEN fs [dataSemTheory.fix_clock_def] THEN rw [] THEN fs []);
val _ = show "fix_clock_imp=" fix_clock_imp_replay;
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
