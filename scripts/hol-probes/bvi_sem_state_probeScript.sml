load "bviSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun typ label term = (print label; print_type (type_of term); print "\n");
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = typ "exn_type=" ``bviSem$Exn``;
val _ = typ "ret_type=" ``bviSem$Ret``;
val _ = typ "result_type=" ``λ(x:bviSem$bvi_result). x``;
val _ = typ "state_refs_type=" ``λ(s:('c,'ffi) bviSem$state). s.refs``;
val _ = typ "state_clock_type=" ``λ(s:('c,'ffi) bviSem$state). s.clock``;
val _ = typ "state_global_type=" ``λ(s:('c,'ffi) bviSem$state). s.global``;
val _ = typ "state_compile_type=" ``λ(s:('c,'ffi) bviSem$state). s.compile``;
val _ = typ "state_oracle_type=" ``λ(s:('c,'ffi) bviSem$state). s.compile_oracle``;
val _ = typ "state_code_type=" ``λ(s:('c,'ffi) bviSem$state). s.code``;
val _ = typ "state_ffi_type=" ``λ(s:('c,'ffi) bviSem$state). s.ffi``;
val _ = show "dec_clock=" bviSemTheory.dec_clock_def;
val _ = show "bvl_to_bvi=" bviSemTheory.bvl_to_bvi_def;
