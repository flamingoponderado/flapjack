load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_type "closure_type=" ``flatSem$Closure``;
val _ = show_type "recclosure_type=" ``flatSem$Recclosure``;
val _ = show_type "conv_type=" ``flatSem$Conv``;
val _ = show_type "lit_type=" ``flatSem$Litv``;
val _ = show_type "loc_type=" ``flatSem$Loc``;
val _ = show_type "vector_type=" ``flatSem$Vectorv``;
val _ = show_type "environment_v_type=" ``λ(s:'a flatSem$environment). s.v``;
val _ = show_type "compile_type=" ``λ(s:'c flatSem$install_config). s.compile``;
val _ = show_type "oracle_type=" ``λ(s:'c flatSem$install_config). s.compile_oracle``;
val _ = show_type "state_ffi_type=" ``λ(s:('c,'ffi) flatSem$state). s.ffi``;
val _ = show_type "state_globals_type=" ``λ(s:('c,'ffi) flatSem$state). s.globals``;
val _ = show_type "state_refs_type=" ``λ(s:('c,'ffi) flatSem$state). s.refs``;
val _ = show_type "state_config_type=" ``λ(s:('c,'ffi) flatSem$state). s.eval_config``;
val _ = show_thm "list_id=" flatSemTheory.list_id_def;
val _ = show_thm "bool_value=" flatSemTheory.Boolv_def;
val _ = show_thm "unit_value=" flatSemTheory.Unitv_def;
val _ = show_thm "build_rec_env=" flatSemTheory.build_rec_env_def;
val _ = show_thm "ctor_same_type=" flatSemTheory.ctor_same_type_def;
