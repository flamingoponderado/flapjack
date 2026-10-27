load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail label;
val compiled = prove(``source_to_flat$compile_exp t env (ast$Con cn es) =
  flatLang$Con None (OPTION_JOIN (OPTION_MAP (source_to_flat$type_group_id_type o nsLookup env.c) cn))
    (source_to_flat$compile_exps t env es)``, simp [source_to_flatTheory.compile_exp_def]);
val _ = show_thm "constructor_compile_typed=" compiled;
val _ = show_thm "constructor_check_typed=" semanticPrimitivesTheory.do_con_check_def;
val _ = show_thm "constructor_build_typed=" semanticPrimitivesTheory.build_conv_def;
