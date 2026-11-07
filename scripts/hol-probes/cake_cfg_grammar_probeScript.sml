load "gramTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "cml_grammar="; print_thm gramTheory.cmlG_def; print "\n");
val _ = (print "cml_start="; print_thm (SIMP_CONV (srw_ss()) [gramTheory.cmlG_def] ``gram$cmlG.start``); print "\n");
val _ = (print "empty_top="; print_thm (SIMP_CONV (srw_ss()) [gramTheory.cmlG_def, finite_mapTheory.FAPPLY_FUPDATE_THM, gramTheory.nt_distinct_ths] ``[] ∈ gram$cmlG.rules ' (INL gram$nTopLevelDecs)``); print "\n");
val _ = (print "decl_top="; print_thm (SIMP_CONV (srw_ss()) [gramTheory.cmlG_def, finite_mapTheory.FAPPLY_FUPDATE_THM, gramTheory.nt_distinct_ths] ``[NT (INL gram$nDecl); NT (INL gram$nNonETopLevelDecs)] ∈ gram$cmlG.rules ' (INL gram$nTopLevelDecs)``); print "\n");
