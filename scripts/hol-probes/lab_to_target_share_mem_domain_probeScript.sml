(* Original HOL share_mem_domain_code_rel (lab_to_targetProofScript.sml:688-717): the full
   typed definition, its reduction on code with no lines to the byte_align domain closure and
   shared_addresses equation, a satisfied instance (the full domain) and a violated one (the
   64-bit singleton {8w}, where byte_align 9w = 8w through LOG2 8 = 3). *)
load "lab_to_targetProofTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib lab_to_targetProofTheory;
val _ = Globals.linewidth := 4000;
fun observe_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = Globals.show_types := true;
val _ = observe_thm "smd_def" share_mem_domain_code_rel_def;
val _ = Globals.show_types := false;
val nil_thm = prove (``share_mem_domain_code_rel mc p [] d <=>
    (!a. byte_align a IN d ==> a IN d) /\ mc.shared_addresses = d``,
  simp [share_mem_domain_code_rel_def, labSemTheory.asm_fetch_aux_def]);
val _ = observe_thm "smd_nil" nil_thm;
val _ = observe_thm "smd_univ" (prove (``!mc p. mc.shared_addresses = UNIV ==>
    share_mem_domain_code_rel mc p [] UNIV``, simp [nil_thm]));
val log2_8 = prove (``LOG2 8 = 3``, REWRITE_TAC [bitTheory.LOG2_def] >> irule logrootTheory.LOG_UNIQUE >> EVAL_TAC);
val ba9 = prove (``byte_align (9w : word64) = 8w``,
  REWRITE_TAC [alignmentTheory.byte_align_def] >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  SIMP_TAC arith_ss [log2_8] >> EVAL_TAC);
val not_closed = prove (``~(!a. byte_align (a : word64) IN {8w} ==> a IN {8w})``,
  strip_tac >> first_x_assum (qspec_then `9w` mp_tac) >> simp [ba9]);
val _ = observe_thm "smd_singleton" (prove (``!mc (p : word64). ~share_mem_domain_code_rel mc p [] {8w}``,
  metis_tac [nil_thm, not_closed]));
