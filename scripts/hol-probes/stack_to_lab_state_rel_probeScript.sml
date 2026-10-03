load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory;
val _ = Globals.linewidth := 1000000;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labProofScript.sml:601-734. *)
val _ = checked "state_rel_def_statement" state_rel_def;
val _ = checked "loc_check_IMP_loc_to_pc_statement" (GEN_ALL loc_check_IMP_loc_to_pc);
val _ = checked "state_rel_dec_clock_statement" (GEN_ALL state_rel_dec_clock);
val _ = checked "state_rel_with_pc_statement" (GEN_ALL state_rel_with_pc);
val _ = checked "state_rel_with_clock_statement" (GEN_ALL state_rel_with_clock);
val _ = checked "set_var_upd_reg_statement" (GEN_ALL set_var_upd_reg);
val _ = checked "set_var_Word_upd_reg_statement" (GEN_ALL set_var_Word_upd_reg);
val _ = checked "set_fp_var_upd_fp_reg_statement" (GEN_ALL set_fp_var_upd_fp_reg);
val _ = checked "mem_store_upd_mem_statement" (GEN_ALL mem_store_upd_mem);
val _ = checked "state_rel_read_reg_FLOOKUP_regs_statement" (GEN_ALL state_rel_read_reg_FLOOKUP_regs);
val _ = checked "state_rel_read_fp_reg_FLOOKUP_fp_regs_statement" (GEN_ALL state_rel_read_fp_reg_FLOOKUP_fp_regs);
val _ = checked "state_rel_get_var_imm_statement" (GEN_ALL state_rel_get_var_imm);
