(* Full unchanged original native target byte proofs and binder types. *)
load "preamble"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val bytes_in_memory_thm = prove (``!w s state a b c d.
      target_state_rel riscv_target s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      ((state.c_MCSR state.procID).mstatus.VM = 0w) /\
      ((state.c_MCSR state.procID).mcpuid.ArchBase = 2w) /\
      (state.c_NextFetch state.procID = NONE) /\
      aligned 2 (state.c_PC state.procID) /\
      (state.MEM8 (state.c_PC state.procID) = a) /\
      (state.MEM8 (state.c_PC state.procID + 1w) = b) /\
      (state.MEM8 (state.c_PC state.procID + 2w) = c) /\
      (state.MEM8 (state.c_PC state.procID + 3w) = d) /\
      state.c_PC state.procID + 3w IN s.mem_domain /\
      state.c_PC state.procID + 2w IN s.mem_domain /\
      state.c_PC state.procID + 1w IN s.mem_domain /\
      state.c_PC state.procID IN s.mem_domain``,
rw [asmPropsTheory.target_state_rel_def, riscv_target_def, riscv_config_def,
       riscv_ok_def, miscTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq]
   \\ fs []);
val _ = (print "bytes_in_memory_thm_statement="; print_term (concl (GEN_ALL bytes_in_memory_thm)); print "\n");
val _ = print ("bytes_in_memory_thm_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL bytes_in_memory_thm))))) ^ "\n");
val _ = print ("bytes_in_memory_thm_hypotheses=" ^ Int.toString (length (hyp bytes_in_memory_thm)) ^ "\n");
val _ = (print "bytes_in_memory_thm_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL bytes_in_memory_thm)))); print "\n");
val bytes_in_memory_thm2 = prove (``!w s state a b c d.
      target_state_rel riscv_target s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM8 (state.c_PC state.procID + w) = a) /\
      (state.MEM8 (state.c_PC state.procID + w + 1w) = b) /\
      (state.MEM8 (state.c_PC state.procID + w + 2w) = c) /\
      (state.MEM8 (state.c_PC state.procID + w + 3w) = d) /\
      state.c_PC state.procID + w + 3w IN s.mem_domain /\
      state.c_PC state.procID + w + 2w IN s.mem_domain /\
      state.c_PC state.procID + w + 1w IN s.mem_domain /\
      state.c_PC state.procID + w IN s.mem_domain``,
rw [asmPropsTheory.target_state_rel_def, riscv_target_def, riscv_config_def,
       riscv_ok_def, miscTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq]
   \\ fs []);
val _ = (print "bytes_in_memory_thm2_statement="; print_term (concl (GEN_ALL bytes_in_memory_thm2)); print "\n");
val _ = print ("bytes_in_memory_thm2_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL bytes_in_memory_thm2))))) ^ "\n");
val _ = print ("bytes_in_memory_thm2_hypotheses=" ^ Int.toString (length (hyp bytes_in_memory_thm2)) ^ "\n");
val _ = (print "bytes_in_memory_thm2_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL bytes_in_memory_thm2)))); print "\n");
val _ = OS.Process.exit OS.Process.success;
