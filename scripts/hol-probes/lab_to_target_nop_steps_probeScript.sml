load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble asmPropsTheory lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
fun emit_types label th =
 (show_types := true; emit label th; show_types := false);
val _ = emit "asm_consts" asm_consts;
val _ = emit_types "asm_consts_types" asm_consts;
val _ = emit "asm_failed_ignore_new_pc" asm_failed_ignore_new_pc;
val _ = emit_types "asm_failed_ignore_new_pc_types" asm_failed_ignore_new_pc;
val _ = emit "asm_mem_ignore_new_pc" asm_mem_ignore_new_pc;
val _ = emit_types "asm_mem_ignore_new_pc_types" asm_mem_ignore_new_pc;
val _ = emit "asm_step_nop_def" asm_step_nop_def;
val _ = emit_types "asm_step_nop_def_types" asm_step_nop_def;
val _ = emit "asm_step_IMP_evaluate_step_nop" asm_step_IMP_evaluate_step_nop;
val _ = emit_types "asm_step_IMP_evaluate_step_nop_types" asm_step_IMP_evaluate_step_nop;
(* evaluate_nop_steps is [local] in lab_to_targetProofScript.sml:152-228 and is
   not exported; re-elaborate its exact unchanged statement text and record the
   inferred types.  This is a statement capture, not a theorem replay. *)
val evaluate_nop_steps_stmt = ``
  !n s1 ms1 c.
      encoder_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      ffi_entry_pcs_disjoint c s1
        (n * LENGTH (c.target.config.encode (Inst Skip))) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc
        (FLAT (REPLICATE n (c.target.config.encode (Inst Skip)))) s1.mem
        s1.mem_domain /\
      (case c.target.config.link_reg of NONE => T | SOME r => s1.lr = r) /\
      (s1.be <=> c.target.config.big_endian) /\
      s1.align = c.target.config.code_alignment /\ ~s1.failed /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2.
        !k.
          (evaluate c io (k + l) ms1 =
           evaluate (shift_interfer l c) io k ms2) /\
          (find_next_interference c io (k + l) ms1 =
           find_next_interference (shift_interfer l c) io k ms2) /\
          target_state_rel c.target
            (upd_pc
              (s1.pc +
               n2w (n * LENGTH (c.target.config.encode (Inst Skip)))) s1)
            ms2``;
val _ = (print "evaluate_nop_steps_statement="; print_term evaluate_nop_steps_stmt; print "\n");
val _ = show_types := true;
val _ = (print "evaluate_nop_steps_statement_types="; print_term evaluate_nop_steps_stmt; print "\n");
val _ = show_types := false;
val _ = OS.Process.exit OS.Process.success;
