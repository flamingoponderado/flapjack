(* Inferred compiler configuration carrier used by compilerProof. *)
load "preamble";
load "compilerTheory";
val _ = loadPath := (valOf (OS.Process.getEnv "CAKEML") ^ "/compiler/backend/proofs") :: !loadPath;
load "stack_removeProofTheory";
load "stack_namesTheory";
load "targetSemTheory";
load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_namesTheory;
val _ = new_theory "flapjack_compiler_read_limits_replay";
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Replay the backend definition and the compilerProof wrapper from source;
   the names are local because the full proof theory need not be built. *)
Definition probe_backend_read_limits_def:
  probe_backend_read_limits (asm_conf:'a asm_config) (c:backend$config) mc ms =
    stack_removeProof$get_stack_heap_limit
      (2 * max_heap_limit (:α) c.data_conf - 1)
      (mc.target.get_reg ms (find_name c.stack_conf.reg_names 2) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 3) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 4) :'a word)
End
Definition probe_read_limits_def:
  probe_read_limits cc mc ms = probe_backend_read_limits cc.asm_config cc.backend_config mc ms
End
val _ = (print "compiler_config_axiom="; print_thm compilerTheory.config_Axiom; print "\n");
val _ = (print "compiler_read_limits_replay="; print_thm probe_read_limits_def; print "\n");
