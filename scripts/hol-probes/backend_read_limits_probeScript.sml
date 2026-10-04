load "preamble"; load "backendTheory"; load "stack_removeProofTheory"; load "stack_namesTheory"; load "targetSemTheory"; load "data_to_wordTheory";
open HolKernel Parse bossLib preamble backendTheory stack_namesTheory;
val _ = new_theory "flapjack_backend_read_limits_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of backendProofScript 2871-2878 (backendProofTheory is not built here). *)
Definition read_limits_def:
  read_limits (asm_conf:'a asm_config) (c:config) mc ms =
    stack_removeProof$get_stack_heap_limit
      (2 * max_heap_limit (:α) c.data_conf - 1)
      (mc.target.get_reg ms (find_name c.stack_conf.reg_names 2) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 3) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 4) :'a word)
End
val _ = if null (hyp (read_limits_def)) then () else raise Fail "hypotheses: read_limits_def";
val _ = (print "read_limits_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (read_limits_def)); print "\n");
