load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
val _ = Parse.temp_remove_user_printer ("num.numeral_computations", mk_var("n", numSyntax.num));
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
val _ = emit "state_rel_full_definition" state_rel_def;
val _ = show_types := true;
val _ = emit "state_rel_full_definition_types" state_rel_def;
val _ = show_types := false;
val _ = emit "state_rel_target_projection" (Q.prove
 (`state_rel (mc,code,labs,p) s t ms ==> target_state_rel mc.target t ms`,
  simp [state_rel_def]));
val _ = emit "state_rel_compile_projection" (Q.prove
 (`state_rel (mc,code,labs,p) s t ms ==> s.compile = compile_lab mc.target.config`,
  simp [state_rel_def]));
val _ = emit "state_rel_memory_projection" (Q.prove
 (`state_rel (mc,code,labs,p) s t ms /\ byte_align a IN s.mem_domain ==>
   a IN t.mem_domain /\ a IN s.mem_domain /\
   word_loc_val_byte p labs s.mem a s.be = SOME (t.mem a)`,
  simp [state_rel_def] >> metis_tac []));
val _ = emit "state_rel_clock_update" (Q.prove
 (`state_rel (mc,code,labs,p) (s with clock := clock) t ms <=>
   state_rel (mc,code,labs,p) s t ms`,
  simp [state_rel_def, share_mem_state_rel_def]));
val _ = emit "state_rel_one_bit_rejected" (Q.prove
 (`~state_rel (mc,code,labs,p) (s:(one,lab_to_target$config,'ffi) labSem$state) t ms`,
  simp [state_rel_def, good_dimindex_def, fcpTheory.index_one]));
val _ = OS.Process.exit OS.Process.success;
