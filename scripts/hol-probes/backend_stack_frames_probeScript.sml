(* Replay backendProof's stack-frame definition and theorem with inferred types. *)
load "preamble";
load "word_to_stackTheory";
open HolKernel Parse boolLib bossLib preamble word_to_stackTheory wordLangTheory sptreeTheory;
val _ = new_theory "flapjack_backend_stack_frames_replay";
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

Definition probe_compute_stack_frame_sizes_def:
  probe_compute_stack_frame_sizes c word_prog =
    let reg_count = c.reg_count - LENGTH c.avoid_regs - 5 in
      mapi (λn (arg_count,prog).
              let stack_arg_count = arg_count - reg_count ;
                  stack_var_count = MAX (max_var prog DIV 2 + 1 - reg_count) stack_arg_count ;
              in if stack_var_count = 0 then 0 else stack_var_count + 1)
        (fromAList word_prog)
End

Theorem probe_compute_stack_frame_sizes_thm:
  probe_compute_stack_frame_sizes c word_prog =
    let k = c.reg_count - LENGTH c.avoid_regs - 5 in
      mapi (λn (arg_count,prog).
        FST (SND (compile_prog c F prog arg_count k (Nil,0)))) (fromAList word_prog)
Proof
  fs [probe_compute_stack_frame_sizes_def]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ qmatch_goalsub_abbrev_tac `compile_prog _ _ _ _ k`
  \\ fs [FUN_EQ_THM,FORALL_PROD]
  \\ rpt gen_tac
  \\ once_rewrite_tac [word_to_stackTheory.compile_prog_def]
  \\ rewrite_tac [LET_THM]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ pairarg_tac \\ asm_rewrite_tac [FST,SND]
  \\ simp []
QED

val _ = (print "stack_frames_def_typed="; print_thm probe_compute_stack_frame_sizes_def; print "\n");
val _ = (print "stack_frames_thm_typed="; print_thm probe_compute_stack_frame_sizes_thm; print "\n");
