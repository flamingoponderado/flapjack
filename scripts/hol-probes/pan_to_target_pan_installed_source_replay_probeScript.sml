(* Literal source replay of pan_to_targetProof pan_installed_def (290-326) and
   pan_installed_imp_installed (328-334). The original proof theory is unbuilt; the definition
   and theorem (with HOL's own proof) are replayed over the loaded original theories. This is
   not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "targetSemTheory"; load "lab_to_targetTheory"; load "set_sepTheory";
open bossLib HolKernel Parse preamble targetSemTheory set_sepTheory;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_targetProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
fun guard name lit = if String.isSubstring lit source_text then ()
  else raise Fail (name ^ " literal source changed");
val _ = guard "pan_installed_def" "Definition pan_installed_def:\n  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) (mc_conf:('a,'state,'b) machine_config) shmem_extra ms p_mem p_dom sdm' \226\135\148\n  \226\136\131t m bitmap_ptr bitmaps_dm sdm.\n  let heap_stack_dm = { w | t.regs r1 <=+ w \226\136\167 w <+ t.regs r2 } in\n    (\226\136\128a. a \226\136\136 p_dom \226\135\146 m a = p_mem a) \226\136\167\n    good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm \226\136\170 bitmaps_dm) sdm \226\136\167 sdm' = sdm \226\136\169 byte_aligned \226\136\167\n    byte_aligned (t.regs r1) /\\\n\n    byte_aligned (t.regs r2) /\\\n    byte_aligned bitmap_ptr /\\\n    t.regs r1 \226\137\164\226\130\138 t.regs r2 /\\\n    1024w * bytes_in_word \226\137\164\226\130\138 t.regs r2 - t.regs r1 /\\\n    DISJOINT heap_stack_dm bitmaps_dm \226\136\167\n    m (t.regs r1) = Word bitmap_ptr \226\136\167\n    m (t.regs r1 + bytes_in_word) =\n    Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) \226\136\167\n    m (t.regs r1 + 2w * bytes_in_word) =\n    Word (bitmap_ptr + bytes_in_word * n2w data_sp +\n          bytes_in_word * n2w (LENGTH bitmaps)) \226\136\167\n    m (t.regs r1 + 3w * bytes_in_word) =\n    Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) \226\136\167\n    m (t.regs r1 + 4w * bytes_in_word) =\n    Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) \226\136\167\n    (word_list bitmap_ptr (MAP Word bitmaps) *\n     word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)\n    (fun2set (m,byte_aligned \226\136\169 bitmaps_dm)) \226\136\167\n    ffi_names = SOME mc_conf.ffi_names \226\136\167\n    (!i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ==>\n         MAP (\\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) shmem_extra =\n         DROP i (MAP w2n mc_conf.ffi_entry_pcs) \226\136\167\n         mc_conf.mmio_info =\n         ZIP (GENLIST (\206\187index. index + i) (LENGTH shmem_extra),\n             (MAP (\206\187rec. (rec.nbytes, Addr rec.addr_reg (n2w rec.addr_off), rec.reg,\n                        n2w rec.exit_pc + mc_conf.target.get_pc ms))\n                                                           shmem_extra)) \226\136\167\n    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a))\nEnd";
val _ = guard "pan_installed_imp_installed" "Theorem pan_installed_imp_installed:\n  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms p_mem p_dom sdm \226\135\146\n  installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms\nProof\n  rw[pan_installed_def, targetSemTheory.installed_def]>>\n  metis_tac[]\nQED";
val _ = new_theory "flapjack_pan_installed_source_replay";
val pan_installed_def = Define `
  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) (mc_conf:('a,'state,'b) machine_config) shmem_extra ms p_mem p_dom sdm' ⇔
  ∃t m bitmap_ptr bitmaps_dm sdm.
  let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
    (∀a. a ∈ p_dom ⇒ m a = p_mem a) ∧
    good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) sdm ∧ sdm' = sdm ∩ byte_aligned ∧
    byte_aligned (t.regs r1) /\

    byte_aligned (t.regs r2) /\
    byte_aligned bitmap_ptr /\
    t.regs r1 ≤₊ t.regs r2 /\
    1024w * bytes_in_word ≤₊ t.regs r2 - t.regs r1 /\
    DISJOINT heap_stack_dm bitmaps_dm ∧
    m (t.regs r1) = Word bitmap_ptr ∧
    m (t.regs r1 + bytes_in_word) =
    Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
    m (t.regs r1 + 2w * bytes_in_word) =
    Word (bitmap_ptr + bytes_in_word * n2w data_sp +
          bytes_in_word * n2w (LENGTH bitmaps)) ∧
    m (t.regs r1 + 3w * bytes_in_word) =
    Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) ∧
    m (t.regs r1 + 4w * bytes_in_word) =
    Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) ∧
    (word_list bitmap_ptr (MAP Word bitmaps) *
     word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)
    (fun2set (m,byte_aligned ∩ bitmaps_dm)) ∧
    ffi_names = SOME mc_conf.ffi_names ∧
    (!i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ==>
         MAP (\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) shmem_extra =
         DROP i (MAP w2n mc_conf.ffi_entry_pcs) ∧
         mc_conf.mmio_info =
         ZIP (GENLIST (λindex. index + i) (LENGTH shmem_extra),
             (MAP (λrec. (rec.nbytes, Addr rec.addr_reg (n2w rec.addr_off), rec.reg,
                        n2w rec.exit_pc + mc_conf.target.get_pc ms))
                                                           shmem_extra)) ∧
    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a))`;
val pan_installed_imp_installed = store_thm("pan_installed_imp_installed",
``  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms p_mem p_dom sdm ⇒
  installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms``,
  rw[pan_installed_def, targetSemTheory.installed_def]>>
  metis_tac[]);
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = Globals.linewidth := 1000000;
val _ = pr_stmt "pan_installed_def_replay_statement" pan_installed_def;
val _ = pr_hyps "pan_installed_def_replay_hypotheses" pan_installed_def;
val _ = pr_typed "pan_installed_def_replay_typed" pan_installed_def;
val _ = pr_stmt "pan_installed_imp_installed_replay_statement" pan_installed_imp_installed;
val _ = pr_hyps "pan_installed_imp_installed_replay_hypotheses" pan_installed_imp_installed;
val _ = pr_typed "pan_installed_imp_installed_replay_typed" pan_installed_imp_installed;
