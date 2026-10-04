load "preamble"; load "lab_to_targetTheory"; load "lab_to_targetProofTheory"; load "targetSemTheory"; load "target_itreePropsTheory"; load "backendPropsTheory";
open HolKernel Parse bossLib preamble lab_to_targetProofTheory target_itreePropsTheory;
val _ = new_theory "flapjack_backend_compile_lab_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of backendProofScript 1215-1221 and 3500-3519 (backendProofTheory is not built here). *)
Theorem compile_lab_LENGTH:
  compile_lab asm_conf c secs = SOME (bytes, c') ==>
  c'.pos = LENGTH bytes + c.pos
Proof
  simp [lab_to_targetTheory.compile_lab_def, UNCURRY]
  \\ every_case_tac \\ rw [] \\ simp []
QED

Theorem compile_lab_IMP_mmio_pcs_min_index:
  compile_lab asm_conf c sec_list = SOME (bytes,c') /\
  OPTION_ALL (EVERY $ \x. ∃s. x = ExtCall s) c.ffi_names ==>
  ?ffi_names. c'.ffi_names = SOME ffi_names /\
    ?x. mmio_pcs_min_index ffi_names = SOME x
Proof
  simp[lab_to_targetTheory.compile_lab_def] >>
  pairarg_tac >>fs[]>>
  pop_assum $ mp_tac o SRULE[AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[DefnBase.one_line_ify NONE OPTION_MAP_DEF,
      OPTION_MAP_DEF,backendPropsTheory.the_eqn,CaseEq"option"] >>
  FULL_CASE_TAC>>fs[] >>
  pairarg_tac>>gvs[]>>
  drule get_shmem_info_MappedRead_or_MappedWrite>>strip_tac>>
  fs[]>>
  irule_at Any mmio_pcs_min_index_APPEND_thm>>fs[Sh_not_Ext]>>
  irule find_ffi_names_EVERY>>metis_tac[]
QED
val _ = if null (hyp (compile_lab_LENGTH)) then () else raise Fail "hypotheses: compile_lab_LENGTH";
val _ = (print "compile_lab_LENGTH_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (compile_lab_LENGTH)); print "\n");
val _ = if null (hyp (compile_lab_IMP_mmio_pcs_min_index)) then () else raise Fail "hypotheses: compile_lab_IMP_mmio_pcs_min_index";
val _ = (print "compile_lab_IMP_mmio_pcs_min_index_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (compile_lab_IMP_mmio_pcs_min_index)); print "\n");
