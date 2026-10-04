(* Literal source replay of riscv_configProofScript is_riscv_machine_config_def (12-19) and
   riscv_init_ok (68-75), with backendProofScript mc_init_ok_def (113-131) replayed (both proof
   theories unbuilt); riscv_init_ok and riscv_machine_config_ok (54-66, over the built lab_to_targetProof and
   riscv_targetProof theories) are re-proved with their own HOL tactics over the loaded theories.
   Not an exported original-theory capture. *)
load "preamble"; load "backendTheory"; load "stack_namesTheory"; load "riscv_configTheory"; load "riscv_targetTheory"; load "targetSemTheory"; load "stack_removeTheory"; load "stackPropsTheory"; load "data_to_wordTheory"; load "lab_to_targetTheory"; load "miscTheory"; load "blastLib"; load "lab_to_targetProofTheory"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble backendTheory stack_namesTheory riscv_configTheory riscv_targetTheory targetSemTheory stackPropsTheory blastLib riscv_targetProofTheory;
val _ = Globals.linewidth := 1000000;
fun read_source rel = let val cake = case OS.Process.getEnv "CAKEML" of SOME p => p | NONE => raise Fail "CAKEML is required"
  val st = TextIO.openIn (OS.Path.concat (cake, rel)) val t = TextIO.inputAll st in TextIO.closeIn st; t end;
val backend_src = read_source "compiler/backend/proofs/backendProofScript.sml";
val riscv_src = read_source "compiler/backend/riscv/proofs/riscv_configProofScript.sml";
fun guard name src lit = if String.isSubstring lit src then () else raise Fail (name ^ " literal source changed");
val _ = guard "mc_init_ok_def" backend_src "Definition mc_init_ok_def:\n  mc_init_ok asm_conf c mc \226\135\148\n  EVERY (\206\187r. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] \226\136\167\n  find_name c.stack_conf.reg_names 4 = mc.len2_reg \226\136\167\n  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg \226\136\167\n  find_name c.stack_conf.reg_names 2 = mc.len_reg \226\136\167\n  find_name c.stack_conf.reg_names 1 = mc.ptr_reg \226\136\167\n  find_name c.stack_conf.reg_names 0 =\n    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\136\167\n  c.data_conf.be = mc.target.config.big_endian \226\136\167\n  (* the next four are implied by injectivity of find_name *)\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.len_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.ptr_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.len2_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.ptr2_reg \226\136\167\n  \194\172MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs \226\136\167\n   asm_conf = mc.target.config\nEnd";
val _ = guard "is_riscv_machine_config_def" riscv_src "Definition is_riscv_machine_config_def:\n  is_riscv_machine_config mc \226\135\148\n  mc.target = riscv_target \226\136\167\n  mc.len_reg = 11  \226\136\167\n  mc.ptr_reg = 10 \226\136\167\n  mc.len2_reg = 13  \226\136\167\n  mc.ptr2_reg = 12 \226\136\167\n  mc.callee_saved_regs = [24;25;26]\nEnd";
val _ = guard "riscv_init_ok" riscv_src "Theorem riscv_init_ok:\n   is_riscv_machine_config mc \226\135\146\n    mc_init_ok riscv_config riscv_backend_config mc\nProof\n  rw[mc_init_ok_def] \\\\\n  fs[is_riscv_machine_config_def] \\\\\n  EVAL_TAC\nQED";
val _ = guard "backend_config_ok_def" backend_src "Definition backend_config_ok_def:\n  backend_config_ok (asm_conf:'a asm_config) (c:config) \226\135\148\n    c.source_conf = prim_src_config \226\136\167\n    0 < c.clos_conf.max_app \226\136\167\n    c.bvl_conf.next_name2 = bvl_num_stubs + 2 \226\136\167\n    LENGTH asm_conf.avoid_regs + 13 \226\137\164 asm_conf.reg_count \226\136\167\n    c.lab_conf.pos = 0 \226\136\167\n    c.lab_conf.labels = LN \226\136\167\n    conf_ok (:'a) c.data_conf \226\136\167\n    (c.data_conf.has_longdiv \226\135\146 asm_conf.ISA = x86_64) /\\\n    (c.data_conf.has_div \226\135\146\n      asm_conf.ISA = ARMv8 \226\136\168 asm_conf.ISA = MIPS \226\136\168\n      asm_conf.ISA = RISC_V) \226\136\167\n    (c.data_conf.has_fp_tern \226\135\148\n        asm_conf.ISA = ARMv7 \226\136\167 2 < asm_conf.fp_reg_count) \226\136\167\n    (c.data_conf.has_fp_ops \226\135\148 1 < asm_conf.fp_reg_count) \226\136\167\n    max_stack_alloc \226\137\164 2 * max_heap_limit (:'a) c.data_conf \226\136\146 1 \226\136\167\n    c.stack_conf.perf_calls = F \226\136\167\n    addr_offset_ok asm_conf 0w \226\136\167\n    hw_offset_ok asm_conf 0w \226\136\167\n    (\226\136\128w. -8w \226\137\164 w \226\136\167 w \226\137\164 8w \226\135\146 byte_offset_ok asm_conf w) \226\136\167\n    asm_conf.valid_imm (INL Add) 8w \226\136\167\n    asm_conf.valid_imm (INL Add) 4w \226\136\167\n    asm_conf.valid_imm (INL Add) 1w \226\136\167\n    asm_conf.valid_imm (INL Sub) 1w \226\136\167\n    OPTION_ALL (EVERY (\206\187x. \226\136\131s. x = ExtCall s)) c.lab_conf.ffi_names \226\136\167\n    find_name c.stack_conf.reg_names PERMUTES UNIV \226\136\167\n    names_ok c.stack_conf.reg_names asm_conf.reg_count asm_conf.avoid_regs \226\136\167\n    stackProps$fixed_names c.stack_conf.reg_names asm_conf \226\136\167\n    (\226\136\128s. addr_offset_ok asm_conf (store_offset s)) \226\136\167\n    (\226\136\128s. hw_offset_ok asm_conf (store_offset s)) \226\136\167\n    (\226\136\128n.\n         n \226\137\164 max_stack_alloc \226\135\146\n         asm_conf.valid_imm (INL Sub) (n2w (n * (dimindex (:\206\177) DIV 8))) \226\136\167\n         asm_conf.valid_imm (INL Add) (n2w (n * (dimindex (:\206\177) DIV 8))))\nEnd";
val _ = guard "names_tac" riscv_src "val names_tac =\n  simp[tlookup_bij_iff] \\\\ EVAL_TAC\n  \\\\ REWRITE_TAC[SUBSET_DEF] \\\\ EVAL_TAC\n  \\\\ rpt strip_tac \\\\ rveq \\\\ EVAL_TAC\n";
val _ = guard "riscv_backend_config_ok" riscv_src "Theorem riscv_backend_config_ok:\n    backend_config_ok riscv_config riscv_backend_config\nProof\n  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)\n  >- fs[riscv_backend_config_def]\n  >- (EVAL_TAC>> blastLib.FULL_BBLAST_TAC)\n  >- names_tac\n  >- (\n    fs [stack_removeTheory.store_offset_def,\n        stack_removeTheory.store_pos_def]\n    \\\\ every_case_tac \\\\ fs [] THEN1 EVAL_TAC\n    \\\\ fs [stack_removeTheory.store_list_def]\n    \\\\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]\n    \\\\ rveq \\\\ fs [] \\\\ EVAL_TAC)\n  >- (\n    fs [stack_removeTheory.store_offset_def,\n        stack_removeTheory.store_pos_def]\n    \\\\ every_case_tac \\\\ fs [] THEN1 EVAL_TAC\n    \\\\ fs [stack_removeTheory.store_list_def]\n    \\\\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]\n    \\\\ rveq \\\\ fs [] \\\\ EVAL_TAC)\n  \\\\ fs[stack_removeTheory.max_stack_alloc_def]\n  \\\\ EVAL_TAC>>fs[]\n  \\\\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP\n  \\\\ fs[]\nQED";
val _ = new_theory "flapjack_riscv_config_proof_replay";
Definition mc_init_ok_def:
  mc_init_ok asm_conf c mc ⇔
  EVERY (λr. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] ∧
  find_name c.stack_conf.reg_names 4 = mc.len2_reg ∧
  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg ∧
  find_name c.stack_conf.reg_names 2 = mc.len_reg ∧
  find_name c.stack_conf.reg_names 1 = mc.ptr_reg ∧
  find_name c.stack_conf.reg_names 0 =
    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ∧
  c.data_conf.be = mc.target.config.big_endian ∧
  (* the next four are implied by injectivity of find_name *)
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len2_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr2_reg ∧
  ¬MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs ∧
   asm_conf = mc.target.config
End
Definition is_riscv_machine_config_def:
  is_riscv_machine_config mc ⇔
  mc.target = riscv_target ∧
  mc.len_reg = 11  ∧
  mc.ptr_reg = 10 ∧
  mc.len2_reg = 13  ∧
  mc.ptr2_reg = 12 ∧
  mc.callee_saved_regs = [24;25;26]
End
Theorem riscv_init_ok:
   is_riscv_machine_config mc ⇒
    mc_init_ok riscv_config riscv_backend_config mc
Proof
  rw[mc_init_ok_def] \\
  fs[is_riscv_machine_config_def] \\
  EVAL_TAC
QED
Definition backend_config_ok_def:
  backend_config_ok (asm_conf:'a asm_config) (c:config) ⇔
    c.source_conf = prim_src_config ∧
    0 < c.clos_conf.max_app ∧
    c.bvl_conf.next_name2 = bvl_num_stubs + 2 ∧
    LENGTH asm_conf.avoid_regs + 13 ≤ asm_conf.reg_count ∧
    c.lab_conf.pos = 0 ∧
    c.lab_conf.labels = LN ∧
    conf_ok (:'a) c.data_conf ∧
    (c.data_conf.has_longdiv ⇒ asm_conf.ISA = x86_64) /\
    (c.data_conf.has_div ⇒
      asm_conf.ISA = ARMv8 ∨ asm_conf.ISA = MIPS ∨
      asm_conf.ISA = RISC_V) ∧
    (c.data_conf.has_fp_tern ⇔
        asm_conf.ISA = ARMv7 ∧ 2 < asm_conf.fp_reg_count) ∧
    (c.data_conf.has_fp_ops ⇔ 1 < asm_conf.fp_reg_count) ∧
    max_stack_alloc ≤ 2 * max_heap_limit (:'a) c.data_conf − 1 ∧
    c.stack_conf.perf_calls = F ∧
    addr_offset_ok asm_conf 0w ∧
    hw_offset_ok asm_conf 0w ∧
    (∀w. -8w ≤ w ∧ w ≤ 8w ⇒ byte_offset_ok asm_conf w) ∧
    asm_conf.valid_imm (INL Add) 8w ∧
    asm_conf.valid_imm (INL Add) 4w ∧
    asm_conf.valid_imm (INL Add) 1w ∧
    asm_conf.valid_imm (INL Sub) 1w ∧
    OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
    find_name c.stack_conf.reg_names PERMUTES UNIV ∧
    names_ok c.stack_conf.reg_names asm_conf.reg_count asm_conf.avoid_regs ∧
    stackProps$fixed_names c.stack_conf.reg_names asm_conf ∧
    (∀s. addr_offset_ok asm_conf (store_offset s)) ∧
    (∀s. hw_offset_ok asm_conf (store_offset s)) ∧
    (∀n.
         n ≤ max_stack_alloc ⇒
         asm_conf.valid_imm (INL Sub) (n2w (n * (dimindex (:α) DIV 8))) ∧
         asm_conf.valid_imm (INL Add) (n2w (n * (dimindex (:α) DIV 8))))
End
val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC
Theorem riscv_backend_config_ok:
    backend_config_ok riscv_config riscv_backend_config
Proof
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[riscv_backend_config_def]
  >- (EVAL_TAC>> blastLib.FULL_BBLAST_TAC)
  >- names_tac
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  \\ fs[stack_removeTheory.max_stack_alloc_def]
  \\ EVAL_TAC>>fs[]
  \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
  \\ fs[]
QED
val _ = guard "riscv_machine_config_ok" riscv_src "Theorem riscv_machine_config_ok:\n   is_riscv_machine_config mc \226\135\146 mc_conf_ok mc\nProof\n  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_riscv_machine_config_def]\n  >- EVAL_TAC\n  >- simp[riscv_targetProofTheory.riscv_encoder_correct]\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- metis_tac[asmPropsTheory.encoder_correct_def,asmPropsTheory.target_ok_def,riscv_encoder_correct]\nQED";
Theorem riscv_machine_config_ok:
   is_riscv_machine_config mc ⇒ mc_conf_ok mc
Proof
  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_riscv_machine_config_def]
  >- EVAL_TAC
  >- simp[riscv_targetProofTheory.riscv_encoder_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- metis_tac[asmPropsTheory.encoder_correct_def,asmPropsTheory.target_ok_def,riscv_encoder_correct]
QED
val _ = (print "riscv_backend_config_ok_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl riscv_backend_config_ok); print "\n");
val _ = print ("riscv_backend_config_ok_hypotheses=" ^ Int.toString (length (hyp riscv_backend_config_ok)) ^ "\n");
val _ = (print "is_riscv_machine_config_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl is_riscv_machine_config_def); print "\n");
val _ = (print "riscv_init_ok_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl riscv_init_ok); print "\n");
val _ = print ("riscv_init_ok_hypotheses=" ^ Int.toString (length (hyp riscv_init_ok)) ^ "\n");
val _ = (print "riscv_machine_config_ok_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl riscv_machine_config_ok); print "\n");
val _ = print ("riscv_machine_config_ok_hypotheses=" ^ Int.toString (length (hyp riscv_machine_config_ok)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
