load "preamble"; load "backendTheory"; load "stack_removeTheory"; load "stack_namesTheory"; load "stackPropsTheory"; load "data_to_wordTheory"; load "lab_to_targetTheory";
open HolKernel Parse bossLib preamble backendTheory stack_namesTheory stackPropsTheory;
val _ = new_theory "flapjack_backend_config_ok_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of backendProofScript 53-88 (backendProofTheory is not built here). *)
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
val _ = if null (hyp (backend_config_ok_def)) then () else raise Fail "hypotheses: backend_config_ok_def";
val _ = (print "backend_config_ok_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (backend_config_ok_def)); print "\n");
