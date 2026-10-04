load "preamble"; load "backendTheory"; load "stack_removeProofTheory"; load "targetSemTheory"; load "stack_namesTheory"; load "alignmentTheory";
open HolKernel Parse bossLib preamble backendTheory stack_namesTheory alignmentTheory;
val _ = new_theory "flapjack_backend_machine_init_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of backendProofScript 39-47, 113-131, 170-173, 300-306 (backendProofTheory is not built here). *)
Theorem byte_aligned_MOD:
    good_dimindex (:'a) ⇒
  ∀x:'a word.x ∈ byte_aligned ⇒
  w2n x MOD (dimindex (:'a) DIV 8) = 0
Proof
  rw[IN_DEF]>>
  fs [aligned_w2n, alignmentTheory.byte_aligned_def]>>
  rfs[good_dimindex_def] \\ rfs []
QED

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


Definition heap_regs_def:
  heap_regs reg_names =
    (find_name reg_names 2, find_name reg_names 4)
End

Theorem word_list_exists_imp:
   dm = stack_removeProof$addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))
Proof
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]
QED
val _ = if null (hyp (mc_init_ok_def)) then () else raise Fail "hypotheses: mc_init_ok_def";
val _ = (print "mc_init_ok_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mc_init_ok_def)); print "\n");
val _ = if null (hyp (heap_regs_def)) then () else raise Fail "hypotheses: heap_regs_def";
val _ = (print "heap_regs_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (heap_regs_def)); print "\n");
val _ = if null (hyp (byte_aligned_MOD)) then () else raise Fail "hypotheses: byte_aligned_MOD";
val _ = (print "byte_aligned_MOD_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (byte_aligned_MOD)); print "\n");
val _ = if null (hyp (word_list_exists_imp)) then () else raise Fail "hypotheses: word_list_exists_imp";
val _ = (print "word_list_exists_imp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_list_exists_imp)); print "\n");
