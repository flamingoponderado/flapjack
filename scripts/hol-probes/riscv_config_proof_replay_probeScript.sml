(* Literal source replay of riscv_configProofScript is_riscv_machine_config_def (12-19) and
   riscv_init_ok (68-75), with backendProofScript mc_init_ok_def (113-131) replayed (both proof
   theories unbuilt); riscv_init_ok is re-proved with its own HOL tactic over the loaded theories.
   Not an exported original-theory capture. *)
load "preamble"; load "backendTheory"; load "stack_namesTheory"; load "riscv_configTheory"; load "riscv_targetTheory"; load "targetSemTheory";
open HolKernel Parse bossLib preamble backendTheory stack_namesTheory riscv_configTheory riscv_targetTheory targetSemTheory;
val _ = Globals.linewidth := 1000000;
fun read_source rel = let val cake = case OS.Process.getEnv "CAKEML" of SOME p => p | NONE => raise Fail "CAKEML is required"
  val st = TextIO.openIn (OS.Path.concat (cake, rel)) val t = TextIO.inputAll st in TextIO.closeIn st; t end;
val backend_src = read_source "compiler/backend/proofs/backendProofScript.sml";
val riscv_src = read_source "compiler/backend/riscv/proofs/riscv_configProofScript.sml";
fun guard name src lit = if String.isSubstring lit src then () else raise Fail (name ^ " literal source changed");
val _ = guard "mc_init_ok_def" backend_src "Definition mc_init_ok_def:\n  mc_init_ok asm_conf c mc \226\135\148\n  EVERY (\206\187r. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] \226\136\167\n  find_name c.stack_conf.reg_names 4 = mc.len2_reg \226\136\167\n  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg \226\136\167\n  find_name c.stack_conf.reg_names 2 = mc.len_reg \226\136\167\n  find_name c.stack_conf.reg_names 1 = mc.ptr_reg \226\136\167\n  find_name c.stack_conf.reg_names 0 =\n    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\136\167\n  c.data_conf.be = mc.target.config.big_endian \226\136\167\n  (* the next four are implied by injectivity of find_name *)\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.len_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.ptr_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.len2_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.ptr2_reg \226\136\167\n  \194\172MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs \226\136\167\n   asm_conf = mc.target.config\nEnd";
val _ = guard "is_riscv_machine_config_def" riscv_src "Definition is_riscv_machine_config_def:\n  is_riscv_machine_config mc \226\135\148\n  mc.target = riscv_target \226\136\167\n  mc.len_reg = 11  \226\136\167\n  mc.ptr_reg = 10 \226\136\167\n  mc.len2_reg = 13  \226\136\167\n  mc.ptr2_reg = 12 \226\136\167\n  mc.callee_saved_regs = [24;25;26]\nEnd";
val _ = guard "riscv_init_ok" riscv_src "Theorem riscv_init_ok:\n   is_riscv_machine_config mc \226\135\146\n    mc_init_ok riscv_config riscv_backend_config mc\nProof\n  rw[mc_init_ok_def] \\\\\n  fs[is_riscv_machine_config_def] \\\\\n  EVAL_TAC\nQED";
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
val _ = (print "is_riscv_machine_config_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl is_riscv_machine_config_def); print "\n");
val _ = (print "riscv_init_ok_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl riscv_init_ok); print "\n");
val _ = print ("riscv_init_ok_hypotheses=" ^ Int.toString (length (hyp riscv_init_ok)) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
