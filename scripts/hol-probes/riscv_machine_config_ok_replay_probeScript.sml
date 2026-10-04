(* Literal source replay of riscv_configProofScript is_riscv_machine_config_def (12-19) and
   riscv_machine_config_ok (54-66). riscv_configProofTheory is unbuilt: the definition and the
   theorem with its own HOL proof are replayed verbatim (source-guarded) over the loaded
   lab_to_targetProof, riscv_targetProof and asmProps theories, and the conclusion is printed
   with show_types. Not an exported original-theory capture. *)
load "preamble"; load "riscv_configTheory"; load "riscv_targetTheory"; load "riscv_targetProofTheory";
load "lab_to_targetProofTheory"; load "asmPropsTheory";
open HolKernel Parse bossLib preamble riscv_configTheory riscv_targetTheory riscv_targetProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun read_source rel = let val cake = case OS.Process.getEnv "CAKEML" of SOME p => p | NONE => raise Fail "CAKEML is required"
  val st = TextIO.openIn (OS.Path.concat (cake, rel)) val t = TextIO.inputAll st in TextIO.closeIn st; t end;
val riscv_src = read_source "compiler/backend/riscv/proofs/riscv_configProofScript.sml";
fun guard name src lit = if String.isSubstring lit src then () else raise Fail (name ^ " literal source changed");
val _ = guard "is_riscv_machine_config_def" riscv_src "Definition is_riscv_machine_config_def:\n  is_riscv_machine_config mc \226\135\148\n  mc.target = riscv_target \226\136\167\n  mc.len_reg = 11  \226\136\167\n  mc.ptr_reg = 10 \226\136\167\n  mc.len2_reg = 13  \226\136\167\n  mc.ptr2_reg = 12 \226\136\167\n  mc.callee_saved_regs = [24;25;26]\nEnd";
val _ = guard "riscv_machine_config_ok" riscv_src "Theorem riscv_machine_config_ok:\n   is_riscv_machine_config mc \226\135\146 mc_conf_ok mc\nProof\n  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_riscv_machine_config_def]\n  >- EVAL_TAC\n  >- simp[riscv_targetProofTheory.riscv_encoder_correct]\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- EVAL_TAC\n  >- metis_tac[asmPropsTheory.encoder_correct_def,asmPropsTheory.target_ok_def,riscv_encoder_correct]\nQED";
val _ = new_theory "flapjack_riscv_machine_config_ok_replay";
Definition is_riscv_machine_config_def:
  is_riscv_machine_config mc ⇔
  mc.target = riscv_target ∧
  mc.len_reg = 11  ∧
  mc.ptr_reg = 10 ∧
  mc.len2_reg = 13  ∧
  mc.ptr2_reg = 12 ∧
  mc.callee_saved_regs = [24;25;26]
End
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
val _ = (print "riscv_machine_config_ok_typed="; print_term (concl riscv_machine_config_ok); print "\n");
val _ = print ("riscv_machine_config_ok_hypotheses=" ^ Int.toString (length (hyp riscv_machine_config_ok)) ^ "\n");
