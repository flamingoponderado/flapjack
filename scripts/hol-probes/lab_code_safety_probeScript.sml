load "preamble";
load "lab_to_targetProofTheory";
open preamble HolKernel Parse boolLib bossLib labPropsTheory lab_to_targetProofTheory;
fun ty label tm = print(label ^ "=" ^ type_to_string(type_of tm) ^ "\n");
fun eqn label tm defs = let val th = prove(tm, SIMP_TAC (srw_ss()) defs) in
 if aconv(concl th) tm andalso null(hyp th) then print(label ^ "=T\n")
 else raise Fail label end;
val _ = ty "no_install_type" ``labProps$no_install``;
val _ = ty "no_share_mem_inst_type" ``labProps$no_share_mem_inst``;
val _ = ty "no_install_or_no_share_mem_type" ``lab_to_targetProof$no_install_or_no_share_mem``;
val _ = eqn "no_install_full" ``!code. labProps$no_install code <=> !p w bytes l. asm_fetch_aux p code <> SOME (LabAsm Install w bytes l)`` [labPropsTheory.no_install_def];
val _ = eqn "no_share_mem_inst_full" ``!code. labProps$no_share_mem_inst code <=> !p op re a inst len. asm_fetch_aux p code <> SOME (Asm (ShareMem op re a) inst len)`` [labPropsTheory.no_share_mem_inst_def];
val _ = eqn "no_install_or_no_share_mem_full" ``!code ffi_names. lab_to_targetProof$no_install_or_no_share_mem code ffi_names <=> (labProps$no_share_mem_inst code /\ EVERY (\x. ?s. x = ExtCall s) ffi_names) \/ labProps$no_install code`` [no_install_or_no_share_mem_def];
val _ = eqn "no_install_empty" ``labProps$no_install ([]:word8 sec list)`` [labPropsTheory.no_install_def,labSemTheory.asm_fetch_aux_def];
val _ = eqn "no_share_mem_empty" ``labProps$no_share_mem_inst ([]:word8 sec list)`` [labPropsTheory.no_share_mem_inst_def,labSemTheory.asm_fetch_aux_def];
val _ = eqn "install_excluded" ``~labProps$no_install [Section 7 [LabAsm Install (0w:word8) [] 0]]`` [labPropsTheory.no_install_def,labSemTheory.asm_fetch_aux_def,labSemTheory.is_Label_def];
val _ = eqn "shared_excluded" ``~labProps$no_share_mem_inst [Section 7 [Asm (ShareMem Load 0 (Addr 0 (0w:word8))) [] 0]]`` [labPropsTheory.no_share_mem_inst_def,labSemTheory.asm_fetch_aux_def,labSemTheory.is_Label_def];
val safety_defs = [no_install_or_no_share_mem_def,labPropsTheory.no_install_def,labPropsTheory.no_share_mem_inst_def,labSemTheory.asm_fetch_aux_def,labSemTheory.is_Label_def];
val _ = eqn "safety_empty_any_names" ``!names. no_install_or_no_share_mem ([]:word8 sec list) names`` safety_defs;
val _ = eqn "safety_install_extcall" ``no_install_or_no_share_mem [Section 7 [LabAsm Install (0w:word8) [] 0]] [ExtCall (strlit "")]`` safety_defs;
val _ = eqn "safety_install_shared_rejected" ``~no_install_or_no_share_mem [Section 7 [LabAsm Install (0w:word8) [] 0]] [SharedMem MappedRead]`` safety_defs;
val _ = eqn "safety_shared_any_names" ``!names. no_install_or_no_share_mem [Section 7 [Asm (ShareMem Load 0 (Addr 0 (0w:word8))) [] 0]] names`` safety_defs;
val _ = OS.Process.exit OS.Process.success;
