load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture original kernel theorem constructor specializations. No standalone
   tactic replay is claimed; original FP opcode proof8174-8222 is compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val mov_to_reg_case = Q.SPEC `Inst (FP (FPMovToReg n n0 n1))` ssa_cc_trans_correct;
val _ = out "fp_mov_to_reg_full" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_st" "st" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_cst" "cst" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_first" "n" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_second" "n0" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_fp" "n1" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_ssa" "ssa" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_next" "na" mov_to_reg_case;
val _ = ty "fp_mov_to_reg_type_tables" "lt" mov_to_reg_case;
