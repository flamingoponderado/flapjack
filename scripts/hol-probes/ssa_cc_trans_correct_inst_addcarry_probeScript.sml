load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native AddCarry constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:8031-8068.
   No standalone tactic replay is claimed. *)
val addcarry_case = Q.SPEC `Inst (Arith (AddCarry n n0 n1 n2))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_addcarry_full" addcarry_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_addcarry_type_st" "st" addcarry_case;
val _ = ty "inst_addcarry_type_cst" "cst" addcarry_case;
val _ = ty "inst_addcarry_type_dst" "n" addcarry_case;
val _ = ty "inst_addcarry_type_src" "n0" addcarry_case;
val _ = ty "inst_addcarry_type_left" "n1" addcarry_case;
val _ = ty "inst_addcarry_type_right" "n2" addcarry_case;
val _ = ty "inst_addcarry_type_ssa" "ssa" addcarry_case;
val _ = ty "inst_addcarry_type_next" "na" addcarry_case;
val _ = ty "inst_addcarry_type_tables" "lt" addcarry_case;
