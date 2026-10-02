load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native LongMul constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:7943-8004.
   No standalone tactic replay is claimed. *)
val longmul_case = Q.SPEC `Inst (Arith (LongMul n n0 n1 n2))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_longmul_full" longmul_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_longmul_type_st" "st" longmul_case;
val _ = ty "inst_longmul_type_cst" "cst" longmul_case;
val _ = ty "inst_longmul_type_dst" "n" longmul_case;
val _ = ty "inst_longmul_type_src" "n0" longmul_case;
val _ = ty "inst_longmul_type_left" "n1" longmul_case;
val _ = ty "inst_longmul_type_right" "n2" longmul_case;
val _ = ty "inst_longmul_type_ssa" "ssa" longmul_case;
val _ = ty "inst_longmul_type_next" "na" longmul_case;
val _ = ty "inst_longmul_type_tables" "lt" longmul_case;
