load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native Div constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:7919-7944.
   No standalone tactic replay is claimed. *)
val div_case = Q.SPEC `Inst (Arith (Div n n0 n1))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_div_full" div_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_div_type_st" "st" div_case;
val _ = ty "inst_div_type_cst" "cst" div_case;
val _ = ty "inst_div_type_dst" "n" div_case;
val _ = ty "inst_div_type_src" "n0" div_case;
val _ = ty "inst_div_type_divisor" "n1" div_case;
val _ = ty "inst_div_type_ssa" "ssa" div_case;
val _ = ty "inst_div_type_next" "na" div_case;
val _ = ty "inst_div_type_tables" "lt" div_case;
