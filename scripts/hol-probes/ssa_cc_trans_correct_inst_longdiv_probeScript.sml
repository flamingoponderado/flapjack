load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native LongDiv constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:7998-8030.
   No standalone tactic replay is claimed. *)
val longdiv_case = Q.SPEC `Inst (Arith (LongDiv n n0 n1 n2 n3))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_longdiv_full" longdiv_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_longdiv_type_st" "st" longdiv_case;
val _ = ty "inst_longdiv_type_cst" "cst" longdiv_case;
val _ = ty "inst_longdiv_type_dst" "n" longdiv_case;
val _ = ty "inst_longdiv_type_src" "n0" longdiv_case;
val _ = ty "inst_longdiv_type_left" "n1" longdiv_case;
val _ = ty "inst_longdiv_type_right" "n2" longdiv_case;
val _ = ty "inst_longdiv_type_divisor" "n3" longdiv_case;
val _ = ty "inst_longdiv_type_ssa" "ssa" longdiv_case;
val _ = ty "inst_longdiv_type_next" "na" longdiv_case;
val _ = ty "inst_longdiv_type_tables" "lt" longdiv_case;
