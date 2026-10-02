load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native SubOverflow constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:8092-8113.
   No standalone tactic replay is claimed. *)
val suboverflow_case = Q.SPEC `Inst (Arith (SubOverflow n n0 n1 n2))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_suboverflow_full" suboverflow_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_suboverflow_type_st" "st" suboverflow_case;
val _ = ty "inst_suboverflow_type_cst" "cst" suboverflow_case;
val _ = ty "inst_suboverflow_type_dst" "n" suboverflow_case;
val _ = ty "inst_suboverflow_type_src" "n0" suboverflow_case;
val _ = ty "inst_suboverflow_type_left" "n1" suboverflow_case;
val _ = ty "inst_suboverflow_type_right" "n2" suboverflow_case;
val _ = ty "inst_suboverflow_type_ssa" "ssa" suboverflow_case;
val _ = ty "inst_suboverflow_type_next" "na" suboverflow_case;
val _ = ty "inst_suboverflow_type_tables" "lt" suboverflow_case;
