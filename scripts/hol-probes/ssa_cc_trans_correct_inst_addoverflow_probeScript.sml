load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native AddOverflow constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:8069-8090.
   No standalone tactic replay is claimed. *)
val addoverflow_case = Q.SPEC `Inst (Arith (AddOverflow n n0 n1 n2))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_addoverflow_full" addoverflow_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_addoverflow_type_st" "st" addoverflow_case;
val _ = ty "inst_addoverflow_type_cst" "cst" addoverflow_case;
val _ = ty "inst_addoverflow_type_dst" "n" addoverflow_case;
val _ = ty "inst_addoverflow_type_src" "n0" addoverflow_case;
val _ = ty "inst_addoverflow_type_left" "n1" addoverflow_case;
val _ = ty "inst_addoverflow_type_right" "n2" addoverflow_case;
val _ = ty "inst_addoverflow_type_ssa" "ssa" addoverflow_case;
val _ = ty "inst_addoverflow_type_next" "na" addoverflow_case;
val _ = ty "inst_addoverflow_type_tables" "lt" addoverflow_case;
