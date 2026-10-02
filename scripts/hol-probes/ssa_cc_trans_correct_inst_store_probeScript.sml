load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native Store constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:8143-8154.
   No standalone tactic replay is claimed. *)
val store_case = Q.SPEC `Inst (Mem Store n (Addr n0 w))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_store_full" store_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_store_type_st" "st" store_case;
val _ = ty "inst_store_type_cst" "cst" store_case;
val _ = ty "inst_store_type_dst" "n" store_case;
val _ = ty "inst_store_type_src" "n0" store_case;
val _ = ty "inst_store_type_offset" "w" store_case;
val _ = ty "inst_store_type_ssa" "ssa" store_case;
val _ = ty "inst_store_type_next" "na" store_case;
val _ = ty "inst_store_type_tables" "lt" store_case;
