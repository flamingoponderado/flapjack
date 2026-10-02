load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture the kernel theorem's fixed native Load constructor specialization.
   The source opcode proof remains at word_allocProofScript.sml:8115-8123.
   No standalone tactic replay is claimed. *)
val load_case = Q.SPEC `Inst (Mem Load n (Addr n0 w))` ssa_cc_trans_correct;
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_load_full" load_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_load_type_st" "st" load_case;
val _ = ty "inst_load_type_cst" "cst" load_case;
val _ = ty "inst_load_type_dst" "n" load_case;
val _ = ty "inst_load_type_src" "n0" load_case;
val _ = ty "inst_load_type_offset" "w" load_case;
val _ = ty "inst_load_type_ssa" "ssa" load_case;
val _ = ty "inst_load_type_next" "na" load_case;
val _ = ty "inst_load_type_tables" "lt" load_case;
