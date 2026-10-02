load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Capture original kernel theorem constructor specializations. No standalone
   tactic replay is claimed; original FP opcode proof8174-8222 is compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val to_int_case = Q.SPEC `Inst (FP (FPToInt n n0))` ssa_cc_trans_correct;
val _ = out "fp_to_int_full" to_int_case;
val _ = ty "fp_to_int_type_st" "st" to_int_case;
val _ = ty "fp_to_int_type_cst" "cst" to_int_case;
val _ = ty "fp_to_int_type_dst" "n" to_int_case;
val _ = ty "fp_to_int_type_arg" "n0" to_int_case;
val _ = ty "fp_to_int_type_ssa" "ssa" to_int_case;
val _ = ty "fp_to_int_type_next" "na" to_int_case;
val _ = ty "fp_to_int_type_tables" "lt" to_int_case;
val from_int_case = Q.SPEC `Inst (FP (FPFromInt n n0))` ssa_cc_trans_correct;
val _ = out "fp_from_int_full" from_int_case;
val _ = ty "fp_from_int_type_st" "st" from_int_case;
val _ = ty "fp_from_int_type_cst" "cst" from_int_case;
val _ = ty "fp_from_int_type_dst" "n" from_int_case;
val _ = ty "fp_from_int_type_arg" "n0" from_int_case;
val _ = ty "fp_from_int_type_ssa" "ssa" from_int_case;
val _ = ty "fp_from_int_type_next" "na" from_int_case;
val _ = ty "fp_from_int_type_tables" "lt" from_int_case;
