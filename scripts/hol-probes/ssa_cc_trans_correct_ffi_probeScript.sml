load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
(* Original kernel specialization; FFI9868-10010 manually compared. *)
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val ffi_case = Q.SPEC `wordLang$FFI (s:mlstring) (n:num) (n0:num) (n1:num) (n2:num) (p:num_set # num_set)` ssa_cc_trans_correct;
val _ = out "ffi_full" ffi_case;
val _ = ty "ffi_type_name" "s" ffi_case;
val _ = ty "ffi_type_pointer" "n" ffi_case;
val _ = ty "ffi_type_length" "n0" ffi_case;
val _ = ty "ffi_type_cutsets" "p" ffi_case;
val _ = ty "ffi_type_st" "st" ffi_case;
val _ = ty "ffi_type_cst" "cst" ffi_case;
val _ = ty "ffi_type_ssa" "ssa" ffi_case;
val _ = ty "ffi_type_next" "na" ffi_case;
val _ = ty "ffi_type_tables" "lt" ffi_case;
