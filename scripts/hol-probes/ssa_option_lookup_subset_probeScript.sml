load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val result = prove (``∀ssa cst_locs ls.
    (∀x y. lookup x ssa = SOME y ⇒ y ∈ domain cst_locs) ∧
    set ls ⊆ domain ssa ⇒
    set (MAP (option_lookup ssa) ls) ⊆ domain cst_locs``,
  rw[SUBSET_DEF,MEM_MAP]>>
  `y ∈ domain ssa` by metis_tac[]>>
  fs[domain_lookup]>>
  rename1`lookup y ssa = SOME z`>>
  `option_lookup ssa y = z` by simp[option_lookup_def]>>
  res_tac>>fs[]);
val _ = print "os_full=";
val _ = print_thm result;
val _ = print "\n";
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (fst(strip_forall(concl result)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "os_type_ssa" "ssa";
val _ = out "os_type_cst_locs" "cst_locs";
val _ = out "os_type_ls" "ls";
