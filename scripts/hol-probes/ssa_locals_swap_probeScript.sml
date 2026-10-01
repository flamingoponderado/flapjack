load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory;
val statement = ``ssa_locals_rel na ssaR st.locals cst.locals /\
  domain ssaL = domain ssaR /\
  (!x. lookup x ssaL = lookup x ssaR) ==>
  ssa_locals_rel na ssaL st.locals cst.locals``;
fun out label name =
  let val term = valOf(List.find (fn t => fst(dest_var t) = name)
      (free_vars statement))
  in print(label ^ "="); print_type(type_of term); print "\n" end;
val _ = out "sw_type_ssaL" "ssaL";
val _ = out "sw_type_cst" "cst";
val _ = out "sw_type_st" "st";
val _ = out "sw_type_ssaR" "ssaR";
val _ = out "sw_type_na" "na";
val result = prove(statement, srw_tac[][ssa_locals_rel_def]);
val _ = print "sw_full=";
val _ = print_thm result;
val _ = print "\n";
