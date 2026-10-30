load "bvl_handleTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "simplify="; print_term (rhs (concl (EVAL ``
 MAP bvl_handle$handle_simp
   [bvl$Handle (bvl$Let [bvl$Var 0] (bvl$Raise (bvl$Var 0))) (bvl$Var 1);
    bvl$Handle (bvl$If (bvl$Var 0) (bvl$Raise (bvl$Var 1)) (bvl$Var 2)) (bvl$Var 1);
    bvl$Handle (bvl$Call 0 (SOME 2) []) (bvl$Force 9 1)]``))); print "\n");
val _ = (print "compiled="; print_term (rhs (concl (EVAL ``
 MAP (bvl_handle$compile_sing 20 3)
   [bvl$Handle (bvl$Call 0 (SOME 2) [bvl$Var 2; bvl$Var 0]) (bvl$Var 1);
    bvl$Handle (bvl$Var 1) (bvl$Var 0); bvl$Force 4 9]``))); print "\n");
val _ = (print "cut="; print_term (rhs (concl (EVAL ``
 bvl_handle$compile_sing 2 3 (bvl$Call 0 (SOME 4) [bvl$Var 2; bvl$Var 0])``))); print "\n");
val _ = (print "seq="; print_term (rhs (concl (EVAL ``
 bvl_handle$compile_seqs 100 (bvl$Let [bvl$Call 0 (SOME 1) []; bvl$Call 0 (SOME 2) []] (bvl$Var 1)) NONE``))); print "\n");
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "can_raise=" bvl_handleTheory.can_raise_def;
val _ = show "dest_handle_Raise=" bvl_handleTheory.dest_handle_Raise_def;
val _ = show "dest_handle_Let=" bvl_handleTheory.dest_handle_Let_def;
val _ = show "dest_handle_If=" bvl_handleTheory.dest_handle_If_def;
val _ = show "handle_adj_vars=" bvl_handleTheory.handle_adj_vars_def;
val _ = show "handle_size=" bvl_handleTheory.handle_size_def;
load "preamble";
open preamble bvl_handleTheory;
val handle_size_non_zero_replay = prove (``0 < handle_size x``,
  Cases_on `x` \\ fs [handle_size_def]);
val _ = show "handle_size_non_zero_replay=" handle_size_non_zero_replay;
