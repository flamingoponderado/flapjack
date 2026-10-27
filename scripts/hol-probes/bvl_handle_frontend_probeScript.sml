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
