(* Typed source declarations for mllist (task 273). *)
load "preamble";
load "mllistTheory";
open HolKernel Parse boolLib bossLib;
open preamble mllistTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="mllist",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by mllist")
  | SOME (th,_) => show label th;

val _ = emit "sort2_tail_sort2_typed" "sort2_tail_sort2";
val _ = emit "sort3_tail_sort3_typed" "sort3_tail_sort3";
val _ = emit "mergetail_merge_typed" "mergetail_merge";
val _ = emit "merge_tail_acc_typed" "merge_tail_acc";
val _ = emit "merge_tail_MEM_typed" "merge_tail_MEM";
val _ = emit "mergesortN_tail_MEM_typed" "mergesortN_tail_MEM";
val _ = emit "mergesort_tail_MEM_typed" "mergesort_tail_MEM";
val _ = emit "merge_tail_PERM_typed" "merge_tail_PERM";
val _ = emit "sort2_tail_PERM_typed" "sort2_tail_PERM";
val _ = emit "sort3_tail_PERM_typed" "sort3_tail_PERM";
val _ = emit "mergesortN_tail_PERM_typed" "mergesortN_tail_PERM";
val _ = emit "sort_set_typed" "sort_set";
val _ = emit "FIND_thm_typed" "FIND_thm";
val _ = emit "index_find_thm_typed" "index_find_thm";
val _ = emit "list_compare_def_typed" "list_compare_def";
val _ = emit "foldli_thm_typed" "foldli_thm";
val _ = emit "MAPI_thm_typed" "MAPI_thm";
val _ = emit "collate_cpn_reln_thm_typed" "collate_cpn_reln_thm";
val _ = emit "tabulate_GENLIST_typed" "tabulate_GENLIST";
