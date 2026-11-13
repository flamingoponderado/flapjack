(* Typed statements of the HOL `alist`/`finite_map` declarations ported in
   `Flapjack/FiniteMap/*.lean` that the existing finite_map probe does not cover,
   from the built HOL4 core theories (no rebuild). *)
load "alistTheory";
load "finite_mapTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "ALOOKUP_def_typed=" alistTheory.ALOOKUP_def;
val _ = show_thm "ALOOKUP_APPEND_typed=" alistTheory.ALOOKUP_APPEND;
val _ = show_thm "ALOOKUP_MEM_typed=" alistTheory.ALOOKUP_MEM;
val _ = show_thm "ALOOKUP_ALL_DISTINCT_MEM_typed=" alistTheory.ALOOKUP_ALL_DISTINCT_MEM;
val _ = show_thm "alist_to_fmap_def_typed=" alistTheory.alist_to_fmap_def;
val _ = show_thm "alist_to_fmap_APPEND_typed=" alistTheory.alist_to_fmap_APPEND;
val _ = show_thm "FUPDATE_LIST_typed=" finite_mapTheory.FUPDATE_LIST;
val _ = show_thm "FCARD_FUPDATE_typed=" finite_mapTheory.FCARD_FUPDATE;
