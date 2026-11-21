(* Typed source declarations for the pan_commonProps finite-map lemmas that
   are stated over HOL `|->` maps (pan_commonPropsScript.sml:156, :263, :289,
   :319, :345, :479, :510, :520, :575, :546, :595, :615, :780).  These
   captures support source review of the exact-carrier Lean twins; they do not
   establish HOL-to-Lean equivalence. *)
load "preamble";
load "pan_commonPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble pan_commonPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "opt_mmap_flookup_update_typed" opt_mmap_flookup_update;
val _ = show "update_eq_zip_map_flookup_typed" update_eq_zip_map_flookup;
val _ = show "flookup_fupdate_zip_not_mem_typed" flookup_fupdate_zip_not_mem;
val _ = show "domsub_commutes_fupdate_typed" domsub_commutes_fupdate;
val _ = show "fm_multi_update_typed" fm_multi_update;
val _ = show "fm_empty_zip_flookup_el_typed" fm_empty_zip_flookup_el;
val _ = show "all_distinct_flookup_all_distinct_typed" all_distinct_flookup_all_distinct;
val _ = show "no_overlap_flookup_distinct_typed" no_overlap_flookup_distinct;
val _ = show "not_mem_fst_zip_flookup_empty_typed" not_mem_fst_zip_flookup_empty;
val _ = show "fupdate_flookup_zip_elim_typed" fupdate_flookup_zip_elim;
val _ = show "fm_zip_append_take_drop_typed" fm_zip_append_take_drop;
val _ = show "map_some_the_map_typed" map_some_the_map;
val _ = show "fm_update_diff_vars_typed" fm_update_diff_vars;
