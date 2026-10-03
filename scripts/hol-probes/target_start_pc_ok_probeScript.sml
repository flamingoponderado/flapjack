load "bossLib";
load "preamble";
load "targetSemTheory";
open bossLib HolKernel Parse preamble targetSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t = DB.fetch "targetSem" "start_pc_ok_def";
val _ = capture "start_pc_ok_def" t;
val _ = types "start_pc_ok_def_types" t;
val _ = print("start_pc_ok_def_hypotheses=" ^ Int.toString(length(hyp t)) ^ "\n");
val _ = show_types := false;
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO th))); print "\n");
val _ = checked "lengths" (prove(
  ``start_pc_ok mc pc ==> LENGTH mc.ffi_names = LENGTH mc.ffi_entry_pcs``,
  simp [start_pc_ok_def] >> metis_tac []));
val _ = checked "entry_bound" (prove(
  ``start_pc_ok mc pc /\ index < LENGTH mc.ffi_names ==>
    index < LENGTH mc.ffi_entry_pcs``,
  simp [start_pc_ok_def] >> metis_tac []));
val _ = checked "halt_cache" (prove(
  ``start_pc_ok mc pc ==>
    mc.halt_pc NOTIN mc.prog_addresses /\
    mc.ccache_pc NOTIN mc.prog_addresses /\
    mc.halt_pc NOTIN mc.shared_addresses /\
    mc.ccache_pc NOTIN mc.shared_addresses /\
    pc - n2w ffi_offset = mc.halt_pc /\
    pc - n2w (2 * ffi_offset) = mc.ccache_pc /\
    (1w && pc) = 0w``, simp [start_pc_ok_def]));
