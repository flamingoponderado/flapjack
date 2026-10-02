(* Original HOL share_mem_state_rel (lab_to_targetProofScript.sml:720-774): the full typed
   definition, a satisfied instance (no FFI names: both conjuncts are vacuous since
   index < LENGTH [] fails) and a violated one (one SharedMem name whose entry PC is the halt PC,
   using the proved mmio_pcs_min_index [SharedMem MappedRead] = SOME 0). *)
load "lab_to_targetProofTheory";
open HolKernel Parse boolLib bossLib lab_to_targetProofTheory targetSemTheory;
val _ = Globals.linewidth := 6000;
fun observe_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = Globals.show_types := true;
val _ = observe_thm "smsr_def" share_mem_state_rel_def;
val _ = Globals.show_types := false;
val sh = prove (``(!j:num. x <= j /\ j < n ==> P j) <=> (!j. j < n ==> x <= j ==> P j)``, metis_tac []);
val bound = DECIDE ``!x:num. x <= 1 <=> x = 0 \/ x = 1``;
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ boolSimps.CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val mmio1 = prove (``mmio_pcs_min_index [SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = observe_thm "smsr_nil" (prove (``!mc s1 t1 ms1. mc.ffi_names = [] ==> share_mem_state_rel mc s1 t1 ms1``,
  rw [share_mem_state_rel_def]));
val _ = observe_thm "smsr_halt" (prove (``!mc s1 t1 ms1 w. mc.ffi_names = [SharedMem MappedRead] /\
    mc.ffi_entry_pcs = [w] /\ mc.halt_pc = w ==> ~share_mem_state_rel mc s1 t1 ms1``,
  rpt strip_tac >> fs [share_mem_state_rel_def] >>
  first_x_assum (qspecl_then [`0`, `0`] mp_tac) >> simp [mmio1]));
