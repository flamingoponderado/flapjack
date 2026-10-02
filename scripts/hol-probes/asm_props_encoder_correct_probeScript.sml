(* Original HOL encoder_correct (asmPropsScript.sml:117-133): the full typed definition and two
   HOL-proved consumers, the target_ok projection and the specialization to the identity
   interference environment (which preserves every projection). *)
load "asmPropsTheory";
open HolKernel Parse boolLib bossLib asmPropsTheory;
val _ = Globals.linewidth := 6000;
fun observe_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = Globals.show_types := true;
val _ = observe_thm "ec_def" encoder_correct_def;
val _ = Globals.show_types := false;
val _ = observe_thm "ec_target_ok" (prove (``encoder_correct t ==> target_ok t``, simp [encoder_correct_def]));
val _ = observe_thm "ec_no_interference" (prove (``encoder_correct t /\ asm_step t.config s1 i s2 /\
    target_state_rel t s1 ms ==>
    ?n. asserts n (\k s. t.next s) ms
          (\ms'. t.state_ok ms' /\
                 (!pc. pc IN all_pcs (LENGTH (t.config.encode i)) s1.pc 0 ==> t.get_byte ms' pc = t.get_byte ms pc) /\
                 t.get_pc ms' IN all_pcs (LENGTH (t.config.encode i)) s1.pc t.config.code_alignment)
          (\ms'. target_state_rel t s2 ms') /\
        asserts2 (n + 1) (\k x. x) t.next ms
          (\ms1 ms2. !x. x NOTIN s1.mem_domain ==> t.get_byte ms1 x = t.get_byte ms2 x)``,
  rw [encoder_correct_def] >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `n` >> first_x_assum (qspec_then `\k x. x` mp_tac) >>
  simp [interference_ok_def] >> simp [ETA_AX]));
