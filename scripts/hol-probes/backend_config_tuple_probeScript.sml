load "preamble"; load "backendTheory";
open HolKernel Parse bossLib preamble backendTheory;
val _ = new_theory "flapjack_backend_config_tuple_replay";
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

(* Literal replay of backendProofScript.sml:329-339; backendProofTheory is not built. *)
Definition config_tuple2_def:
  config_tuple2 c = (c.bvl_conf.inlines, c.bvl_conf.next_name1,
    c.bvl_conf.next_name2, c.bvl_conf.next_name3, c.bvl_conf.bvi_inlines,
    c.word_conf.bitmaps_length, c.lab_conf)
End

Definition config_tuple1_def:
  config_tuple1 c = (c.source_conf, c.clos_conf.next_loc,
    clos_known$option_val_approx_spt c.clos_conf.known_conf,
    FST c.clos_conf.call_state, config_tuple2 c)
End

fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "config_tuple2_typed=" config_tuple2_def;
val _ = show_thm "config_tuple1_typed=" config_tuple1_def;
val _ = (print "config_tuple2_type="; print_type (type_of ``config_tuple2``); print "\n");
val _ = (print "config_tuple1_type="; print_type (type_of ``config_tuple1``); print "\n");
