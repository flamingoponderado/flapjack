load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory finite_mapTheory;
val _ = Globals.linewidth := 1000000;
val original = convert_eshapes_def;
val correspondence = prove(``!ctxt eshapes eid.
  FLOOKUP (convert_eshapes ctxt eshapes) eid =
  OPTION_MAP (compile_shape ctxt) (FLOOKUP eshapes eid)``,
  simp [convert_eshapes_def,FLOOKUP_FMAP_MAP2,SF ETA_ss]);
val _ = (print "convert_eshapes_definition="; print_term(concl original); print "\n");
val _ = (print "convert_eshapes_type="; print_type(type_of ``convert_eshapes``); print "\n");
val _ = print("convert_eshapes_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = (print "convert_eshapes_lookup_statement="; print_term(concl correspondence); print "\n");
val _ = print("convert_eshapes_lookup_proved=" ^ term_to_string(rhs(concl(EQT_INTRO correspondence))) ^ "\n");
