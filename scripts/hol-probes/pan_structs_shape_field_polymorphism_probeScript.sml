load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
val original = compile_shape_def;
val map_theorem = GEN_ALL(prove(``!shs. compile_shapes sctxt shs = MAP (compile_shape sctxt) shs``,
  Induct >> simp [compile_shape_def]));
val _ = (print "compile_shape_definition="; print_term(concl original); print "\n");
val _ = (print "compile_shape_type="; print_type(type_of ``compile_shape``); print "\n");
val _ = (print "compile_shapes_type="; print_type(type_of ``compile_shapes``); print "\n");
val _ = print("compile_shape_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = (print "compile_shapes_eq_map_statement="; print_term(concl map_theorem); print "\n");
val _ = print("compile_shapes_eq_map_proved=" ^ term_to_string(rhs(concl(EQT_INTRO map_theorem))) ^ "\n");
