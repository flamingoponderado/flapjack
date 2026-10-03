load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
val original = convert_code_def;
val _ = (print "convert_code_definition="; print_term(concl original); print "\n");
val _ = (print "convert_code_type="; print_type(type_of ``convert_code``); print "\n");
val _ = print("convert_code_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
