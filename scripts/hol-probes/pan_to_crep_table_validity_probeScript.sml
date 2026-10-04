load "preamble";
load "pan_to_wordProofTheory";
open HolKernel Parse bossLib preamble pan_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th =
  let val full = GEN_ALL th in
    if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
    print(label ^ "=" ^ term_to_string(concl full) ^ "\n")
  end;
val _ = emit "every_inst_ok_less_pan_to_crep_compile_to_crep" every_inst_ok_less_pan_to_crep_compile_to_crep;
