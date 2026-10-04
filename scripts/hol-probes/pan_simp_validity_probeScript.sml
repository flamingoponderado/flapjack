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
val _ = emit "every_inst_ok_less_ret_to_tail" every_inst_ok_less_ret_to_tail;
val _ = emit "every_inst_ok_less_seq_assoc" every_inst_ok_less_seq_assoc;
val _ = emit "every_inst_ok_less_pan_simp_compile" every_inst_ok_less_pan_simp_compile;
val _ = emit "every_inst_ok_less_pan_simp_compile_prog" every_inst_ok_less_pan_simp_compile_prog;
