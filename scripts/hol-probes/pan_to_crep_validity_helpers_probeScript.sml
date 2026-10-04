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
val _ = emit "exps_of_nested_seq" exps_of_nested_seq;
val _ = emit "every_inst_ok_nested_decs" every_inst_ok_nested_decs;
val _ = emit "every_inst_ok_less_pan_to_crep_comp_field" every_inst_ok_less_pan_to_crep_comp_field;
val _ = emit "every_inst_ok_less_pan_to_crep_load_shape" every_inst_ok_less_pan_to_crep_load_shape;
val _ = emit "every_inst_ok_less_pan_to_crep_cexp_heads" every_inst_ok_less_pan_to_crep_cexp_heads;
val _ = emit "every_inst_ok_less_stores" every_inst_ok_less_stores;
val _ = emit "every_inst_ok_less_store_globals" every_inst_ok_less_store_globals;
