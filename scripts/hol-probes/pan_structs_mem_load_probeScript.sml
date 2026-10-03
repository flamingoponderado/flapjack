load "bossLib";
load "preamble";
load "pan_structsProofTheory";
open bossLib HolKernel Parse preamble pan_structsProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
val _ = capture "mem_load_flds_eq" (DB.fetch "pan_structsProof" "mem_load_flds_eq");
val _ = capture "mem_loads_EL" (DB.fetch "pan_structsProof" "mem_loads_EL");
val _ = capture "mem_loads_mem" (DB.fetch "pan_structsProof" "mem_loads_mem");
val _ = capture "mem_load_conversion" (DB.fetch "pan_structsProof" "mem_load_conversion");
val inst = mem_load_conversion |> SIMP_RULE bool_ss []
  |> Q.SPEC `0` |> SIMP_RULE list_ss [compile_shape_n_eq];
val _ = capture "mem_load_conversion_inst" inst;
