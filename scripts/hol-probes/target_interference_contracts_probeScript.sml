load "preamble";
load "targetSemTheory";
load "targetPropsTheory";
open HolKernel Parse preamble targetSemTheory targetPropsTheory;
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has theorem hypotheses");
val _ = emit "ffi_contract_full_definition" ffi_interfer_ok_def;
val _ = emit "cache_contract_full_definition" ccache_interfer_ok_def;
val _ = emit "post_ffi_state_full_statement" ffi_interfer_ok_post_ffi_asm;
val _ = emit "post_cache_state_full_statement" ccache_interfer_ok_post_ccache_asm;
val _ = OS.Process.exit OS.Process.success;
