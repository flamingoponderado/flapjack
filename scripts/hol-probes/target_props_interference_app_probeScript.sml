load "preamble";
load "targetPropsTheory";
open preamble HolKernel Parse boolLib bossLib targetPropsTheory;
fun emit label tm = let val th = SIMP_CONV (srw_ss()) [is_ffi_app_def, app_post_def] tm in
 if aconv (rhs(concl th)) ``T`` then print(label ^ "=T\n")
 else raise Fail (label ^ " did not reduce to T") end;
fun ty label tm = print(label ^ "=" ^ type_to_string(type_of tm) ^ "\n");
val _ = ty "ia_ffi_type" ``FfiApp``;
val _ = ty "ia_cc_type" ``CcApp``;
val _ = ty "ia_isffi_type" ``is_ffi_app``;
val _ = ty "ia_post_type" ``app_post``;
val _ = emit "ia_ffi_classifier" ``!i bs pre post. is_ffi_app (FfiApp i bs pre post)``;
val _ = emit "ia_cc_classifier" ``!a b pre post. ~is_ffi_app (CcApp a b pre post)``;
val _ = emit "ia_ffi_post" ``!i bs pre post. app_post (FfiApp i bs pre post) = post``;
val _ = emit "ia_cc_post" ``!a b pre post. app_post (CcApp a b pre post) = post``;
val _ = OS.Process.exit OS.Process.success;
