load "preamble";
load "asmPropsTheory";
open preamble HolKernel Parse boolLib bossLib asmPropsTheory;
val statement = ``!env proj. interference_ok env proj <=> (!i ms. proj (env i ms) = proj ms)``;
val th = prove(statement, SIMP_TAC (srw_ss()) [interference_ok_def]);
val _ = if aconv (concl th) statement andalso null(hyp th)
 then print "interference_ok_full=T\n" else raise Fail "interference_ok statement mismatch";
val _ = print ("interference_ok_type=" ^ type_to_string(type_of ``interference_ok``) ^ "\n");
val identity = SIMP_CONV (srw_ss()) [interference_ok_def] ``interference_ok (\i (ms:num). ms) (\ms. ms)``;
val _ = if aconv(rhs(concl identity)) ``T`` then print "interference_ok_identity=T\n"
 else raise Fail "identity oracle mismatch";
val changed = SIMP_CONV (srw_ss()) [interference_ok_def] ``interference_ok (\i (ms:num). ms + 1) (\ms. ms)``;
val _ = if aconv(rhs(concl changed)) ``F`` then print "interference_ok_changed=F\n"
 else raise Fail "changed oracle mismatch";
val _ = OS.Process.exit OS.Process.success;
