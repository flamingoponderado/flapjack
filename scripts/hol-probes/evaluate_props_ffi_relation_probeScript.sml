load "preamble"; load "evaluatePropsTheory";
open HolKernel Parse bossLib preamble evaluatePropsTheory ffiTheory;
val _ = Globals.linewidth := 100000;
val _ = print ("ffi_rel_full_def=" ^ term_to_string (concl call_FFI_rel_def) ^ "\n");
val _ = print ("ffi_rel_type=" ^ type_to_string (type_of ``call_FFI_rel``) ^ "\n");
val identity = prove (``!s. call_FFI_rel s s``,
  rw [call_FFI_rel_def] >>
  qexists_tac `ExtCall «»` >> qexists_tac `[]` >>
  qexists_tac `[]` >> qexists_tac `[]` >> simp [call_FFI_def]);
val _ = if null (hyp identity) then print "ffi_rel_identity=T\n"
  else raise Fail "identity has assumptions";
val _ = OS.Process.exit OS.Process.success;
