load "riscvTheory";
open HolKernel Parse bossLib Tactical boolSyntax riscvTheory;
val _ = Globals.linewidth := 100000;
val _ = print ("raise_exception_type=" ^ type_to_string (type_of ``raise'exception``) ^ "\n");
val _ = print "raise_exception_equation=";
val th = prove (``raise'exception e s = ((ARB:'a), if s.exception = NoException then s with exception := e else s)``,
  SIMP_TAC (srw_ss()) [raise'exception_def]);
val _ = if null(hyp th) then (print_thm th; print "\n") else raise Fail "undischarged assumptions";
