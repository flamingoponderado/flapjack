load "riscvTheory";load "wordsLib";
open HolKernel Parse bossLib Tactical Tactic boolSyntax Conv riscvTheory;
val _=Globals.linewidth:=100000;
val th=prove(``rawWriteData(a,d,n)s = s with MEM8 := (rawWriteData(a,d,n)s).MEM8``,SIMP_TAC(srw_ss())[rawWriteData_def,boolTheory.LET_THM] THEN REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC(srw_ss())[write'MEM_def,boolTheory.LET_THM]);
val _=if null(hyp th) then(print "raw_write_frame=";print_thm th;print "\n")else raise Fail "assumptions";
