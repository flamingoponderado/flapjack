(* Full original StackRemove code relation/type and kernel-proved complete
   relation fixtures. CakeML theories are read-only; no source amendments. *)
load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("cr_full_def=" ^ term_to_string (concl code_rel_def) ^ "\n");
val _ = print ("cr_full_type=" ^ type_to_string (type_of ``code_rel``) ^ "\n");
fun check label expected q =
  let val th = prove ((if expected then q else mk_neg q),
    simp [code_rel_def, sptreeTheory.lookup_fromAList, sptreeTheory.domain_fromAList,
      sptreeTheory.lookup_def, pred_setTheory.EXTENSION] >>
    rpt strip_tac >> every_case_tac >> fs [Once reg_bound_def, Once comp_def])
      val eq = if expected then EQT_INTRO th else EQF_INTRO th
  in print (label ^ "=" ^ term_to_string (rhs (concl eq)) ^ "\n") end;
val _ = check "cr_empty_1" true ``code_rel T (0w,0w) 24 (LN : 1 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip)])``;
val _ = check "cr_empty_8" true ``code_rel T (0w,0w) 24 (LN : 8 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip)])``;
val _ = check "cr_empty_32" true ``code_rel T (0w,0w) 24 (LN : 32 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip)])``;
val _ = check "cr_empty_64" true ``code_rel T (0w,0w) 24 (LN : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip)])``;
val _ = check "cr_empty_80" true ``code_rel T (0w,0w) 24 (LN : 80 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip)])``;
val _ = check "cr_missing_stub" false ``code_rel F (0w,0w) 24 (LN : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip)])``;
val _ = check "cr_extra_target" false ``code_rel T (0w,0w) 24 (LN : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip);(99,Tick)])``;
val _ = check "cr_tick" true ``code_rel T (0w,0w) 24 (fromAList [(9,Tick)] : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip);(9,Tick)])``;
val _ = check "cr_wrong_body" false ``code_rel T (0w,0w) 24 (fromAList [(9,Tick)] : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip);(9,Skip)])``;
val _ = check "cr_bad_register" false ``code_rel F (0w,0w) 24 (fromAList [(9,Get 24 CurrHeap)] : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip);(9,Inst (Arith (Binop Or 24 26 (Reg 26))))])``;
val _ = check "cr_reserved_source" true ``code_rel T (0w,0w) 24 (fromAList [(0,Tick)] : 64 stackLang$prog sptree$spt) (fromAList [(0,Tick);(1,Skip);(2,Skip)])``;
val _ = check "cr_malformed_source" true ``code_rel T (0w,0w) 24 (BN LN LN : 64 stackLang$prog sptree$spt) (fromAList [(0,Skip);(1,Skip);(2,Skip)])``;
