load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory set_sepTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("sm_def=" ^ term_to_string (concl memory_def) ^ "\n");
val _ = print ("sm_type=" ^ type_to_string (type_of ``stack_removeProof$memory``) ^ "\n");
fun check label q = let val th = prove(q,
  simp [memory_def,EXTENSION,FORALL_PROD,fun2set_def,fun2set_thm,IN_DEF] >> metis_tac [DECIDE ``(0:num) <> 1``])
  in print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n") end;
val _ = check "sm_full_generic" ``!m:'a->'b d. memory m d (fun2set(m,d))``;
val _ = check "sm_unique" ``!m:'a->'b d s t. memory m d s /\ memory m d t ==> s=t``;
val _ = check "sm_empty" ``!m:'a->'b. memory m {} {}``;
val _ = check "sm_infinite" ``!m:num->bool. memory m UNIV {(address,m address) | address IN UNIV}``;
val _ = check "sm_independent" ``memory (\b:bool. if b then 7 else 11) UNIV {(T,7);(F,11)}``;
val _ = check "sm_product" ``!m:bool->num#bool. memory m UNIV (fun2set(m,UNIV))``;
val _ = check "sm_missing" ``~memory (\n:num. F) {0} {}``;
val _ = check "sm_extra" ``~memory (\n:num. F) {} {(0,F)}``;
val _ = check "sm_wrong_value" ``~memory (\n:num. F) {0} {(0,T)}``;
val _ = check "sm_wrong_address" ``~memory (\n:num. F) {0} {(1,F)}``;
val _ = check "sm_noninjective" ``memory (\n:num. F) {1;2} {(1,F);(2,F)}``;
