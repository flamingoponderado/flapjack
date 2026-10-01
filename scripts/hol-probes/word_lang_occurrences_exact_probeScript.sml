load "preamble";
load "wordLangTheory";
open bossLib HolKernel Parse preamble wordLangTheory;
fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");
val P = ``(\(n:num). n MOD 2 = 0)``;
(* Literal original occurrence predicates, including ignored ill-formed Call
   handlers under NONE return and Loop local/stack cutset distinction. *)
val _ = print_eval "name_empty" ``every_name ^P ((LN,LN):wordLang$cutsets)``;
val _ = print_eval "name_even" ``every_name ^P (fromAList [(2,());(4,())], fromAList [(6,())])``;
val _ = print_eval "name_odd" ``every_name ^P (fromAList [(2,())], fromAList [(3,())])``;
val _ = print_eval "var_move_even" ``every_var ^P (Move 0 [(2,4)] : 8 wordLang$prog)``;
val _ = print_eval "var_move_odd" ``every_var ^P (Move 0 [(2,3)] : 8 wordLang$prog)``;
val _ = print_eval "var_loop_live" ``every_var ^P (Loop (fromAList [(3,())]) Skip (fromAList [(2,())]) : 8 wordLang$prog)``;
val _ = print_eval "stack_loop_live" ``every_stack_var ^P (Loop (fromAList [(3,())]) Skip (fromAList [(2,())]) : 8 wordLang$prog)``;
val _ = print_eval "stack_alloc_odd" ``every_stack_var ^P (Alloc 2 (LN,fromAList [(3,())]) : 8 wordLang$prog)``;
val _ = print_eval "var_call_none" ``every_var ^P (Call NONE NONE [2] (SOME (3,Raise 3,1,0)) : 8 wordLang$prog)``;
val _ = print_eval "stack_call_none" ``every_stack_var ^P (Call NONE NONE [2] (SOME (3,Alloc 2 (LN,fromAList [(3,())]),1,0)) : 8 wordLang$prog)``;
val _ = print_eval "var_call_some" ``every_var ^P (Call (SOME ([2],(LN,LN),Skip,1,0)) NONE [2] (SOME (3,Raise 3,1,0)) : 8 wordLang$prog)``;
val _ = print_eval "stack_call_some" ``every_stack_var ^P (Call (SOME ([2],(LN,LN),Skip,1,0)) NONE [2] (SOME (2,Alloc 2 (LN,fromAList [(3,())]),1,0)) : 8 wordLang$prog)``;
