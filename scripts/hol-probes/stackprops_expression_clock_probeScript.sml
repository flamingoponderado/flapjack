(* Original full memory/expression/assignment clock commutation and observations.
Captures are regression evidence, not HOL-to-Lean equivalence. *)
load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
  print (term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
  (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "ec_store_statement" (DB.fetch "stackProps" "mem_load_with_const");
val _ = captureTypes "ec_store_types" (DB.fetch "stackProps" "mem_load_with_const");
val _ = capture "ec_word_statement" (DB.fetch "stackProps" "word_exp_with_const");
val _ = captureTypes "ec_word_types" (DB.fetch "stackProps" "word_exp_with_const");
val _ = capture "ec_assign_statement" (DB.fetch "stackProps" "assign_with_const");
val _ = captureTypes "ec_assign_types" (DB.fetch "stackProps" "assign_with_const");
fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = show_types := false;
val _ = observe "ec_const" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Const 255w)``;
val _ = observe "ec_var_word" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Var 1)``;
val _ = observe "ec_var_loc" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Var 2)``;
val _ = observe "ec_var_missing" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Var 3)``;
val _ = observe "ec_lookup_word" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Lookup AllocSize)``;
val _ = observe "ec_lookup_loc" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Lookup NextFree)``;
val _ = observe "ec_lookup_missing" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Lookup TriggerGC)``;
val _ = observe "ec_load_word" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Load (Const 0w))``;
val _ = observe "ec_load_loc" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Load (Const 1w))``;
val _ = observe "ec_load_oob" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Load (Const 2w))``;
val _ = observe "ec_load_bad_address" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Load (Var 2))``;
val _ = observe "ec_op_empty_and" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Op And [])``;
val _ = observe "ec_op_add_wrap" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Op Add [Const 255w;Const 2w])``;
val _ = observe "ec_op_sub_bad_arity" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Op Sub [Const 1w])``;
val _ = observe "ec_op_bad_operand" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Op Add [Const 1w;Var 2])``;
val _ = observe "ec_shift_valid" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Shift Lsl (Const 3w) (Const 2w))``;
val _ = observe "ec_shift_oob" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Shift Lsl (Const 3w) (Const 8w))``;
val _ = observe "ec_shift_bad_right" ``stackSem$word_exp ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>) (Shift Lsr (Const 3w) (Var 2))``;
val _ = observe "ec_assign_success" ``OPTION_MAP (λs. (FLOOKUP s.regs 1,FLOOKUP s.regs 2)) (stackSem$assign 1 (Const 12w) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>))``;
val _ = observe "ec_assign_failure" ``OPTION_MAP (λs. (FLOOKUP s.regs 1,FLOOKUP s.regs 2)) (stackSem$assign 1 (Var 2) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);store := FEMPTY |+ (AllocSize,Word 9w) |+ (NextFree,Loc 2 3);memory := (λa. if a = 0w then Word 11w else Loc 8 9);mdomain := {0w;1w};clock := 19|>))``;
val _ = observe "ec_store_success" ``OPTION_MAP (λs. (s.clock,s.memory 0w)) (stackSem$mem_store 0w (Loc 4 5) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY;store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>))``;
val _ = observe "ec_store_failure" ``OPTION_MAP (λs. (s.clock,s.memory 0w)) (stackSem$mem_store 1w (Word 7w) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY;store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>))``;
