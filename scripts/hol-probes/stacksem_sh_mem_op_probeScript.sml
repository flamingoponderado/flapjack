(* Direct source observations for the StackSem evaluate_def ShMemOp clause.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:922-927.
   The clause computes the effective address with
   word_exp s (Op Add [Var a; Const w]); a miss returns (SOME Error,s), a zero
   clock returns (SOME TimeOut,empty_env s), and otherwise
   sh_mem_op op r a (dec_clock s) runs.  A byte-incrementing FFI oracle makes
   the successful row observable through ffi_state, and the observer records
   result, clock, ffi_state, register 3 and the stack length. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

val inc = ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) (MAP (\b. b + 1w) bytes));
               ffi_state := 0; io_events := [] |>``;

val base = ``(ARB : (64,unit,unit) stackSem$state) with <|
    code_buffer := <| position := 0w; buffer := [] : 8 word list; space_left := 2 |>;
    data_buffer := <| position := 0w; buffer := [] : 64 word list; space_left := 2 |>;
    sh_mdomain := {8w}; ffi := ^inc; stack := [Word 9w] |>``;

(* (a) successful ShMemOp: word_exp evaluates 0w + 8w = 8w, the clock is 5 so
   dec_clock gives 4, and sh_mem_op Load invokes the incrementing oracle. *)
val _ = observe "sh_mem_op_success"
  ``let s = ^base with <| regs := FEMPTY |+ (3,Word 0w); clock := 5 |> in
    let (r,s1) = stackSem$evaluate (ShMemOp Load 5 (Addr 3 8w), s) in
      (r, s1.clock, s1.ffi.ffi_state, FLOOKUP s1.regs 3, LENGTH s1.stack)``;

(* (b) word_exp miss: register 3 holds a Loc, so Op Add [Var 3; Const 8w] is
   NONE and the clause returns Error with the original state. *)
val _ = observe "sh_mem_op_word_exp_none"
  ``let s = ^base with <| regs := FEMPTY |+ (3,Loc 1 0); clock := 5 |> in
    let (r,s1) = stackSem$evaluate (ShMemOp Load 5 (Addr 3 8w), s) in
      (r, s1.clock, s1.ffi.ffi_state, FLOOKUP s1.regs 3, LENGTH s1.stack)``;

(* (b') word_exp miss on a missing register: the same Error return. *)
val _ = observe "sh_mem_op_missing_register"
  ``let s = ^base with <| regs := FEMPTY; clock := 5 |> in
    let (r,s1) = stackSem$evaluate (ShMemOp Load 5 (Addr 3 8w), s) in
      (r, s1.clock, s1.ffi.ffi_state, FLOOKUP s1.regs 3, LENGTH s1.stack)``;

(* (c) clock = 0: word_exp succeeds but the clock guard returns TimeOut with
   empty_env s, clearing regs and the stack. *)
val _ = observe "sh_mem_op_timeout"
  ``let s = ^base with <| regs := FEMPTY |+ (3,Word 0w); clock := 0 |> in
    let (r,s1) = stackSem$evaluate (ShMemOp Load 5 (Addr 3 8w), s) in
      (r, s1.clock, s1.ffi.ffi_state, FLOOKUP s1.regs 3, LENGTH s1.stack)``;
