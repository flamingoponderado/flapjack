(*
  Direct HOL-EVAL fixture for wordSem evaluate_def
  (cakeml/compiler/backend/semantics/wordSemScript.sml:1016-1260) ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/Evaluate.lean, at 64-bit words.
  States are record updates of a free state s; each row observes
  (result, toAList locals, clock), except the clauses that update other state
  fields (Store, CodeBufferWrite/DataBufferWrite, Install), whose rows add the
  affected memory/buffer/code fields to the projection.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory;

val _ = computeLib.add_funs [evaluate_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,num) wordSem$state``;
val ffi = ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) bytes);
               ffi_state := 0; io_events := [] |>``;
val code = ``fromAList [(5:num, (1:num, Return 0 [0] : 64 wordLang$prog));
                         (6, (2, Return 0 [2]))]``;
val st = ``^s with <|
  locals := fromAList [(2, Word 7w); (3, Loc 5 0); (8, Word 16w); (9, Word 1w)];
  clock := 3; termdep := 2; code := ^code; stack := []; handler := 0;
  store := FEMPTY; locals_size := SOME 0; stack_max := SOME 0; stack_size := LN;
  permute := (\n i. i); memory := (\a. Word 0w); mdomain := {16w}; ffi := ^ffi |>``;
val bl = ``fromAList [(2, Word 7w); (3, Loc 5 0); (8, Word 16w); (9, Word 1w)]
            : 64 word_loc sptree$num_map``;
fun evst label p sti =
  print_eval label ``(\(r:64 wordSem$result option, t:(64,'c,num) wordSem$state).
      (r, toAList t.locals, t.clock)) (evaluate (^p, ^sti))``;
fun ev label p = evst label p st;

val _ = ev "skip" ``Skip : 64 wordLang$prog``;
val _ = ev "seq_tick" ``Seq (Assign 1 (Const 5w)) Tick : 64 wordLang$prog``;
val _ = evst "tick_zero" ``Tick : 64 wordLang$prog`` ``^st with clock := 0``;
val _ = ev "if_true" ``If Equal 2 (Imm 7w) (Assign 1 (Const 1w)) (Assign 1 (Const 0w)) : 64 wordLang$prog``;
val _ = ev "if_false" ``If Less 2 (Imm 7w) (Assign 1 (Const 1w)) (Assign 1 (Const 0w)) : 64 wordLang$prog``;
val _ = ev "if_error" ``If Equal 3 (Imm 7w) Skip Skip : 64 wordLang$prog``;
val _ = ev "loop_break" ``Loop (insert 2 () LN) (Break 0) (insert 2 () LN) : 64 wordLang$prog``;
val _ = ev "loop_timeout" ``Loop LN (Continue 0) LN : 64 wordLang$prog``;
val _ = ev "loop_exit" ``Loop LN (Break 1) LN : 64 wordLang$prog``;
val _ = ev "return" ``Return 3 [2] : 64 wordLang$prog``;
val _ = ev "raise_nohandler" ``Raise 2 : 64 wordLang$prog``;
val _ = evst "raise_handler" ``Raise 2 : 64 wordLang$prog``
  ``^st with stack := [StackFrame (SOME 1) [(4, Word 1w)] [(6, Word 2w)] (SOME (0, 7, 8))]``;
val _ = evst "must_terminate_zero" ``MustTerminate Skip : 64 wordLang$prog`` ``^st with termdep := 0``;
val _ = ev "must_terminate" ``MustTerminate (Assign 1 (Const 9w)) : 64 wordLang$prog``;
val _ = ev "move" ``Move 0 [(5, 2); (6, 3)] : 64 wordLang$prog``;
val _ = ev "move_dup" ``Move 0 [(5, 2); (5, 3)] : 64 wordLang$prog``;
val _ = ev "set_get" ``Seq (Set NextFree (Const 4w)) (Get 1 NextFree) : 64 wordLang$prog``;
val _ = ev "set_handler" ``Set Handler (Const 1w) : 64 wordLang$prog``;
val _ = ev "loc_value" ``LocValue 1 5 : 64 wordLang$prog``;
val _ = ev "loc_value_missing" ``LocValue 1 4 : 64 wordLang$prog``;
val _ = ev "store_consts"
  ``StoreConsts 20 21 8 9 [(T, 5w)] : 64 wordLang$prog``;
val _ = ev "call_tail" ``Call NONE (SOME 5) [3] NONE : 64 wordLang$prog``;
val _ = evst "call_tail_timeout" ``Call NONE (SOME 5) [3] NONE : 64 wordLang$prog`` ``^st with clock := 0``;
val _ = ev "call_ret"
  ``Call (SOME ([4], (insert 2 () LN, insert 3 () LN), Skip, 10, 11)) (SOME 6) [2] NONE
      : 64 wordLang$prog``;
val _ = ev "call_ret_empty_names"
  ``Call (SOME ([4], (LN, insert 3 () LN), Skip, 10, 11)) (SOME 6) [2] NONE : 64 wordLang$prog``;
val _ = ev "call_missing" ``Call NONE (SOME 7) [3] NONE : 64 wordLang$prog``;
val _ = ev "ffi_missing_len"
  ``FFI (strlit "f") 8 21 8 21 (insert 2 () LN, LN) : 64 wordLang$prog``;
val _ = ev "ffi_ok"
  ``FFI (strlit "f") 8 9 8 9 (insert 2 () LN, LN) : 64 wordLang$prog``;

(* Alloc: a GC-free successful allocation.  The state's gc_fun is the identity
   and the store bounds the free space (TriggerGC - NextFree = 16); the local
   variable named by the Alloc argument (16) is the requested size. *)
val gcid = ``\(wl:64 word_loc list, m:64 word -> 64 word_loc, d:64 word set,
               st:store_name |-> 64 word_loc). SOME (wl, m, st)``;
val ast = ``^st with <|
  locals := insert 2 (Word (16w:word64)) (insert 4 (Loc 1 0) LN);
  stack := []; locals_size := SOME 3; stack_max := NONE;
  store := FEMPTY |+ (NextFree, Word (8w:word64)) |+ (TriggerGC, Word (24w:word64));
  gc_fun := ^gcid |>``;
val _ = evst "alloc_ok" ``Alloc 2 (insert 2 () LN, insert 4 () LN) : 64 wordLang$prog`` ast;

(* Store: a successful memory store at 16, which is the only address in the
   domain, followed by a read-back of 16 and of the untouched cell 17. *)
val _ = print_eval "store_ok"
  ``(\(r:64 wordSem$result option, t:(64,'c,num) wordSem$state).
       (r, t.memory 16w, t.memory 17w, t.clock))
     (evaluate (Store (Const 16w) 2 : 64 wordLang$prog, ^st))``;

(* OpCurrHeap: evaluates `Op Add [Var src; Lookup CurrHeap]` against a store
   entry for CurrHeap. *)
val _ = evst "op_curr_heap"
  ``OpCurrHeap Add 1 2 : 64 wordLang$prog``
  ``^st with store := FEMPTY |+ (CurrHeap, Word (5w:word64))``;

(* ShareInst: a shared-memory load from an address in sh_mdomain, with the
   oracle echoing the requested bytes; the loaded word is the round-trip of the
   address bytes under word_of_bytes/word_to_bytes. *)
val _ = evst "share_inst_load"
  ``ShareInst Load 1 (Const 16w) : 64 wordLang$prog``
  ``^st with sh_mdomain := {(16w:word64)}``;

(* CodeBufferWrite: appends one byte to a two-element code buffer whose
   position is 0 and whose next write address is 2. *)
val cbw_cb = ``<| position := (0w:word64); buffer := [1w; 2w] : word8 list; space_left := 5 |>``;
val cbw_locals = ``insert 1 (Word (2w:word64)) (insert 2 (Word (7w:word64)) ^bl)``;
val cbw_st = ``(^st with code_buffer := ^cbw_cb) with locals := ^cbw_locals``;
val _ = print_eval "code_buffer_write"
  ``(\(r:64 wordSem$result option, t:(64,'c,num) wordSem$state).
       (r, t.code_buffer.position, t.code_buffer.buffer,
        t.code_buffer.space_left, t.clock))
     (evaluate (CodeBufferWrite 1 2 : 64 wordLang$prog, ^cbw_st))``;

(* DataBufferWrite: appends one 64-bit word to a one-element data buffer whose
   position is 0 and whose next write address is 8. *)
val dbw_db = ``<| position := (0w:word64); buffer := [5w] : word64 list; space_left := 2 |>``;
val dbw_locals = ``insert 1 (Word (8w:word64)) (insert 2 (Word (7w:word64)) ^bl)``;
val dbw_st = ``(^st with data_buffer := ^dbw_db) with locals := ^dbw_locals``;
val _ = print_eval "data_buffer_write"
  ``(\(r:64 wordSem$result option, t:(64,'c,num) wordSem$state).
       (r, t.data_buffer.position, t.data_buffer.buffer,
        t.data_buffer.space_left, t.clock))
     (evaluate (DataBufferWrite 1 2 : 64 wordLang$prog, ^dbw_st))``;

(* Install: a successful code installation.  The code buffer holds two bytes
   positioned at 0 (next address 2) and the data buffer one word positioned at
   0 (next address 8); compile returns matching bytes/data and a config equal
   to the next oracle config (1), so the flushed buffers are committed, the
   installed code 42 -> (42,Skip) is unioned in, var 1 is set to Loc 42 0, and
   stack_max/stack_size are reset. *)
val cb0 = ``<| position := (0w:word64); buffer := [1w; 2w] : word8 list; space_left := 5 |>``;
val db0 = ``<| position := (0w:word64); buffer := [3w] : word64 list; space_left := 5 |>``;
val cfuns = ``\c:num (ps:(num # num # 64 wordLang$prog) list).
              SOME (([1w; 2w] : word8 list), ([3w] : word64 list), (1:num))``;
val ofuns = ``\n:num. (n, if n = 0 then [(42:num, (42:num, Skip:64 wordLang$prog))] else [])``;
val icode = ``fromAList [(5:num, (1:num, Return 0 [0] : 64 wordLang$prog));
                         (6, (2, Return 0 [2]))]``;
val ilocals = ``insert 1 (Word (0w:word64)) (insert 2 (Word (2w:word64))
                 (insert 3 (Word (0w:word64)) (insert 4 (Word (8w:word64)) LN)))``;
(* A concrete-configuration copy of the base state for the rows whose state
   constrains the compile-oracle type (Install, caught Call handler). *)
val sN = ``sN:(64,num,num) wordSem$state``;
val blN = ``fromAList [(2, Word 7w); (3, Loc 5 0); (8, Word 16w); (9, Word 1w)]
            : 64 word_loc sptree$num_map``;
val stN = ``^sN with <|
  locals := ^blN; clock := 3; termdep := 2; code := ^code; stack := []; handler := 0;
  store := FEMPTY; locals_size := SOME 0; stack_max := SOME 0; stack_size := LN;
  permute := (\n i. i); memory := (\a. Word 0w); mdomain := {16w}; ffi := ^ffi |>``;
val ist2 = ``^stN with <| locals := ^ilocals; compile := ^cfuns;
                         compile_oracle := ^ofuns; code_buffer := ^cb0;
                         data_buffer := ^db0; fp_regs := FEMPTY; code := ^icode |>``;
val _ = print_eval "install_ok"
  ``(\(r:64 wordSem$result option, t:(64,num,num) wordSem$state).
       (r, toAList t.locals, t.code_buffer.position, t.code_buffer.buffer,
        t.data_buffer.position, t.data_buffer.buffer, toAList t.code,
        t.stack_max, t.stack_size, t.clock))
     (evaluate (Install 1 2 3 4 (LN, LN) : 64 wordLang$prog, ^ist2))``;

(* Caught-handler exception: a returning Call installs handler
   SOME (3, Assign 5 (Const 99w), 7, 8); the callee at label 6 is `Raise 2` (argument key 2)
   and raises with the handler's labels (7,8), so the handler body runs and
   binds the payload to variable 3. *)
val hlocals = ``insert 2 (Word (7w:word64)) (insert 4 (Word (1w:word64)) ^bl)``;
val hcode = ``fromAList [(6:num, (2:num, Raise 2 : 64 wordLang$prog))]``;
val hst = ``^stN with <| locals := ^hlocals; code := ^hcode;
                         handler := 0; permute := (\n i. i) |>``;
val _ = print_eval "call_handler_exception"
  ``(\(r:64 wordSem$result option, t:(64,num,num) wordSem$state).
       (r, toAList t.locals, t.clock))
     (evaluate (Call (SOME ([4], (insert 2 () LN, LN), Skip, 10, 11))
                     (SOME 6) [2] (SOME (3, Assign 5 (Const 99w), 7, 8))
                     : 64 wordLang$prog, ^hst))``;
