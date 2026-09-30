(* Direct source observations for the StackSem evaluate_def CodeBufferWrite and
   DataBufferWrite clauses.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:928-944. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

(* Code buffer: position 0 with two bytes buffered, so the next write address is
   2. Register 1 holds the address, register 2 the byte.  The CodeBufferWrite
   clause truncates the byte with w2w, so 260w becomes 4w. *)

val _ = observe "code_write_success"
  ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 2w) |+ (2,Word 260w);
      code_buffer := <| position := 0w; buffer := [1w;2w] : 8 word list; space_left := 5 |>;
      data_buffer := <| position := 0w; buffer := [] : 64 word list; space_left := 2 |>;
      use_stack := T; clock := 6 |>) in
    let (r,s1) = stackSem$evaluate (CodeBufferWrite 1 2, s) in
      (r, s1.code_buffer.position, s1.code_buffer.buffer, s1.code_buffer.space_left)``;

(* Register 1 holds a wrong address (3 instead of 2): buffer_write fails and the
   clause returns Error with the code buffer unchanged. *)
val _ = observe "code_write_mismatch"
  ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 260w);
      code_buffer := <| position := 0w; buffer := [1w;2w] : 8 word list; space_left := 5 |>;
      data_buffer := <| position := 0w; buffer := [] : 64 word list; space_left := 2 |>;
      use_stack := T; clock := 6 |>) in
    let (r,s1) = stackSem$evaluate (CodeBufferWrite 1 2, s) in
      (r, s1.code_buffer.position, s1.code_buffer.buffer, s1.code_buffer.space_left)``;

(* Data buffer: position 0 with one 64-bit word buffered, so the next write
   address is 8.  Register 1 holds the address, register 2 the word. *)
val _ = observe "data_write_success"
  ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 8w) |+ (2,Word 300w);
      code_buffer := <| position := 0w; buffer := [] : 8 word list; space_left := 5 |>;
      data_buffer := <| position := 0w; buffer := [5w] : 64 word list; space_left := 2 |>;
      use_stack := T; clock := 6 |>) in
    let (r,s1) = stackSem$evaluate (DataBufferWrite 1 2, s) in
      (r, s1.data_buffer.position, s1.data_buffer.buffer, s1.data_buffer.space_left)``;

(* Register 1 holds a wrong address (9 instead of 8): buffer_write fails and the
   clause returns Error with the data buffer unchanged. *)
val _ = observe "data_write_mismatch"
  ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 9w) |+ (2,Word 300w);
      code_buffer := <| position := 0w; buffer := [] : 8 word list; space_left := 5 |>;
      data_buffer := <| position := 0w; buffer := [5w] : 64 word list; space_left := 2 |>;
      use_stack := T; clock := 6 |>) in
    let (r,s1) = stackSem$evaluate (DataBufferWrite 1 2, s) in
      (r, s1.data_buffer.position, s1.data_buffer.buffer, s1.data_buffer.space_left)``;

(* use_stack = F rejects DataBufferWrite before reading any register. *)
val _ = observe "data_write_disabled"
  ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 8w) |+ (2,Word 300w);
      code_buffer := <| position := 0w; buffer := [] : 8 word list; space_left := 5 |>;
      data_buffer := <| position := 0w; buffer := [5w] : 64 word list; space_left := 2 |>;
      use_stack := F; clock := 6 |>) in
    let (r,s1) = stackSem$evaluate (DataBufferWrite 1 2, s) in
      (r, s1.data_buffer.position, s1.data_buffer.buffer, s1.data_buffer.space_left)``;
