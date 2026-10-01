(* Direct original loopSem evaluate_def Store32/StoreByte clauses325-337.
   Uses original wordSem operations; no hand-written store implementation. *)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib HolKernel Parse preamble loopSemTheory;
val s = ``(s:(64,'ffi) loopSem$state)``;
(* Recursive evaluate_def is not in the default compset. Register the original
   theorem, as in loop_sem_evaluate_control_probe; no surrogate evaluator. *)
val _ = computeLib.add_funs [evaluate_def];
fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val _ = print_eval "store32_narrow"
  ``case evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Word (0x111223344w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>)) of (NONE,t) => SOME (t.memory (0w:64 word)) | _ => NONE``;

val _ = print_eval "store32_big"
  ``case evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Word (0x11223344w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := T; clock := 7 |>)) of (NONE,t) => SOME (t.memory (0w:64 word)) | _ => NONE``;

val _ = print_eval "store32_upper"
  ``case evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (4w:64 word)); (1,Word (0x11223344w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>)) of (NONE,t) => SOME (t.memory (0w:64 word)) | _ => NONE``;

val _ = print_eval "store32_unaligned"
  ``FST (evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (2w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "store32_domain"
  ``FST (evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (8w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "store32_memory_loc"
  ``FST (evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Loc 0 0); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "store32_address_loc"
  ``FST (evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Loc 0 0); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "store32_value_loc"
  ``FST (evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Loc 0 0)]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "store32_other"
  ``case evaluate (Store32 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>)) of (NONE,t) => SOME (t.memory (8w:64 word)) | _ => NONE``;

val _ = print_eval "storeByte_narrow"
  ``case evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Word (1w:64 word)); (1,Word (0x1eew:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>)) of (NONE,t) => SOME (t.memory (0w:64 word)) | _ => NONE``;

val _ = print_eval "storeByte_big"
  ``case evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Word (1w:64 word)); (1,Word (0xeew:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := T; clock := 7 |>)) of (NONE,t) => SOME (t.memory (0w:64 word)) | _ => NONE``;

val _ = print_eval "storeByte_domain"
  ``FST (evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Word (8w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "storeByte_memory_loc"
  ``FST (evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Loc 0 0); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "storeByte_address_loc"
  ``FST (evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Loc 0 0); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "storeByte_value_loc"
  ``FST (evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Loc 0 0)]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>))) = SOME Error``;

val _ = print_eval "storeByte_clock"
  ``case evaluate (StoreByte 0 1,(^s with <| locals := fromAList [(0,Word (0w:64 word)); (1,Word (1w:64 word))]; memory := (λw:64 word. Word (0w:64 word)); mdomain := {0w:64 word}; be := F; clock := 7 |>)) of (NONE,t) => SOME t.clock | _ => NONE``;
