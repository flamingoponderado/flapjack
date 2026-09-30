(*
  Direct HOL-EVAL fixture for the stackSem shared-memory helpers ported in
  Flapjack/Compiler/Backend/Semantics/StackSem/ShMem.lean
  (cakeml/compiler/backend/semantics/stackSemScript.sml:194-308) at 64-bit
  words.  The FFI oracle increments every byte and counts calls in a num
  state, so the rows observe the exact configuration and payload bytes via the
  recorded io_events; a second oracle diverges.  States are record updates of
  a free state `s`.  The plain word forms guard on `a IN sh_mdomain`, the
  sized forms on `byte_align a IN sh_mdomain`.
*)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,num) stackSem$state``;
val inc = ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) (MAP (\b. b + 1w) bytes));
               ffi_state := 0; io_events := [] |>``;
val divffi = ``<| oracle := (\n (st:num) conf bytes. Oracle_final FFI_diverged);
               ffi_state := 0; io_events := [] |>``;
val st = ``^s with <| sh_mdomain := {8w}; ffi := ^inc;
                      regs := (FEMPTY |+ (3, Word 0x1122w) |+ (4, Loc 1 0));
                      stack := []; clock := 0 |>``;
val proj = ``\(r:(64) stackSem$result option, t:(64,'c,num) stackSem$state).
                (r, t.ffi.ffi_state, t.ffi.io_events,
                 FLOOKUP t.regs 3, FLOOKUP t.regs 4, FLOOKUP t.regs 5, LENGTH t.stack)``;

val _ = print_eval "store" ``^proj (stackSem$sh_mem_op Store 3 8w ^st)``;
val _ = print_eval "load" ``^proj (stackSem$sh_mem_op Load 5 8w ^st)``;
val _ = print_eval "store8" ``^proj (stackSem$sh_mem_op Store8 3 9w ^st)``;
val _ = print_eval "load8" ``^proj (stackSem$sh_mem_op Load8 5 9w ^st)``;
val _ = print_eval "store16" ``^proj (stackSem$sh_mem_op Store16 3 10w ^st)``;
val _ = print_eval "load16" ``^proj (stackSem$sh_mem_op Load16 5 10w ^st)``;
val _ = print_eval "store32" ``^proj (stackSem$sh_mem_op Store32 3 12w ^st)``;
val _ = print_eval "load32" ``^proj (stackSem$sh_mem_op Load32 5 12w ^st)``;
val _ = print_eval "load_outside" ``^proj (stackSem$sh_mem_op Load 5 16w ^st)``;
val _ = print_eval "store8_outside" ``^proj (stackSem$sh_mem_op Store8 3 17w ^st)``;
val _ = print_eval "load_word_unaligned" ``^proj (stackSem$sh_mem_op Load 5 9w ^st)``;
val _ = print_eval "store_word_unaligned" ``^proj (stackSem$sh_mem_op Store 3 9w ^st)``;
val _ = print_eval "load_final" ``^proj (stackSem$sh_mem_op Load 5 8w (^st with ffi := ^divffi))``;
val _ = print_eval "store_final" ``^proj (stackSem$sh_mem_op Store 3 8w (^st with ffi := ^divffi))``;
val _ = print_eval "store_loc" ``^proj (stackSem$sh_mem_op Store 4 8w ^st)``;
