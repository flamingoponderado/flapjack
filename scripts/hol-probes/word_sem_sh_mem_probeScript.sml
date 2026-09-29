(*
  Direct HOL-EVAL fixture for the wordSem shared-memory helpers ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/ShMem.lean
  (cakeml/compiler/backend/semantics/wordSemScript.sml:374-470) at 64-bit
  words.  The FFI oracle increments every byte and counts calls in a num
  state, so the rows observe the exact configuration and payload bytes via
  the recorded io_events; a second oracle diverges.  States are record
  updates of a free state `s`.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,num) wordSem$state``;
val inc = ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) (MAP (\b. b + 1w) bytes));
               ffi_state := 0; io_events := [] |>``;
val divffi = ``<| oracle := (\n (st:num) conf bytes. Oracle_final FFI_diverged);
               ffi_state := 0; io_events := [] |>``;
val st = ``^s with <| sh_mdomain := {8w}; ffi := ^inc;
                      locals := insert 3 (Word 0x1122w) (insert 4 (Loc 1 0) LN);
                      stack := [StackFrame NONE [] [] NONE]; locals_size := SOME 9 |>``;
val proj = ``\(r:64 wordSem$result option, t:(64,'c,num) wordSem$state).
                (r, t.ffi.ffi_state, t.ffi.io_events, toAList t.locals, LENGTH t.stack)``;

val _ = print_eval "store" ``^proj (share_inst Store 3 8w ^st)``;
val _ = print_eval "store_outside" ``^proj (share_inst Store 3 16w ^st)``;
val _ = print_eval "store_loc" ``^proj (share_inst Store 4 8w ^st)``;
val _ = print_eval "store_missing" ``^proj (share_inst Store 7 8w ^st)``;
val _ = print_eval "store_final" ``^proj (share_inst Store 3 8w (^st with ffi := ^divffi))``;
val _ = print_eval "store8" ``^proj (share_inst Store8 3 9w ^st)``;
val _ = print_eval "store8_outside" ``^proj (share_inst Store8 3 17w ^st)``;
val _ = print_eval "store16" ``^proj (share_inst Store16 3 10w ^st)``;
val _ = print_eval "store32" ``^proj (share_inst Store32 3 12w ^st)``;
val _ = print_eval "store_unaligned" ``^proj (share_inst Store 3 9w ^st)``;
val _ = print_eval "load" ``^proj (share_inst Load 5 8w ^st)``;
val _ = print_eval "load_outside" ``^proj (share_inst Load 5 9w ^st)``;
val _ = print_eval "load8" ``^proj (share_inst Load8 5 9w ^st)``;
val _ = print_eval "load16" ``^proj (share_inst Load16 5 10w ^st)``;
val _ = print_eval "load32" ``^proj (share_inst Load32 5 12w ^st)``;
val _ = print_eval "load_final" ``^proj (share_inst Load 5 8w (^st with ffi := ^divffi))``;
val _ = print_eval "sh_mem_set_var_none" ``^proj (sh_mem_set_var NONE 5 ^st)``;
