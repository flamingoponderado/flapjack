(* Original-HOL oracle for the asmSem memory-word accessors and the asmProps
   memory-word invariants.
   References: asmSemScript.sml:178-189 (addr_def, read_mem_word_def,
   write_mem_word_def) and asmPropsScript.sml:339-357/424-... (the
   memory-word invariant statements). *)
load "bossLib";
load "preamble";
load "asmSemTheory";
load "asmPropsTheory";
open bossLib; open HolKernel Parse; open preamble;
open asmSemTheory asmPropsTheory;

val a = ``(0w:8 word)``;
val st = ``(<| regs := (\r. (0w:8 word));
             fp_regs := (\r. (0w:64 word));
             mem := (\x. (0w:8 word));
             mem_domain := {(0w:8 word); (1w:8 word); (2w:8 word); (3w:8 word)};
             pc := (0w:8 word); lr := 0; align := 0; be := F; failed := F |>): 8 asm_state``;
val stm = ``(<| regs := (\r. (0w:8 word));
             fp_regs := (\r. (0w:64 word));
             mem := (\x. if x = (0w:8 word) then (0x11w:8 word) else if x = (1w:8 word) then (0x22w:8 word) else (0x33w:8 word));
             mem_domain := UNIV;
             pc := (0w:8 word); lr := 0; align := 0; be := F; failed := F |>): 8 asm_state``;

fun observe label tm =
  (print (label ^ "="); print_term (rconc (EVAL tm)); print "\n");

val _ = observe "addr"        ``addr (Addr 4 (2w:8 word)) ^st = (2w:8 word)``;
val _ = observe "rw_zero"     ``read_mem_word ^a 0 ^st = ((0w:8 word), ^st)``;
val _ = observe "rw_le_ok"    ``~(SND (read_mem_word ^a 4 ^st)).failed``;
val _ = observe "rw_be_fail"  ``(SND (read_mem_word ^a 4 (^st with be := T))).failed``;
val _ = observe "rw_fail_dom" ``(SND (read_mem_word (9w:8 word) 1 ^st)).failed``;
val _ = observe "ww_zero"     ``write_mem_word ^a 0 (171w:8 word) ^st = ^st``;
val _ = observe "ww_le"       ``(write_mem_word ^a 1 (171w:8 word) ^st).mem (0w:8 word) = (171w:8 word)``;
val _ = observe "ww_le_ok"    ``~(write_mem_word ^a 1 (171w:8 word) ^st).failed``;
val _ = observe "ww_be_fail"  ``(write_mem_word ^a 2 (171w:8 word) (^st with be := T)).failed``;
val _ = observe "rw_le2"      ``FST (read_mem_word (0w:8 word) 2 ^stm) = (0x2211w:8 word)``;
val _ = observe "rw_be2"      ``FST (read_mem_word (1w:8 word) 2 (^stm with be := T)) = (0x1122w:8 word)``;
val _ = observe "rw_wrap_ok"  ``~(SND (read_mem_word (255w:8 word) 4 (^stm with mem_domain := {(255w:8 word);(0w:8 word);(1w:8 word);(2w:8 word)}))).failed``;
val _ = observe "rw_wrap_oob" ``(SND (read_mem_word (255w:8 word) 4 ^st)).failed``;
