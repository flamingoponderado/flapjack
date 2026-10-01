load "preamble";
load "targetSemTheory";
load "miscTheory";
load "asmTheory";
open bossLib HolKernel Parse preamble targetSemTheory miscTheory asmTheory;
fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");
val oracle = ``(\(n:num) (x:num). n + x)``;
val c = ``(<| ISA := RISC_V
              ; encode := (\i. [10w;20w;30w;40w])
              ; big_endian := F
              ; code_alignment := 1
              ; link_reg := NONE
              ; avoid_regs := []
              ; reg_count := 8
              ; fp_reg_count := 8
              ; two_reg_arith := T
              ; valid_imm := (K (K T))
              ; addr_offset := (0w,0w)
              ; hw_offset := (0w,0w)
              ; byte_offset := (0w,0w)
              ; jump_offset := (0w,0w)
              ; cjump_offset := (0w,0w)
              ; loc_offset := (0w,0w) |>) : 8 asm_config``;
val m = ``(\ (a:8 word). if a = 0w then (30w:8 word) else if a = 1w then (40w:8 word) else (0w:8 word))``;
val mw = ``(\ (a:1 word). if a = 255w then (1w:8 word) else if a = 0w then (2w:8 word) else (0w:8 word))``;
val _ = print_eval "oracle_first" ``FST (apply_oracle ^oracle (5:num))``;
val _ = print_eval "oracle_shift" ``SND (apply_oracle ^oracle (5:num)) 0 7``;
val _ = print_eval "bytes_empty" ``bytes_in_memory (0w:8 word) [] ^m UNIV``;
val _ = print_eval "bytes_nonempty" ``bytes_in_memory (0w:8 word) [30w;40w] ^m UNIV``;
val _ = print_eval "bytes_domain_fail" ``bytes_in_memory (0w:8 word) [30w] ^m (\ (a:8 word). a <> 0w)``;
val _ = print_eval "bytes_wrap" ``bytes_in_memory (255w:1 word) [1w;2w] ^mw UNIV``;
val _ = print_eval "encoded_drop" ``DROP (1 * 2 ** ^c.code_alignment) (^c.encode ARB)``;
val _ = print_eval "encoded_guard_true" ``1 * 2 ** ^c.code_alignment < LENGTH (^c.encode ARB)``;
val _ = print_eval "encoded_guard_strict" ``2 * 2 ** ^c.code_alignment < LENGTH (^c.encode ARB)``;
val _ = print_eval "encoded_bytes_match" ``bytes_in_memory (0w:8 word)
    (DROP (1 * 2 ** ^c.code_alignment) (^c.encode ARB)) ^m UNIV``;
