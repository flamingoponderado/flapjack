load "preamble"; load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib preamble data_to_wordTheory;
val _ = Globals.linewidth := 1000000;
val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
  has_div := F; has_longdiv := F; has_fp_ops := T; has_fp_tern := T;
  be := F; call_empty_ffi := F; gc_kind := Simple |>``;
val _ = (print "entry="; print_term (rconc (EVAL ``[
  (0n, 0n, comp ^conf 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_cmp FP_Less)) [1;2] NONE));
  (1n, 0n, comp ^conf 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_cmp FP_GreaterEqual)) [1;2] NONE));
  (2n, 0n, comp ^conf 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_bop FP_Sub)) [1;2] NONE));
  (3n, 0n, comp ^conf 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_uop FP_Sqrt)) [1] NONE));
  (4n, 0n, comp ^conf 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_top FP_Fma)) [1;2;3] NONE));
  (5n, 0n, comp (^conf with has_fp_ops := F) 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_cmp FP_Equal)) [1;2] NONE));
  (6n, 0n, comp (^conf with len_size := 0) 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_bop FP_Add)) [1;2] NONE));
  (7n, 0n, comp (^conf with has_fp_tern := F) 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_top FP_Fma)) [1;2;3] NONE));
  (8n, 0n, comp ^conf 4 7 (dataLang$Assign 3 (closLang$WordOp (FP_uop FP_Neg)) [1;2] NONE))
 ] : (num # num # (32 wordLang$prog # num)) list``)); print "\n");
