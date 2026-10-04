(* Direct HOL-EVAL fixture for word_simp$const_fp_inst_cs_def
   (cakeml/compiler/backend/word_simpScript.sml:226-246) through const_fp:
   only Load/Load32/Load8 forget their destination; stores and the 16-bit
   operations keep the constant knowledge. *)
load "bossLib"; load "preamble"; load "word_simpTheory";
open HolKernel Parse bossLib preamble word_simpTheory;
val _ = Globals.linewidth := 1000;
fun out label op' =
  let
    val p = ``(Seq (Assign 2 (Const 7w))
                 (Seq (Inst (Mem ^op' 2 (Addr 3 0w)))
                      (Assign 4 (Op Add [Var 2; Const 3w]))) : 64 wordLang$prog)``
  in
    print (label ^ "=");
    print_term (rhs (concl (EVAL ``const_fp ^p``)));
    print "\n"
  end;
val _ = out "mem_store" ``asm$Store``;
val _ = out "mem_store8" ``asm$Store8``;
val _ = out "mem_store16" ``asm$Store16``;
val _ = out "mem_store32" ``asm$Store32``;
val _ = out "mem_load" ``asm$Load``;
val _ = out "mem_load8" ``asm$Load8``;
val _ = out "mem_load16" ``asm$Load16``;
val _ = out "mem_load32" ``asm$Load32``;
