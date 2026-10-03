load "preamble"; load "word_simpTheory";
open HolKernel Parse bossLib preamble wordLangTheory word_simpTheory;
val _ = Globals.linewidth := 1000000;
fun evald name tm = let
  val th = EVAL tm
  val _ = if null (hyp th) then () else raise Fail ("hyp " ^ name)
in rhs (concl th) end;
val _ = (print "fold_chain="; print_term (evald "fold_chain" ``word_simp$compile_exp
  (Seq (Assign 1 (Const 5w)) (Seq (Assign 2 (Op Add [Var 1; Const 4w])) (Assign 3 (Var 2))) : 64 wordLang$prog)``); print "\n");
val _ = (print "call_drop_consts="; print_term (evald "call_drop_consts" ``word_simp$compile_exp
  (Seq (Assign 2 (Const 7w)) (Seq (Assign 6 (Const 5w)) (Call NONE (SOME 10) [2;6] NONE)) : 64 wordLang$prog)``); print "\n");
val _ = (print "static_if="; print_term (evald "static_if" ``word_simp$compile_exp
  (Seq (Assign 1 (Const 0w)) (If Equal 1 (Imm 0w) (Assign 2 (Const 3w)) (Assign 2 (Const 4w))) : 64 wordLang$prog)``); print "\n");
val _ = (print "push_out_if="; print_term (evald "push_out_if" ``word_simp$compile_exp
  (If Equal 1 (Imm 0w) (Return 0 [1]) (Assign 2 (Const 3w)) : 64 wordLang$prog)``); print "\n");
val _ = (print "hoist_if="; print_term (evald "hoist_if" ``word_simp$compile_exp
  (Seq (If Lower 1 (Reg 2) (Assign 5 (Const 1w)) (Assign 5 (Const 2w)))
       (Seq (Assign 7 (Var 3)) (If Equal 5 (Imm 1w) (Assign 8 (Const 9w)) (Assign 8 (Const 10w)))) : 64 wordLang$prog)``); print "\n");
val _ = (print "shift_move_loop="; print_term (evald "shift_move_loop" ``word_simp$compile_exp
  (Seq (Assign 1 (Shift Lsl (Const 1w) (Const 3w)))
   (Seq (Move 0 [(4,1);(5,9)])
   (Seq (Loop (insert 4 () LN) (Assign 6 (Var 4)) LN)
        (Assign 7 (Op Sub [Var 4; Var 1])))) : 64 wordLang$prog)``); print "\n");
val _ = (print "ffi_install_share="; print_term (evald "ffi_install_share" ``word_simp$compile_exp
  (Seq (Assign 2 (Const 8w))
   (Seq (FFI «f» 2 3 4 5 (insert 2 () LN, LN))
   (Seq (ShareInst Load 3 (Op Add [Var 2; Const 1w]))
        (Install 2 3 4 5 (insert 2 () LN, LN)))) : 64 wordLang$prog)``); print "\n");
val _ = (print "inst_alloc_ret_call="; print_term (evald "inst_alloc_ret_call" ``word_simp$compile_exp
  (Seq (Assign 2 (Const 6w))
   (Seq (Inst (Const 3 4w))
   (Seq (Alloc 2 (insert 2 () LN, LN))
        (Call (SOME ([1], (insert 3 () LN, LN), Assign 9 (Var 3), 5, 6)) (SOME 11) [3] NONE))) : 64 wordLang$prog)``); print "\n");
