load "preamble"; load "word_instTheory";
open HolKernel Parse bossLib preamble wordLangTheory word_instTheory asmTheory;
val _ = Globals.linewidth := 1000000;
(* Only valid_imm, addr_offset, hw_offset and byte_offset are read by
   inst_select; the remaining asm_config fields are left unspecified. *)
val cfg = ``(ARB : 64 asm_config) with <|
   valid_imm := (\b i. -2048w <= i /\ i <= 2047w);
   addr_offset := (-2048w, 2047w); hw_offset := (-2048w, 2047w);
   byte_offset := (-2048w, 2047w) |>``;
fun evald name tm = let
  val th = EVAL tm
  val _ = if null (hyp th) then () else raise Fail ("hyp " ^ name)
in rhs (concl th) end;
fun sel p = ``inst_select ^cfg 100 ^p``;
val _ = (print "add3="; print_term (evald "add3" (sel ``(Assign 5 (Op Add [Var 1; Const 3w; Var 2]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "sub_const="; print_term (evald "sub_const" (sel ``(Assign 5 (Op Sub [Var 1; Const 3w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "big_imm="; print_term (evald "big_imm" (sel ``(Assign 5 (Op Add [Var 1; Const 5000w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "store_off="; print_term (evald "store_off" (sel ``(Store (Op Add [Var 1; Const 8w]) 4 : 64 wordLang$prog)``)); print "\n");
val _ = (print "load_off="; print_term (evald "load_off" (sel ``(Assign 5 (Load (Op Add [Var 1; Const 16w])) : 64 wordLang$prog)``)); print "\n");
val _ = (print "shifts="; print_term (evald "shifts" (sel ``(Seq (Assign 5 (Shift Lsl (Var 1) (Const 3w))) (Seq (Assign 6 (Shift Lsr (Var 1) (Const 0w))) (Assign 7 (Shift Asr (Var 1) (Const 64w)))) : 64 wordLang$prog)``)); print "\n");
val _ = (print "curr_heap="; print_term (evald "curr_heap" (sel ``(Assign 5 (Op Add [Var 1; Lookup CurrHeap]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "share_load8="; print_term (evald "share_load8" (sel ``(ShareInst Load8 3 (Op Add [Var 1; Const 4w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "set_and="; print_term (evald "set_and" (sel ``(Set Globals (Op And [Var 1; Op And [Var 2; Const 255w]]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "const_fold="; print_term (evald "const_fold" (sel ``(Assign 5 (Op Xor [Const 3w; Const 5w; Op Sub [Const 9w; Const 4w]]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "two_reg="; print_term (evald "two_reg" ``three_to_two_reg_prog T (Seq (Inst (Arith (Binop Add 5 1 (Imm 3w)))) (Seq (OpCurrHeap Sub 6 2) (If Equal 1 (Imm 0w) (Inst (Arith (Shift Lsl 7 8 (Imm 2w)))) Skip)) : 64 wordLang$prog)``); print "\n");
