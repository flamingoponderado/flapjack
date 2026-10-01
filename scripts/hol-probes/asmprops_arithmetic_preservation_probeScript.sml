load "bossLib";
load "preamble";
load "asmPropsTheory";
open bossLib HolKernel Parse preamble asmPropsTheory asmSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "ap_upd_pc_simps" (DB.fetch "asmProps" "upd_pc_simps");
val _ = captureTypes "ap_upd_pc_simps_types" (DB.fetch "asmProps" "upd_pc_simps");
val _ = capture "ap_binop_upd_consts" (DB.fetch "asmProps" "binop_upd_consts");
val _ = captureTypes "ap_binop_upd_consts_types" (DB.fetch "asmProps" "binop_upd_consts");
val _ = capture "ap_arith_upd_consts" (DB.fetch "asmProps" "arith_upd_consts");
val _ = captureTypes "ap_arith_upd_consts_types" (DB.fetch "asmProps" "arith_upd_consts");
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "ap_add" ``let t = arith_upd (Binop Add 0 2 (Imm 1w)) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_shift_fail" ``let t = arith_upd (Shift Lsl 0 2 (Reg 2)) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_div_zero" ``let t = arith_upd (Div 0 2 3) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_longmul" ``let t = arith_upd (LongMul 0 1 2 2) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_longdiv_zero" ``let t = arith_upd (LongDiv 0 1 2 2 3) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_carry" ``let t = arith_upd (AddCarry 0 2 2 4) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_addoverflow" ``let t = arith_upd (AddOverflow 0 2 2 4) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_suboverflow" ``let t = arith_upd (SubOverflow 0 2 2 4) ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be)``;
val _ = observe "ap_pc" ``let t = upd_pc 77w ((ARB:8 asm_state) with <|regs := (\r. if r = 3 then 0w else 99w); mem := (\a. 9w); mem_domain := {0w}; align := 3;lr := 5;be := T;failed := F|>) in (t.failed,0w IN t.mem_domain,t.align,w2n(t.mem 0w),t.lr,t.be,w2n t.pc)``;
