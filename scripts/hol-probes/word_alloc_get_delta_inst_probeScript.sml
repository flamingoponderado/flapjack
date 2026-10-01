(* Direct original instruction-delta observations; CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "gdi_skip"
  ``get_delta_inst (Skip : 8 inst) = Delta [] []``;
val _ = print_eval "gdi_const"
  ``get_delta_inst (Const 1 (7w:8 word)) = Delta [1] []``;
val _ = print_eval "gdi_binop_reg"
  ``get_delta_inst (Arith (Binop Add 1 2 (Reg 3)) : 8 inst) = Delta [1] [2;3]``;
val _ = print_eval "gdi_binop_imm"
  ``get_delta_inst (Arith (Binop Add 1 2 (Imm (7w:8 word))) : 8 inst) =
    Delta [1] [2]``;
val _ = print_eval "gdi_shift_reg"
  ``get_delta_inst (Arith (Shift Lsl 1 2 (Reg 3)) : 8 inst) = Delta [1] [2;3]``;
val _ = print_eval "gdi_shift_imm"
  ``get_delta_inst (Arith (Shift Lsl 1 2 (Imm (7w:8 word))) : 8 inst) =
    Delta [1] [2]``;
val _ = print_eval "gdi_div"
  ``get_delta_inst (Arith (Div 1 2 3) : 8 inst) = Delta [1] [3;2]``;
val _ = print_eval "gdi_addcarry"
  ``get_delta_inst (Arith (AddCarry 1 2 3 4) : 8 inst) = Delta [1;4] [4;3;2]``;
val _ = print_eval "gdi_addoverflow"
  ``get_delta_inst (Arith (AddOverflow 1 2 3 4) : 8 inst) = Delta [1;4] [3;2]``;
val _ = print_eval "gdi_suboverflow"
  ``get_delta_inst (Arith (SubOverflow 1 2 3 4) : 8 inst) = Delta [1;4] [3;2]``;
val _ = print_eval "gdi_longmul"
  ``get_delta_inst (Arith (LongMul 1 2 3 4) : 8 inst) = Delta [1;2] [4;3]``;
val _ = print_eval "gdi_longdiv"
  ``get_delta_inst (Arith (LongDiv 1 2 3 4 5) : 8 inst) = Delta [1;2] [5;4;3]``;
val _ = print_eval "gdi_load"
  ``get_delta_inst (Mem Load 1 (Addr 2 (0w:8 word)) : 8 inst) = Delta [1] [2]``;
val _ = print_eval "gdi_store"
  ``get_delta_inst (Mem Store 1 (Addr 2 (0w:8 word)) : 8 inst) = Delta [] [1;2]``;
val _ = print_eval "gdi_load32"
  ``get_delta_inst (Mem Load32 1 (Addr 2 (0w:8 word)) : 8 inst) = Delta [1] [2]``;
val _ = print_eval "gdi_store32"
  ``get_delta_inst (Mem Store32 1 (Addr 2 (0w:8 word)) : 8 inst) =
    Delta [] [1;2]``;
val _ = print_eval "gdi_load8"
  ``get_delta_inst (Mem Load8 1 (Addr 2 (0w:8 word)) : 8 inst) = Delta [1] [2]``;
val _ = print_eval "gdi_store8"
  ``get_delta_inst (Mem Store8 1 (Addr 2 (0w:8 word)) : 8 inst) = Delta [] [1;2]``;
val _ = print_eval "gdi_fpless"
  ``get_delta_inst (FP (FPLess 1 2 3) : 8 inst) = Delta [1] []``;
val _ = print_eval "gdi_fpmovtoreg64"
  ``get_delta_inst (FP (FPMovToReg 1 2 3) : 64 inst) = Delta [1] []``;
val _ = print_eval "gdi_fpmovtoreg32"
  ``get_delta_inst (FP (FPMovToReg 1 2 3) : 32 inst) = Delta [1;2] []``;
val _ = print_eval "gdi_fpmovfromreg64"
  ``get_delta_inst (FP (FPMovFromReg 3 1 2) : 64 inst) = Delta [] [1]``;
val _ = print_eval "gdi_fpmovfromreg32"
  ``get_delta_inst (FP (FPMovFromReg 3 1 2) : 32 inst) = Delta [] [1;2]``;
val _ = print_eval "gdi_fpneg_catchall"
  ``get_delta_inst (FP (FPNeg 1 2) : 8 inst) = Delta [] []``;
