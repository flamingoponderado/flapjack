val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/common") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/lib") :: !loadPath;
load "riscv_stepTheory"; load "wordsLib"; load "bitstringLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.max_print_depth := 1000;
val _ = Parse.temp_remove_user_printer ("num.numeral_computations", mk_var("n", numSyntax.num));
val () = computeLib.add_funs (map snd (DB.definitions "riscv"));
val () = computeLib.add_funs (map snd (DB.definitions "riscv_step"));
val conv = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL;
fun observe label tm = (print(label ^ "="); print_term(rhs(concl(conv tm))); print "\n");
val _ = observe "l3_round_modes" ``MAP l3round [RNE;RTZ;RDN;RUP;RMM;RDYN]``;
val s = ``(ARB:riscv_state) with <| procID := 0w;
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with FRM := 0w) |>``;
val _ = observe "round_static_modes" ``MAP (\n. riscv$round (n2w n) ^s) [0;1;2;3;4;5;6;7]``;
val _ = observe "round_dynamic_modes" ``MAP (\n. riscv$round 7w (^s with
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with FRM := n2w n))) [0;1;2;3;4;5;6;7]``;
val _ = OS.Process.exit OS.Process.success;
