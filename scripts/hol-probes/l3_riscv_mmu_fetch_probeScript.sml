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
val s = ``(ARB:riscv_state) with <|
 procID := 0w; exception := NoException;
 MEM8 := (\a. n2w (w2n a));
 c_PC := (\_. 0w); c_Skip := (\_. 0w);
 c_gpr := (\_ r. if r = 2w then 8w else 0w);
 c_MCSR := (\_. (ARB:MachineCSR) with <|
   mstatus := (ARB:mstatus) with <| VM := 0w; MMPRV := F; MPRV := 3w |>;
   mcpuid := (ARB:mcpuid) with ArchBase := 2w |>) |>``;
val _ = observe "read_aligned" ``rawReadData 0w ^s``;
val _ = observe "read_unaligned" ``rawReadData 3w ^s``;
val _ = observe "read_cross_word" ``rawReadData 7w ^s``;
val _ = observe "translate_bare" ``FST (translateAddr (0x12345w,Data,Read) ^s)``;
val _ = observe "walk_invalid_level0" ``FST (walk64 (0w,Data,Read,Machine,0w,0) ^s)``;
val _ = observe "walk_invalid_level2" ``FST (walk64 (0w,Data,Read,Machine,0w,2) ^s)``;
val _ = observe "fetch_half" ``FST (riscv_step$Fetch ^s)``;
val _ = observe "fetch_half_skip" ``Skip (SND (riscv_step$Fetch ^s))``;
val sw = ``^s with MEM8 := (\a. if a = 0w then 3w else n2w (w2n a))``;
val _ = observe "fetch_word" ``FST (riscv_step$Fetch ^sw)``;
val _ = observe "fetch_word_skip" ``Skip (SND (riscv_step$Fetch ^sw))``;
val _ = observe "load_double" ``GPR 1w (dfn'LD (1w,2w,0w) ^s)``;
val _ = observe "store_cross_word" ``rawReadData 7w (rawWriteData (7w,0xABCDw,2) ^s)``;
val _ = OS.Process.exit OS.Process.success;
