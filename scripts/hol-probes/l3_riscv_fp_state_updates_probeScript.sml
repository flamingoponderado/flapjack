val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/common") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/lib") :: !loadPath;
load "riscv_stepTheory"; load "binary_ieeeLib"; load "wordsLib"; load "bitstringLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.max_print_depth := 1000;
val _ = Parse.temp_remove_user_printer ("num.numeral_computations", mk_var("n", numSyntax.num));
val () = computeLib.add_funs (map snd (DB.definitions "riscv"));
val () = computeLib.add_funs (map snd (DB.definitions "riscv_step"));
val () = computeLib.add_funs [machine_ieeeTheory.fp32_compare_def,
 machine_ieeeTheory.fp64_compare_def, machine_ieeeTheory.fp32_to_float_def,
 machine_ieeeTheory.fp64_to_float_def, machine_ieeeTheory.float_to_fp32_def,
 machine_ieeeTheory.float_to_fp64_def, machine_ieeeTheory.fp32_posInf_def,
 machine_ieeeTheory.fp64_posInf_def];
val conv = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL;
fun observe label tm = (print(label ^ "="); print_term(rhs(concl(conv tm))); print "\n");
val s = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "write_fprs" ``let r = writeFPRS (3w,0x3f800000w) ^s in (FPRD 3w r, GPR 3w r, r.c_gpr 7w 0w, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD, (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w)``;
val _ = observe "write_fprd" ``let r = writeFPRD (3w,0x3ff0000000000000w) ^s in (FPRD 3w r, GPR 3w r, r.c_gpr 7w 0w, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD, (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w)``;
val _ = observe "set_invalid" ``let r = setFP_Invalid () ^s in (FPRD 3w r, GPR 3w r, r.c_gpr 7w 0w, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD, (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w)``;
val _ = observe "write_gpr_zero" ``let r = write'GPR (77w,0w) ^s in (FPRD 3w r, GPR 3w r, r.c_gpr 7w 0w, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD, (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w)``;
val _ = observe "write_gpr_three" ``let r = write'GPR (77w,3w) ^s in (FPRD 3w r, GPR 3w r, r.c_gpr 7w 0w, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD, (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w)``;
