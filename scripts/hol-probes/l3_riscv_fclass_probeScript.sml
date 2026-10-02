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
val () = computeLib.add_funs [machine_ieeeTheory.fp32_isNormal_def,
 machine_ieeeTheory.fp64_isNormal_def, machine_ieeeTheory.fp32_isSubnormal_def,
 machine_ieeeTheory.fp64_isSubnormal_def, machine_ieeeTheory.fp32_posZero_def,
 machine_ieeeTheory.fp64_posZero_def, machine_ieeeTheory.fp32_negZero_def,
 machine_ieeeTheory.fp64_negZero_def];
val conv = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL;
fun observe label tm = (print(label ^ "="); print_term(rhs(concl(conv tm))); print "\n");
val s = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val s_fclass_s_neg_inf = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xff800000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_neg_inf" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_neg_inf in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_neg_normal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xbf800000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_neg_normal" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_neg_normal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_neg_subnormal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x80000001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_neg_subnormal" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_neg_subnormal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_neg_zero = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x80000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_neg_zero" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_neg_zero in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_pos_zero = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x0w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_pos_zero" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_pos_zero in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_pos_subnormal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x1w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_pos_subnormal" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_pos_subnormal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_pos_normal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x3f800000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_pos_normal" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_pos_normal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_pos_inf = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7f800000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_pos_inf" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_pos_inf in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_snan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7f800001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_snan" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_snan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_canonical_nan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7fc00000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_canonical_nan" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_canonical_nan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_payload_qnan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7fc00001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_payload_qnan" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_payload_qnan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_neg_qnan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xffc00000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_neg_qnan" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_neg_qnan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_neg_snan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xff800001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_neg_snan" ``let r = dfn'FCLASS_S (3w,1w) ^s_fclass_s_neg_snan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_s_dest_zero = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x3f800000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_s_dest_zero" ``let r = dfn'FCLASS_S (0w,1w) ^s_fclass_s_dest_zero in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_neg_inf = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xfff0000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_neg_inf" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_neg_inf in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_neg_normal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xbff0000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_neg_normal" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_neg_normal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_neg_subnormal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x8000000000000001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_neg_subnormal" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_neg_subnormal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_neg_zero = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x8000000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_neg_zero" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_neg_zero in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_pos_zero = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x0w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_pos_zero" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_pos_zero in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_pos_subnormal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x1w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_pos_subnormal" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_pos_subnormal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_pos_normal = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x3ff0000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_pos_normal" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_pos_normal in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_pos_inf = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7ff0000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_pos_inf" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_pos_inf in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_snan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7ff0000000000001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_snan" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_snan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_canonical_nan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7ff8000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_canonical_nan" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_canonical_nan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_payload_qnan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x7ff8000000000001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_payload_qnan" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_payload_qnan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_neg_qnan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xfff8000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_neg_qnan" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_neg_qnan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_neg_snan = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0xfff0000000000001w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_neg_snan" ``let r = dfn'FCLASS_D (3w,1w) ^s_fclass_d_neg_snan in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
val s_fclass_d_dest_zero = ``^s with c_fpr := (\c r. if c = 7w /\ r = 1w then 0x3ff0000000000000w else if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w)``;
val _ = observe "fclass_d_dest_zero" ``let r = dfn'FCLASS_D (0w,1w) ^s_fclass_d_dest_zero in (GPR 3w r, r.c_gpr 7w 0w, FPRD 1w r, (fcsr r).NV, (fcsr r).NX, (MCSR r).mstatus.MFS, (Delta r).data1, r.c_gpr 8w 3w)``;
