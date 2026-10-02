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
val () = computeLib.add_funs [machine_ieeeTheory.int_to_fp32_def,
 machine_ieeeTheory.int_to_fp64_def, machine_ieeeTheory.real_to_fp32_def,
 machine_ieeeTheory.real_to_fp64_def, machine_ieeeTheory.float_to_fp32_def,
 machine_ieeeTheory.float_to_fp64_def];
val probe_dir = case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
 SOME p => p | NONE => raise Fail "FLAPJACK_HOL_PROBE_DIR is required";
val _ = QUse.use (OS.Path.concat(probe_dir,"binary_ieee_directed_certificates.sml"));
fun checked_float_round tm = let
 val (mode,_,_,_,_) = binary_ieeeSyntax.dest_float_round tm
 in if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm orelse
       mode ~~ binary_ieeeSyntax.roundTowardNegative_tm
 then FlapjackDirected.certified_directed_float_round_CONV tm
 else binary_ieeeLib.float_round_CONV tm end
 handle HOL_ERR err => raise Fail (Feedback.exn_to_string (HOL_ERR err));
val () = computeLib.upd_compset (computeLib.add_conv
  (binary_ieeeSyntax.float_round_tm, 3, checked_float_round));
val conv = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL;
fun observe label tm = let val th = conv tm in
 if null (hyp th) then (print(label ^ "="); print_term(rhs(concl th)); print "\n")
 else raise Fail (label ^ " has undischarged assumptions") end;
val s_zero = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 0w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_zero" ``let r = dfn'FCVT_S_W (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_zero" ``let r = dfn'FCVT_S_WU (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_zero" ``let r = dfn'FCVT_S_L (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_zero" ``let r = dfn'FCVT_S_LU (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_zero" ``let r = dfn'FCVT_D_W (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_zero" ``let r = dfn'FCVT_D_WU (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_zero" ``let r = dfn'FCVT_D_L (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_zero" ``let r = dfn'FCVT_D_LU (3w,1w,0w) ^s_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_one = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 1w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_one" ``let r = dfn'FCVT_S_W (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_one" ``let r = dfn'FCVT_S_WU (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_one" ``let r = dfn'FCVT_S_L (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_one" ``let r = dfn'FCVT_S_LU (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_one" ``let r = dfn'FCVT_D_W (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_one" ``let r = dfn'FCVT_D_WU (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_one" ``let r = dfn'FCVT_D_L (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_one" ``let r = dfn'FCVT_D_LU (3w,1w,0w) ^s_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_negative_one = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073709551615w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_negative_one" ``let r = dfn'FCVT_S_W (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_negative_one" ``let r = dfn'FCVT_S_WU (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_negative_one" ``let r = dfn'FCVT_S_L (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_negative_one" ``let r = dfn'FCVT_S_LU (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_negative_one" ``let r = dfn'FCVT_D_W (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_negative_one" ``let r = dfn'FCVT_D_WU (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_negative_one" ``let r = dfn'FCVT_D_L (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_negative_one" ``let r = dfn'FCVT_D_LU (3w,1w,0w) ^s_negative_one in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_tie_even = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 16777217w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_tie_even" ``let r = dfn'FCVT_S_W (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_tie_even" ``let r = dfn'FCVT_S_WU (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_tie_even" ``let r = dfn'FCVT_S_L (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_tie_even" ``let r = dfn'FCVT_S_LU (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_tie_even" ``let r = dfn'FCVT_D_W (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_tie_even" ``let r = dfn'FCVT_D_WU (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_tie_even" ``let r = dfn'FCVT_D_L (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_tie_even" ``let r = dfn'FCVT_D_LU (3w,1w,0w) ^s_tie_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_tie_zero = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 16777217w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_tie_zero" ``let r = dfn'FCVT_S_W (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_tie_zero" ``let r = dfn'FCVT_S_WU (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_tie_zero" ``let r = dfn'FCVT_S_L (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_tie_zero" ``let r = dfn'FCVT_S_LU (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_tie_zero" ``let r = dfn'FCVT_D_W (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_tie_zero" ``let r = dfn'FCVT_D_WU (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_tie_zero" ``let r = dfn'FCVT_D_L (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_tie_zero" ``let r = dfn'FCVT_D_LU (3w,1w,1w) ^s_tie_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_tie_down = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 16777217w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_tie_down" ``let r = dfn'FCVT_S_W (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_tie_down" ``let r = dfn'FCVT_S_WU (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_tie_down" ``let r = dfn'FCVT_S_L (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_tie_down" ``let r = dfn'FCVT_S_LU (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_tie_down" ``let r = dfn'FCVT_D_W (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_tie_down" ``let r = dfn'FCVT_D_WU (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_tie_down" ``let r = dfn'FCVT_D_L (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_tie_down" ``let r = dfn'FCVT_D_LU (3w,1w,2w) ^s_tie_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_tie_up = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 16777217w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_tie_up" ``let r = dfn'FCVT_S_W (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_tie_up" ``let r = dfn'FCVT_S_WU (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_tie_up" ``let r = dfn'FCVT_S_L (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_tie_up" ``let r = dfn'FCVT_S_LU (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_tie_up" ``let r = dfn'FCVT_D_W (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_tie_up" ``let r = dfn'FCVT_D_WU (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_tie_up" ``let r = dfn'FCVT_D_L (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_tie_up" ``let r = dfn'FCVT_D_LU (3w,1w,3w) ^s_tie_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_negative_tie = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073692774399w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_negative_tie" ``let r = dfn'FCVT_S_W (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_negative_tie" ``let r = dfn'FCVT_S_WU (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_negative_tie" ``let r = dfn'FCVT_S_L (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_negative_tie" ``let r = dfn'FCVT_S_LU (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_negative_tie" ``let r = dfn'FCVT_D_W (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_negative_tie" ``let r = dfn'FCVT_D_WU (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_negative_tie" ``let r = dfn'FCVT_D_L (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_negative_tie" ``let r = dfn'FCVT_D_LU (3w,1w,0w) ^s_negative_tie in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_negative_down = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073692774399w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_negative_down" ``let r = dfn'FCVT_S_W (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_negative_down" ``let r = dfn'FCVT_S_WU (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_negative_down" ``let r = dfn'FCVT_S_L (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_negative_down" ``let r = dfn'FCVT_S_LU (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_negative_down" ``let r = dfn'FCVT_D_W (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_negative_down" ``let r = dfn'FCVT_D_WU (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_negative_down" ``let r = dfn'FCVT_D_L (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_negative_down" ``let r = dfn'FCVT_D_LU (3w,1w,2w) ^s_negative_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_negative_up = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073692774399w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_negative_up" ``let r = dfn'FCVT_S_W (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_negative_up" ``let r = dfn'FCVT_S_WU (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_negative_up" ``let r = dfn'FCVT_S_L (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_negative_up" ``let r = dfn'FCVT_S_LU (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_negative_up" ``let r = dfn'FCVT_D_W (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_negative_up" ``let r = dfn'FCVT_D_WU (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_negative_up" ``let r = dfn'FCVT_D_L (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_negative_up" ``let r = dfn'FCVT_D_LU (3w,1w,3w) ^s_negative_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_large_even = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073709551615w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_large_even" ``let r = dfn'FCVT_S_W (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_large_even" ``let r = dfn'FCVT_S_WU (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_large_even" ``let r = dfn'FCVT_S_L (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_large_even" ``let r = dfn'FCVT_S_LU (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_large_even" ``let r = dfn'FCVT_D_W (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_large_even" ``let r = dfn'FCVT_D_WU (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_large_even" ``let r = dfn'FCVT_D_L (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_large_even" ``let r = dfn'FCVT_D_LU (3w,1w,0w) ^s_large_even in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_large_zero = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073709551615w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_large_zero" ``let r = dfn'FCVT_S_W (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_large_zero" ``let r = dfn'FCVT_S_WU (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_large_zero" ``let r = dfn'FCVT_S_L (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_large_zero" ``let r = dfn'FCVT_S_LU (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_large_zero" ``let r = dfn'FCVT_D_W (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_large_zero" ``let r = dfn'FCVT_D_WU (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_large_zero" ``let r = dfn'FCVT_D_L (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_large_zero" ``let r = dfn'FCVT_D_LU (3w,1w,1w) ^s_large_zero in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_large_down = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073709551615w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_large_down" ``let r = dfn'FCVT_S_W (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_large_down" ``let r = dfn'FCVT_S_WU (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_large_down" ``let r = dfn'FCVT_S_L (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_large_down" ``let r = dfn'FCVT_S_LU (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_large_down" ``let r = dfn'FCVT_D_W (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_large_down" ``let r = dfn'FCVT_D_WU (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_large_down" ``let r = dfn'FCVT_D_L (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_large_down" ``let r = dfn'FCVT_D_LU (3w,1w,2w) ^s_large_down in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_large_up = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 18446744073709551615w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_large_up" ``let r = dfn'FCVT_S_W (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_large_up" ``let r = dfn'FCVT_S_WU (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_large_up" ``let r = dfn'FCVT_S_L (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_large_up" ``let r = dfn'FCVT_S_LU (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_large_up" ``let r = dfn'FCVT_D_W (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_large_up" ``let r = dfn'FCVT_D_WU (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_large_up" ``let r = dfn'FCVT_D_L (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_large_up" ``let r = dfn'FCVT_D_LU (3w,1w,3w) ^s_large_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_zero_up = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 0w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_zero_up" ``let r = dfn'FCVT_S_W (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_zero_up" ``let r = dfn'FCVT_S_WU (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_zero_up" ``let r = dfn'FCVT_S_L (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_zero_up" ``let r = dfn'FCVT_S_LU (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_zero_up" ``let r = dfn'FCVT_D_W (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_zero_up" ``let r = dfn'FCVT_D_WU (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_zero_up" ``let r = dfn'FCVT_D_L (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_zero_up" ``let r = dfn'FCVT_D_LU (3w,1w,3w) ^s_zero_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_dynamic_up = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 16777217w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_dynamic_up" ``let r = dfn'FCVT_S_W (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_dynamic_up" ``let r = dfn'FCVT_S_WU (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_dynamic_up" ``let r = dfn'FCVT_S_L (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_dynamic_up" ``let r = dfn'FCVT_S_LU (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_dynamic_up" ``let r = dfn'FCVT_D_W (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_dynamic_up" ``let r = dfn'FCVT_D_WU (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_dynamic_up" ``let r = dfn'FCVT_D_L (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_dynamic_up" ``let r = dfn'FCVT_D_LU (3w,1w,7w) ^s_dynamic_up in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_illegal = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 1w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_illegal" ``let r = dfn'FCVT_S_W (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_illegal" ``let r = dfn'FCVT_S_WU (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_illegal" ``let r = dfn'FCVT_S_L (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_illegal" ``let r = dfn'FCVT_S_LU (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_illegal" ``let r = dfn'FCVT_D_W (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_illegal" ``let r = dfn'FCVT_D_WU (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_illegal" ``let r = dfn'FCVT_D_L (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_illegal" ``let r = dfn'FCVT_D_LU (3w,1w,4w) ^s_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val s_dynamic_illegal = ``(ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ r. if r = 1w then 1w else 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c _. if c = 7w then 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>``;
val _ = observe "fcvt_s_w_dynamic_illegal" ``let r = dfn'FCVT_S_W (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_wu_dynamic_illegal" ``let r = dfn'FCVT_S_WU (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_l_dynamic_illegal" ``let r = dfn'FCVT_S_L (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_s_lu_dynamic_illegal" ``let r = dfn'FCVT_S_LU (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_w_dynamic_illegal" ``let r = dfn'FCVT_D_W (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_wu_dynamic_illegal" ``let r = dfn'FCVT_D_WU (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_l_dynamic_illegal" ``let r = dfn'FCVT_D_L (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fcvt_d_lu_dynamic_illegal" ``let r = dfn'FCVT_D_LU (3w,1w,7w) ^s_dynamic_illegal in
 (FPRD 3w r, GPR 1w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = OS.Process.exit OS.Process.success;
