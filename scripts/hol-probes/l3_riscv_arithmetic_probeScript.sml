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
 then let
 val (m,z,x,t,w) = binary_ieeeSyntax.dest_float_round tm
 val up = m ~~ binary_ieeeSyntax.roundTowardPositive_tm
 val found = FlapjackDirected.discover_directed_candidate up x (t,w)
 (* Candidate discovery is untrusted. Rebuild its bits at the original HOL
    result carrier, including compound dimensions such as (:8 + 1), before
    the independent original kernel certificate checks the complete result. *)
 val (_,(_,en,sn)) = binary_ieeeSyntax.triple_of_float found
 val (pt,et) = binary_ieeeSyntax.dest_float_ty (type_of tm)
 val a = binary_ieeeSyntax.mk_floating_point
   (binary_ieeeSyntax.mk_float_sign found,
    wordsSyntax.mk_n2w (numSyntax.mk_numeral en,et),
    wordsSyntax.mk_n2w (numSyntax.mk_numeral sn,pt))
 val th = FlapjackDirected.directed_candidate_certificate up z x a
 in if aconv (lhs (concl th)) tm then th
 else (TextIO.output(TextIO.stdErr, "INPUT " ^ term_to_string tm ^ "\nCERT " ^ term_to_string (lhs(concl th)) ^ "\n");
       raise Fail "directed input mismatch") end
 else binary_ieeeLib.float_round_CONV tm end
 handle HOL_ERR err => raise Fail (Feedback.exn_to_string (HOL_ERR err));
val () = computeLib.upd_compset (computeLib.add_conv
  (binary_ieeeSyntax.float_round_tm, 3, checked_float_round));
val conv = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL;
fun observe label tm = let val th = conv tm in
 if null (hyp th) then (print(label ^ "="); print_term(rhs(concl th)); print "\n")
 else raise Fail (label ^ " has undischarged assumptions") end;
val () = computeLib.add_funs [machine_ieeeTheory.convert_def,
 machine_ieeeTheory.fp32_to_fp64_def, machine_ieeeTheory.fp64_to_fp32_def,
 machine_ieeeTheory.fp32_to_fp64_with_flags_def, machine_ieeeTheory.fp64_to_fp32_with_flags_def,
 machine_ieeeTheory.real_to_fp32_with_flags_def, machine_ieeeTheory.real_to_fp64_with_flags_def];
val () = computeLib.add_funs [machine_ieeeTheory.fp32_add_def, machine_ieeeTheory.fp32_sub_def, machine_ieeeTheory.fp32_mul_def, machine_ieeeTheory.fp32_div_def, machine_ieeeTheory.fp64_add_def, machine_ieeeTheory.fp64_sub_def, machine_ieeeTheory.fp64_mul_def, machine_ieeeTheory.fp64_div_def];

(* Check unspecified NaN payloads as complete original state equations. *)
fun observe_nan_equation label tm = let
 val support = map snd (List.filter (fn (name,_) =>
   not (String.isPrefix "write" name) andalso name <> "signalException_def")
   (DB.definitions "riscv"))
 val defs = support @ [riscvTheory.dfn'FDIV_S_def, riscvTheory.dfn'FDIV_D_def,
  riscvTheory.round_def, riscvTheory.FPRS_def, riscvTheory.FPRD_def,
  machine_ieeeTheory.fp32_div_def, machine_ieeeTheory.fp64_div_def,
  machine_ieeeTheory.fp32_to_float_def, machine_ieeeTheory.fp64_to_float_def,
  binary_ieeeTheory.float_div_def, binary_ieeeTheory.float_value_def,
  binary_ieeeTheory.float_to_real_def]
 val th = prove(tm, SIMP_TAC (srw_ss() ++ wordsLib.WORD_EXTRACT_ss) defs)
 in if null(hyp th) then
  (print(label ^ "="); print_thm th; print "\n")
 else raise Fail(label ^ " has assumptions") end;
val _ = observe "fadd_s_one_two_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_one_two_rtz" ``let r = dfn'FADD_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_one_two_down" ``let r = dfn'FADD_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_one_two_up" ``let r = dfn'FADD_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_one_two_dynamic_up" ``let r = dfn'FADD_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_one_two_invalid_static" ``let r = dfn'FADD_S (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_one_two_invalid_dynamic" ``let r = dfn'FADD_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_negative_one_two_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_zero_negative_one_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_negative_zero_zero_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_negative_zero_zero_rtz" ``let r = dfn'FADD_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_negative_zero_zero_down" ``let r = dfn'FADD_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_negative_zero_zero_up" ``let r = dfn'FADD_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_cancel_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_cancel_rtz" ``let r = dfn'FADD_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_cancel_down" ``let r = dfn'FADD_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_cancel_up" ``let r = dfn'FADD_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_tie_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x33800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_tie_rtz" ``let r = dfn'FADD_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x33800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_tie_down" ``let r = dfn'FADD_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x33800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_tie_up" ``let r = dfn'FADD_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x33800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_s_pinf_one_rte" ``let r = dfn'FADD_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_rte" ``let r = dfn'FSUB_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_rtz" ``let r = dfn'FSUB_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_down" ``let r = dfn'FSUB_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_up" ``let r = dfn'FSUB_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_dynamic_up" ``let r = dfn'FSUB_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_invalid_static" ``let r = dfn'FSUB_S (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_two_invalid_dynamic" ``let r = dfn'FSUB_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_negative_one_two_rte" ``let r = dfn'FSUB_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_zero_negative_one_rte" ``let r = dfn'FSUB_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_negative_zero_zero_rte" ``let r = dfn'FSUB_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_negative_zero_zero_rtz" ``let r = dfn'FSUB_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_negative_zero_zero_down" ``let r = dfn'FSUB_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_negative_zero_zero_up" ``let r = dfn'FSUB_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_cancel_rte" ``let r = dfn'FSUB_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_cancel_rtz" ``let r = dfn'FSUB_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_cancel_down" ``let r = dfn'FSUB_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_cancel_up" ``let r = dfn'FSUB_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_s_one_pinf_rte" ``let r = dfn'FSUB_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x7f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_rte" ``let r = dfn'FMUL_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_rtz" ``let r = dfn'FMUL_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_down" ``let r = dfn'FMUL_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_up" ``let r = dfn'FMUL_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_dynamic_up" ``let r = dfn'FMUL_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_invalid_static" ``let r = dfn'FMUL_S (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_one_two_invalid_dynamic" ``let r = dfn'FMUL_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_negative_one_two_rte" ``let r = dfn'FMUL_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_zero_negative_one_rte" ``let r = dfn'FMUL_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_negative_zero_zero_rte" ``let r = dfn'FMUL_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_negative_zero_zero_rtz" ``let r = dfn'FMUL_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_negative_zero_zero_down" ``let r = dfn'FMUL_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_negative_zero_zero_up" ``let r = dfn'FMUL_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_s_pinf_negative_one_rte" ``let r = dfn'FMUL_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_rte" ``let r = dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_rtz" ``let r = dfn'FDIV_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_down" ``let r = dfn'FDIV_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_up" ``let r = dfn'FDIV_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_dynamic_up" ``let r = dfn'FDIV_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_invalid_static" ``let r = dfn'FDIV_S (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_two_invalid_dynamic" ``let r = dfn'FDIV_S (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_negative_one_two_rte" ``let r = dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_zero_negative_one_rte" ``let r = dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_nan_equation "fdiv_s_negative_zero_zero_rte" ``dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRS (3w, float_to_fp32 (float_some_qnan (FP_Div roundTiesToEven
 (fp32_to_float (0x80000000w : word32)) (fp32_to_float (0w : word32))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_nan_equation "fdiv_s_negative_zero_zero_rtz" ``dfn'FDIV_S (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRS (3w, float_to_fp32 (float_some_qnan (FP_Div roundTowardZero
 (fp32_to_float (0x80000000w : word32)) (fp32_to_float (0w : word32))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_nan_equation "fdiv_s_negative_zero_zero_down" ``dfn'FDIV_S (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRS (3w, float_to_fp32 (float_some_qnan (FP_Div roundTowardNegative
 (fp32_to_float (0x80000000w : word32)) (fp32_to_float (0w : word32))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_nan_equation "fdiv_s_negative_zero_zero_up" ``dfn'FDIV_S (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRS (3w, float_to_fp32 (float_some_qnan (FP_Div roundTowardPositive
 (fp32_to_float (0x80000000w : word32)) (fp32_to_float (0w : word32))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fdiv_s_one_zero_rte" ``let r = dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_one_pinf_rte" ``let r = dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x7f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_s_pinf_negative_one_rte" ``let r = dfn'FDIV_S (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_rtz" ``let r = dfn'FADD_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_down" ``let r = dfn'FADD_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_up" ``let r = dfn'FADD_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_dynamic_up" ``let r = dfn'FADD_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_invalid_static" ``let r = dfn'FADD_D (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_one_two_invalid_dynamic" ``let r = dfn'FADD_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_negative_one_two_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_zero_negative_one_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_negative_zero_zero_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_negative_zero_zero_rtz" ``let r = dfn'FADD_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_negative_zero_zero_down" ``let r = dfn'FADD_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_negative_zero_zero_up" ``let r = dfn'FADD_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_cancel_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_cancel_rtz" ``let r = dfn'FADD_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_cancel_down" ``let r = dfn'FADD_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_cancel_up" ``let r = dfn'FADD_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_tie_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ca0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_tie_rtz" ``let r = dfn'FADD_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ca0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_tie_down" ``let r = dfn'FADD_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ca0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_tie_up" ``let r = dfn'FADD_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ca0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fadd_d_pinf_one_rte" ``let r = dfn'FADD_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_rte" ``let r = dfn'FSUB_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_rtz" ``let r = dfn'FSUB_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_down" ``let r = dfn'FSUB_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_up" ``let r = dfn'FSUB_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_dynamic_up" ``let r = dfn'FSUB_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_invalid_static" ``let r = dfn'FSUB_D (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_two_invalid_dynamic" ``let r = dfn'FSUB_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_negative_one_two_rte" ``let r = dfn'FSUB_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_zero_negative_one_rte" ``let r = dfn'FSUB_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_negative_zero_zero_rte" ``let r = dfn'FSUB_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_negative_zero_zero_rtz" ``let r = dfn'FSUB_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_negative_zero_zero_down" ``let r = dfn'FSUB_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_negative_zero_zero_up" ``let r = dfn'FSUB_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_cancel_rte" ``let r = dfn'FSUB_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_cancel_rtz" ``let r = dfn'FSUB_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_cancel_down" ``let r = dfn'FSUB_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_cancel_up" ``let r = dfn'FSUB_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fsub_d_one_pinf_rte" ``let r = dfn'FSUB_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x7ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_rte" ``let r = dfn'FMUL_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_rtz" ``let r = dfn'FMUL_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_down" ``let r = dfn'FMUL_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_up" ``let r = dfn'FMUL_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_dynamic_up" ``let r = dfn'FMUL_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_invalid_static" ``let r = dfn'FMUL_D (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_one_two_invalid_dynamic" ``let r = dfn'FMUL_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_negative_one_two_rte" ``let r = dfn'FMUL_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_zero_negative_one_rte" ``let r = dfn'FMUL_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_negative_zero_zero_rte" ``let r = dfn'FMUL_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_negative_zero_zero_rtz" ``let r = dfn'FMUL_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_negative_zero_zero_down" ``let r = dfn'FMUL_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_negative_zero_zero_up" ``let r = dfn'FMUL_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmul_d_pinf_negative_one_rte" ``let r = dfn'FMUL_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_rte" ``let r = dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_rtz" ``let r = dfn'FDIV_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_down" ``let r = dfn'FDIV_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_up" ``let r = dfn'FDIV_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_dynamic_up" ``let r = dfn'FDIV_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_invalid_static" ``let r = dfn'FDIV_D (3w,1w,2w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_two_invalid_dynamic" ``let r = dfn'FDIV_D (3w,1w,2w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_negative_one_two_rte" ``let r = dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_zero_negative_one_rte" ``let r = dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_nan_equation "fdiv_d_negative_zero_zero_rte" ``dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRD (3w, float_to_fp64 (float_some_qnan (FP_Div roundTiesToEven
 (fp64_to_float (0x8000000000000000w : word64)) (fp64_to_float (0w : word64))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_nan_equation "fdiv_d_negative_zero_zero_rtz" ``dfn'FDIV_D (3w,1w,2w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRD (3w, float_to_fp64 (float_some_qnan (FP_Div roundTowardZero
 (fp64_to_float (0x8000000000000000w : word64)) (fp64_to_float (0w : word64))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_nan_equation "fdiv_d_negative_zero_zero_down" ``dfn'FDIV_D (3w,1w,2w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRD (3w, float_to_fp64 (float_some_qnan (FP_Div roundTowardNegative
 (fp64_to_float (0x8000000000000000w : word64)) (fp64_to_float (0w : word64))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_nan_equation "fdiv_d_negative_zero_zero_up" ``dfn'FDIV_D (3w,1w,2w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) =
 writeFPRD (3w, float_to_fp64 (float_some_qnan (FP_Div roundTowardPositive
 (fp64_to_float (0x8000000000000000w : word64)) (fp64_to_float (0w : word64))))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fdiv_d_one_zero_rte" ``let r = dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_one_pinf_rte" ``let r = dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x7ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fdiv_d_pinf_negative_one_rte" ``let r = dfn'FDIV_D (3w,1w,2w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 3w r, FPRD 1w r, FPRD 2w r, (MCSR r).mstatus.MFS, (MCSR r).mstatus.MSD,
  (Delta r).data1, (fcsr r).NV, (fcsr r).NX, r.c_fpr 8w 3w,
  case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
