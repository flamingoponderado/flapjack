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

val () = computeLib.add_funs [machine_ieeeTheory.fp32_add_def, machine_ieeeTheory.fp32_sub_def,
 machine_ieeeTheory.fp32_mul_def, machine_ieeeTheory.fp32_negate_def,
 machine_ieeeTheory.fp64_add_def, machine_ieeeTheory.fp64_sub_def,
 machine_ieeeTheory.fp64_mul_def, machine_ieeeTheory.fp64_negate_def];
fun observe_choice_equation label tm = let
 val defs = map snd (List.filter (fn (name,_) =>
   not (String.isPrefix "write" name) andalso name <> "signalException_def")
   (DB.definitions "riscv"))
 val th = prove(tm,SIMP_TAC(srw_ss() ++ wordsLib.WORD_EXTRACT_ss) defs)
 in if null(hyp th) then (print(label ^ "=");print_thm th;print "\n")
 else raise Fail(label ^ " has assumptions") end;
val _ = observe "fmadd_s_basic_rte" ``let r = dfn'FMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_basic_rtz" ``let r = dfn'FMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_basic_down" ``let r = dfn'FMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_basic_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_basic_dynamic_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_basic_invalid_static" ``let r = dfn'FMADD_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_basic_invalid_dynamic" ``let r = dfn'FMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_rte" ``let r = dfn'FMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_rtz" ``let r = dfn'FMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_down" ``let r = dfn'FMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_dynamic_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_invalid_static" ``let r = dfn'FMADD_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_double_round_invalid_dynamic" ``let r = dfn'FMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_signed_zero_rte" ``let r = dfn'FMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_signed_zero_rtz" ``let r = dfn'FMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_signed_zero_down" ``let r = dfn'FMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_signed_zero_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_infinity_rte" ``let r = dfn'FMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_infinity_rtz" ``let r = dfn'FMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_infinity_down" ``let r = dfn'FMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_infinity_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_negative_finite_rte" ``let r = dfn'FMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_negative_finite_rtz" ``let r = dfn'FMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_negative_finite_down" ``let r = dfn'FMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_s_negative_finite_up" ``let r = dfn'FMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fmadd_s_invalid_product_rte" ``dfn'FMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_add roundTiesToEven (fp32_mul roundTiesToEven 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmadd_s_invalid_product_rtz" ``dfn'FMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_add roundTowardZero (fp32_mul roundTowardZero 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmadd_s_invalid_product_down" ``dfn'FMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_add roundTowardNegative (fp32_mul roundTowardNegative 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmadd_s_invalid_product_up" ``dfn'FMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_add roundTowardPositive (fp32_mul roundTowardPositive 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fmsub_s_basic_rte" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_basic_rtz" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_basic_down" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_basic_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_basic_dynamic_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_basic_invalid_static" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_basic_invalid_dynamic" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_rte" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_rtz" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_down" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_dynamic_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_invalid_static" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_double_round_invalid_dynamic" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_signed_zero_rte" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_signed_zero_rtz" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_signed_zero_down" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_signed_zero_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_infinity_rte" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_infinity_rtz" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_infinity_down" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_infinity_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_negative_finite_rte" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_negative_finite_rtz" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_negative_finite_down" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_s_negative_finite_up" ``let r = dfn'FMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fmsub_s_invalid_product_rte" ``dfn'FMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_sub roundTiesToEven (fp32_mul roundTiesToEven 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmsub_s_invalid_product_rtz" ``dfn'FMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_sub roundTowardZero (fp32_mul roundTowardZero 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmsub_s_invalid_product_down" ``dfn'FMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_sub roundTowardNegative (fp32_mul roundTowardNegative 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmsub_s_invalid_product_up" ``dfn'FMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_sub roundTowardPositive (fp32_mul roundTowardPositive 0x0w 0x7f800000w) 0x3f800000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fnmadd_s_basic_rte" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_basic_rtz" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_basic_down" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_basic_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_basic_dynamic_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_basic_invalid_static" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_basic_invalid_dynamic" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_rte" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_rtz" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_down" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_dynamic_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_invalid_static" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_double_round_invalid_dynamic" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0xbf800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_signed_zero_rte" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_signed_zero_rtz" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_signed_zero_down" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_signed_zero_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_infinity_rte" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_infinity_rtz" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_infinity_down" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_infinity_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_negative_finite_rte" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_negative_finite_rtz" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_negative_finite_down" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_s_negative_finite_up" ``let r = dfn'FNMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fnmadd_s_invalid_product_rte" ``dfn'FNMADD_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_add roundTiesToEven (fp32_mul roundTiesToEven 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmadd_s_invalid_product_rtz" ``dfn'FNMADD_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_add roundTowardZero (fp32_mul roundTowardZero 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmadd_s_invalid_product_down" ``dfn'FNMADD_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_add roundTowardNegative (fp32_mul roundTowardNegative 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmadd_s_invalid_product_up" ``dfn'FNMADD_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_add roundTowardPositive (fp32_mul roundTowardPositive 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fnmsub_s_basic_rte" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_basic_rtz" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_basic_down" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_basic_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_basic_dynamic_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_basic_invalid_static" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_basic_invalid_dynamic" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_rte" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_rtz" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_down" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_dynamic_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_invalid_static" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_double_round_invalid_dynamic" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3f800001w else if r = 2w then 0x3f7ffffew else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_signed_zero_rte" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_signed_zero_rtz" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_signed_zero_down" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_signed_zero_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x80000000w else if r = 2w then 0x40000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_infinity_rte" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_infinity_rtz" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_infinity_down" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_infinity_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7f800000w else if r = 2w then 0xbf800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_negative_finite_rte" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_negative_finite_rtz" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_negative_finite_down" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_s_negative_finite_up" ``let r = dfn'FNMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbf800000w else if r = 2w then 0x40000000w else if r = 3w then 0x40400000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fnmsub_s_invalid_product_rte" ``dfn'FNMSUB_S (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_sub roundTiesToEven (fp32_mul roundTiesToEven 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmsub_s_invalid_product_rtz" ``dfn'FNMSUB_S (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_sub roundTowardZero (fp32_mul roundTowardZero 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmsub_s_invalid_product_down" ``dfn'FNMSUB_S (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_sub roundTowardNegative (fp32_mul roundTowardNegative 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmsub_s_invalid_product_up" ``dfn'FNMSUB_S (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRS (4w,(fp32_negate (fp32_sub roundTowardPositive (fp32_mul roundTowardPositive 0x0w 0x7f800000w) 0x3f800000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7f800000w else if r = 3w then 0x3f800000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fmadd_d_basic_rte" ``let r = dfn'FMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_basic_rtz" ``let r = dfn'FMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_basic_down" ``let r = dfn'FMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_basic_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_basic_dynamic_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_basic_invalid_static" ``let r = dfn'FMADD_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_basic_invalid_dynamic" ``let r = dfn'FMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_rte" ``let r = dfn'FMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_rtz" ``let r = dfn'FMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_down" ``let r = dfn'FMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_dynamic_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_invalid_static" ``let r = dfn'FMADD_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_double_round_invalid_dynamic" ``let r = dfn'FMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_signed_zero_rte" ``let r = dfn'FMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_signed_zero_rtz" ``let r = dfn'FMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_signed_zero_down" ``let r = dfn'FMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_signed_zero_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_infinity_rte" ``let r = dfn'FMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_infinity_rtz" ``let r = dfn'FMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_infinity_down" ``let r = dfn'FMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_infinity_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_negative_finite_rte" ``let r = dfn'FMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_negative_finite_rtz" ``let r = dfn'FMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_negative_finite_down" ``let r = dfn'FMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmadd_d_negative_finite_up" ``let r = dfn'FMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fmadd_d_invalid_product_rte" ``dfn'FMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_add roundTiesToEven (fp64_mul roundTiesToEven 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmadd_d_invalid_product_rtz" ``dfn'FMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_add roundTowardZero (fp64_mul roundTowardZero 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmadd_d_invalid_product_down" ``dfn'FMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_add roundTowardNegative (fp64_mul roundTowardNegative 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmadd_d_invalid_product_up" ``dfn'FMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_add roundTowardPositive (fp64_mul roundTowardPositive 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fmsub_d_basic_rte" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_basic_rtz" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_basic_down" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_basic_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_basic_dynamic_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_basic_invalid_static" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_basic_invalid_dynamic" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_rte" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_rtz" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_down" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_dynamic_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_invalid_static" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_double_round_invalid_dynamic" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_signed_zero_rte" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_signed_zero_rtz" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_signed_zero_down" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_signed_zero_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_infinity_rte" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_infinity_rtz" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_infinity_down" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_infinity_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_negative_finite_rte" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_negative_finite_rtz" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_negative_finite_down" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fmsub_d_negative_finite_up" ``let r = dfn'FMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fmsub_d_invalid_product_rte" ``dfn'FMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_sub roundTiesToEven (fp64_mul roundTiesToEven 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmsub_d_invalid_product_rtz" ``dfn'FMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_sub roundTowardZero (fp64_mul roundTowardZero 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmsub_d_invalid_product_down" ``dfn'FMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_sub roundTowardNegative (fp64_mul roundTowardNegative 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fmsub_d_invalid_product_up" ``dfn'FMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_sub roundTowardPositive (fp64_mul roundTowardPositive 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w)) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fnmadd_d_basic_rte" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_basic_rtz" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_basic_down" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_basic_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_basic_dynamic_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_basic_invalid_static" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_basic_invalid_dynamic" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_rte" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_rtz" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_down" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_dynamic_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_invalid_static" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_double_round_invalid_dynamic" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0xbff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_signed_zero_rte" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_signed_zero_rtz" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_signed_zero_down" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_signed_zero_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_infinity_rte" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_infinity_rtz" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_infinity_down" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_infinity_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_negative_finite_rte" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_negative_finite_rtz" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_negative_finite_down" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmadd_d_negative_finite_up" ``let r = dfn'FNMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fnmadd_d_invalid_product_rte" ``dfn'FNMADD_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_add roundTiesToEven (fp64_mul roundTiesToEven 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmadd_d_invalid_product_rtz" ``dfn'FNMADD_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_add roundTowardZero (fp64_mul roundTowardZero 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmadd_d_invalid_product_down" ``dfn'FNMADD_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_add roundTowardNegative (fp64_mul roundTowardNegative 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmadd_d_invalid_product_up" ``dfn'FNMADD_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_add roundTowardPositive (fp64_mul roundTowardPositive 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe "fnmsub_d_basic_rte" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_basic_rtz" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_basic_down" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_basic_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_basic_dynamic_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_basic_invalid_static" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_basic_invalid_dynamic" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_rte" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_rtz" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_down" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_dynamic_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 3w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_invalid_static" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,4w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_double_round_invalid_dynamic" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,7w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x3ff0000000000001w else if r = 2w then 0x3feffffffffffffew else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 4w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_signed_zero_rte" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_signed_zero_rtz" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_signed_zero_down" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_signed_zero_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x8000000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x0w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_infinity_rte" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_infinity_rtz" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_infinity_down" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_infinity_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x7ff0000000000000w else if r = 2w then 0xbff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_negative_finite_rte" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_negative_finite_rtz" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_negative_finite_down" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe "fnmsub_d_negative_finite_up" ``let r = dfn'FNMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0xbff0000000000000w else if r = 2w then 0x4000000000000000w else if r = 3w then 0x4008000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) in
 (FPRD 4w r,FPRD 1w r,FPRD 2w r,FPRD 3w r,(MCSR r).mstatus.MFS,(MCSR r).mstatus.MSD,
 (Delta r).data1,(fcsr r).NV,(fcsr r).NX,r.c_fpr 8w 4w,
 case NextFetch r of SOME (Trap t) => t.trap = Illegal_Instr /\ t.badaddr = NONE | _ => F)``;
val _ = observe_choice_equation "fnmsub_d_invalid_product_rte" ``dfn'FNMSUB_D (4w,1w,2w,3w,0w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_sub roundTiesToEven (fp64_mul roundTiesToEven 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmsub_d_invalid_product_rtz" ``dfn'FNMSUB_D (4w,1w,2w,3w,1w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_sub roundTowardZero (fp64_mul roundTowardZero 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmsub_d_invalid_product_down" ``dfn'FNMSUB_D (4w,1w,2w,3w,2w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_sub roundTowardNegative (fp64_mul roundTowardNegative 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
val _ = observe_choice_equation "fnmsub_d_invalid_product_up" ``dfn'FNMSUB_D (4w,1w,2w,3w,3w) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>) = writeFPRD (4w,(fp64_negate (fp64_sub roundTowardPositive (fp64_mul roundTowardPositive 0x0w 0x7ff0000000000000w) 0x3ff0000000000000w))) ((ARB:riscv_state) with <| procID := 7w;
 c_gpr := (\_ _. 99w); c_NextFetch := (\_. NONE);
 c_fpr := (\c r. if c = 7w then if r = 1w then 0x0w else if r = 2w then 0x7ff0000000000000w else if r = 3w then 0x3ff0000000000000w else 0xcafe000000000000w else 0xbbbb000000000000w);
 c_update := (\_. (ARB:StateDelta) with data1 := SOME 42w);
 c_UCSR := (\_. (ARB:UserCSR) with fpcsr := (ARB:FPCSR) with <| NV := F; NX := T; FRM := 0w |>);
 c_MCSR := (\_. (ARB:MachineCSR) with mstatus := (ARB:mstatus) with <| MFS := 0w; MSD := F |>) |>)``;
