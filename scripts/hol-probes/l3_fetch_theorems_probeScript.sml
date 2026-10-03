val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
fun check source q =
  let val th = prove(q, METIS_TAC [source])
  in if null(hyp source) andalso null(hyp th) andalso aconv (concl th) q then th
     else raise Fail "original full Fetch theorem shape or hypotheses changed"
  end;
fun binders label th =
  let val (vars,_) = strip_forall (concl th)
  in print(label ^ "=");
     List.app (fn v => (print(fst(dest_var v) ^ ":"); print_type(type_of v); print ";")) vars;
     print "\n"
  end;
fun statement label th = (print(label ^ "="); print_term(concl th); print "\n");
val Fetch16 = check riscv_stepTheory.Fetch16
  ``!s. !xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF.
       (xs = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF]) /\
       ((s.c_MCSR s.procID).mstatus.VM = 0w) ∧
       (s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ∧
       (s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF]) ∧
       ~(xE ∧ xF) ⇒
       (Fetch s =
        (Half (v2w xs), s with c_Skip := (s.procID =+ 2w) s.c_Skip))``;
val _ = binders "Fetch16_binders" Fetch16;
val _ = statement "Fetch16_statement" Fetch16;
val _ = print "Fetch16_hypotheses=0\n";
val _ = print "Fetch16_proof=T\n";
val Fetch32 = check riscv_stepTheory.Fetch32
  ``!s. !xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF
        y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF.
       (xs = [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9; yA; yB; yC; yD; yE; yF;
              x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF]) /\
       ((s.c_MCSR s.procID).mstatus.VM = 0w) ∧
       (s.MEM8 (s.c_PC s.procID + 3w) = v2w [y0; y1; y2; y3; y4; y5; y6; y7]) ∧
       (s.MEM8 (s.c_PC s.procID + 2w) = v2w [y8; y9; yA; yB; yC; yD; yE; yF]) ∧
       (s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ∧
       (s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF]) ∧
       xE ∧ xF ⇒
       (Fetch s =
        (Word (v2w xs), s with c_Skip := (s.procID =+ 4w) s.c_Skip))``;
val _ = binders "Fetch32_binders" Fetch32;
val _ = statement "Fetch32_statement" Fetch32;
val _ = print "Fetch32_hypotheses=0\n";
val _ = print "Fetch32_proof=T\n";
val _ = (print "v2w8_type="; print_type(type_of ``v2w : bool list -> word8``); print "\n");
val _ = (print "v2w16_type="; print_type(type_of ``v2w : bool list -> word16``); print "\n");
val _ = (print "v2w32_type="; print_type(type_of ``v2w : bool list -> word32``); print "\n");
