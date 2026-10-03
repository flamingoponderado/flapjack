import Flapjack.RiscV.L3.Step.Fetch
import Flapjack.RiscV.L3.Step.BitRewrites
import Mathlib.Tactic.IntervalCases

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-- Flapjack proof infrastructure: original bare-VM premise reduces the faithful
step Fetch definition; no distinct named original HOL theorem. -/
theorem fetch_bare (s : riscv_state)
    (h : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    Fetch s = rawReadInst (s.c_PC s.procID) s := by
  simp [Fetch, translateAddr, vmType, MCSR, PC, h, holThe]



/-- Original full compressed fetch theorem: all Boolean/list and native state
variables retain their source domains, premises and complete Skip update. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "Fetch16"]
theorem fetch16 (s : riscv_state) (xs : List Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF : Bool)
    (h : xs = [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,xA,xB,xC,xD,xE,xF] ∧
      (s.c_MCSR s.procID).mstatus.VM = 0#5 ∧
      s.MEM8 (s.c_PC s.procID + 1#64) = holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7] ∧
      s.MEM8 (s.c_PC s.procID) = holV2w 8 [x8,x9,xA,xB,xC,xD,xE,xF] ∧
      ¬(xE = true ∧ xF = true)) :
    Fetch s = (.Half (holV2w 16 xs),
      {s with c_Skip := holUpdate s.procID 2#64 s.c_Skip}) := by
  rcases h with ⟨hxs,hvm,hmem1,hmem0,hbits⟩
  subst xs
  have hc : holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7] ++ holV2w 8 [x8,x9,xA,xB,xC,xD,xE,xF] =
      holV2w 16 [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,xA,xB,xC,xD,xE,xF] := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_append, holV2w, Flapjack.getLsbD_holFcpWord]
    interval_cases i <;> simp
  rw [fetch_bare s hvm]
  simp only [rawReadInst, boolify8, hmem0]
  rw [(word_bit_1_0 x8 x9 xA xB xC xD xE xF).1,
      (word_bit_1_0 x8 x9 xA xB xC xD xE xF).2]
  simp [«write'Skip», hbits, hmem0, hmem1, hc]



/-- Original full word fetch theorem: all32 Boolean/list variables and full
state are unrestricted, with exactly the source VM/byte/low-bit premises. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "Fetch32"]
theorem fetch32 (s : riscv_state) (xs : List Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF : Bool)
    (h : xs = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,yA,yB,yC,yD,yE,yF,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,xA,xB,xC,xD,xE,xF] ∧
      (s.c_MCSR s.procID).mstatus.VM = 0#5 ∧
      s.MEM8 (s.c_PC s.procID + 3#64) = holV2w 8 [y0,y1,y2,y3,y4,y5,y6,y7] ∧
      s.MEM8 (s.c_PC s.procID + 2#64) = holV2w 8 [y8,y9,yA,yB,yC,yD,yE,yF] ∧
      s.MEM8 (s.c_PC s.procID + 1#64) = holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7] ∧
      s.MEM8 (s.c_PC s.procID) = holV2w 8 [x8,x9,xA,xB,xC,xD,xE,xF] ∧
      xE = true ∧ xF = true) :
    Fetch s = (.Word (holV2w 32 xs),
      {s with c_Skip := holUpdate s.procID 4#64 s.c_Skip}) := by
  rcases h with ⟨hxs,hvm,hmem3,hmem2,hmem1,hmem0,hE,hF⟩
  subst xs
  have hc : holV2w 8 [y0,y1,y2,y3,y4,y5,y6,y7] ++ (holV2w 8 [y8,y9,yA,yB,yC,yD,yE,yF] ++
      (holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7] ++ holV2w 8 [x8,x9,xA,xB,xC,xD,xE,xF])) =
      holV2w 32 [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,yA,yB,yC,yD,yE,yF,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,xA,xB,xC,xD,xE,xF] := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_append, holV2w, Flapjack.getLsbD_holFcpWord]
    interval_cases i <;> simp
  rw [fetch_bare s hvm]
  simp only [rawReadInst, boolify8, hmem0]
  rw [(word_bit_1_0 x8 x9 xA xB xC xD xE xF).1,
      (word_bit_1_0 x8 x9 xA xB xC xD xE xF).2]
  have hcontrol : (xE && xF) = true := by simp [hE, hF]
  simp [«write'Skip», hcontrol, hmem0, hmem1, hmem2, hmem3, hc]

end Flapjack.RiscV.L3.Step
